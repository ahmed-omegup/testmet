import { DocId, QueryId, DocStateDom, RetrievalEvent, RetrievalBatchDoc } from './limit-index/types';

interface BatchEntry {
  queries: Set<QueryId>;
}

export class RetrievalJobWorker<DocState extends DocStateDom> {
  private pendingBatch = new Map<DocId, BatchEntry>();
  private processingBatch = new Map<DocId, BatchEntry>();
  private pendingWaiter: Promise<void> | null = null;
  private resolvePending: (() => void) | null = null;
  private loop: Promise<void>;
  private stopped = false;

  constructor(
    private readonly loadDocs: (docIds: DocId[]) => Promise<Map<DocId, DocState>>,
    private readonly emit: (event: RetrievalEvent<DocState>) => void,
    private readonly options: { batchIntervalMs?: number } = {}
  ) {
    this.loop = this.runLoop();
    // Silence unused variable lint
    void this.loop;
  }

  async stop(): Promise<void> {
    if (this.stopped) {
      await this.loop;
      return;
    }
    this.stopped = true;
    this.signalPending();
    await this.loop;
  }

  register(docId: DocId, queryId: QueryId) {
    console.log('RetrievalJobWorker: register', { docId, queryId });
    if(this.processingBatch.get(docId)?.queries.has(queryId)) {
      console.log(JSON.stringify(Object.fromEntries([...(global as any)['docs'].queries.get(queryId)[1]]), undefined, 2));
      throw new Error('Cannot register a doc that is currently being processed');
    }
    const entry = this.pendingBatch.get(docId) ?? { queries: new Set<QueryId>() };
    entry.queries.add(queryId);
    this.pendingBatch.set(docId, entry);
    this.signalPending();
  }

  cancel(docId: DocId, queryId: QueryId): boolean {
    const reg = this.pendingBatch.get(docId) ? this.pendingBatch : this.processingBatch;
    const entry = reg.get(docId);
    if (!entry) return false;
    const removed = entry.queries.delete(queryId);
    if (entry.queries.size === 0) {
      reg.delete(docId);
    }
    return removed;
  }

  resolveDoc(docId: DocId): boolean {
    const removedFromPending = this.pendingBatch.delete(docId);
    const removedFromProcessing = this.processingBatch.delete(docId);
    return removedFromProcessing || removedFromPending;
  }

  private async runLoop(): Promise<void> {
    while (true) {
      if (this.stopped && this.pendingBatch.size === 0) {
        break;
      }
      if (this.pendingBatch.size === 0) {
        await this.waitForPending();
        if (this.stopped && this.pendingBatch.size === 0) break;
        continue;
      }
      const nextProcessing = this.pendingBatch;
      this.processingBatch = nextProcessing;
      this.pendingBatch = new Map();
      const docIds = Array.from(this.processingBatch.keys());
      try {
        const docs = await this.loadDocs(docIds);
        const payload: RetrievalBatchDoc<DocState>[] = [];
        for (const docId of docIds) {
          const entry = this.processingBatch.get(docId);
          if (!entry) continue;
          const state = docs.get(docId);
          if (!state) continue;
          payload.push({ docId, state, queries: Array.from(entry.queries) });
        }
        if (payload.length) {
          this.emit({ kind: 'retrieval', docs: payload });
        }
      } catch (err) {
        console.error('retrieval-job: failed to load docs', err);
      }
      this.processingBatch.clear();
      const delayMs = this.options.batchIntervalMs ?? 0;
      if (delayMs > 0) await this.delay(delayMs);
    }
  }


  private signalPending(): void {
    if (this.resolvePending) {
      this.resolvePending();
      this.resolvePending = null;
      this.pendingWaiter = null;
    }
  }

  private async waitForPending(): Promise<void> {
    if (this.pendingBatch.size > 0 || this.stopped) return;
    if (!this.pendingWaiter) {
      this.pendingWaiter = new Promise(resolve => {
        this.resolvePending = resolve;
      });
    }
    await this.pendingWaiter;
  }

  private async delay(ms: number): Promise<void> {
    await new Promise(resolve => setTimeout(resolve, ms));
  }
}
