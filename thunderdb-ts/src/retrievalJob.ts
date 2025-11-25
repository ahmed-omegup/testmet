import { DocId, QueryId, DocStateDom, BatchNumber, RetrievalEvent, RetrievalBatchDoc } from './limit-index/types';

interface BatchEntry {
  queries: Set<QueryId>;
}

interface SourceLookup<DocState extends DocStateDom> {
  map: Map<DocId, BatchEntry>;
  entry: BatchEntry;
  batchNumber: BatchNumber;
}

export class RetrievalJobWorker<DocState extends DocStateDom> {
  private pendingBatch = new Map<DocId, BatchEntry>();
  private processingBatch = new Map<DocId, BatchEntry>();
  private pendingBatchNumber: BatchNumber = 1n;
  private processingBatchNumber: BatchNumber | null = null;
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

  register(docId: DocId, queryId: QueryId): BatchNumber {
    const entry = this.pendingBatch.get(docId) ?? { queries: new Set<QueryId>() };
    entry.queries.add(queryId);
    this.pendingBatch.set(docId, entry);
    this.signalPending();
    return this.pendingBatchNumber;
  }

  cancel(docId: DocId, queryId: QueryId, batchNumber: BatchNumber): boolean {
    if (batchNumber !== this.pendingBatchNumber) return false;
    const entry = this.pendingBatch.get(docId);
    if (!entry) return false;
    const removed = entry.queries.delete(queryId);
    if (entry.queries.size === 0) {
      this.pendingBatch.delete(docId);
    }
    return removed;
  }

  async resolveDoc(docId: DocId, batchHint?: BatchNumber): Promise<boolean> {
    const source = this.pickSource(docId, batchHint);
    if (!source) return false;
    source.map.delete(docId);
    this.cleanupProcessingIfEmpty();
    return true;
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
      const currentBatchNumber = this.pendingBatchNumber;
      this.processingBatch = nextProcessing;
      this.processingBatchNumber = currentBatchNumber;
      this.pendingBatch = new Map();
      this.pendingBatchNumber = currentBatchNumber + 1n;
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
          this.emit({ kind: 'retrieval', batchNumber: currentBatchNumber, docs: payload });
        }
      } catch (err) {
        console.error('retrieval-job: failed to load docs', err);
      }
      this.processingBatch.clear();
      this.processingBatchNumber = null;
      const delayMs = this.options.batchIntervalMs ?? 0;
      if (delayMs > 0) await this.delay(delayMs);
    }
  }

  private pickSource(docId: DocId, batchHint?: BatchNumber): SourceLookup<DocState> | null {
    if (batchHint && batchHint === this.processingBatchNumber && this.processingBatchNumber !== null) {
      const entry = this.processingBatch.get(docId);
      if (entry) return { map: this.processingBatch, entry, batchNumber: this.processingBatchNumber };
    }
    if (batchHint && batchHint === this.pendingBatchNumber) {
      const entry = this.pendingBatch.get(docId);
      if (entry) return { map: this.pendingBatch, entry, batchNumber: this.pendingBatchNumber };
    }
    if (this.processingBatchNumber !== null) {
      const entry = this.processingBatch.get(docId);
      if (entry) return { map: this.processingBatch, entry, batchNumber: this.processingBatchNumber };
    }
    const entry = this.pendingBatch.get(docId);
    if (entry) {
      return { map: this.pendingBatch, entry, batchNumber: this.pendingBatchNumber };
    }
    return null;
  }

  private cleanupProcessingIfEmpty(): void {
    if (this.processingBatchNumber !== null && this.processingBatch.size === 0) {
      this.processingBatchNumber = null;
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
