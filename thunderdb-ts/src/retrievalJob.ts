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
  private loadFailure: Error | null = null;
  private terminalFailure: Error | null = null;

  constructor(
    private readonly loadDocs: (docIds: DocId[]) => Promise<Map<DocId, DocState>>,
    private readonly emit: (event: RetrievalEvent<DocState>) => void,
    private readonly options: { batchIntervalMs?: number } = {}
  ) {
    this.loop = this.startLoop();
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
    if (this.stopped) throw new Error('Cannot register after retrieval worker has stopped');
    if (this.terminalFailure) throw this.terminalFailure;
    const entry = this.pendingBatch.get(docId) ?? { queries: new Set<QueryId>() };
    entry.queries.add(queryId);
    this.pendingBatch.set(docId, entry);
    this.signalPending();
    return this.pendingBatchNumber;
  }

  retryFailed(): boolean {
    if (!this.loadFailure || !this.terminalFailure) return false;
    this.loadFailure = null;
    this.terminalFailure = null;
    this.loop = this.startLoop();
    return true;
  }

  getFailure(): Error | null {
    return this.terminalFailure;
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

  resolveDoc(docId: DocId, batchHint?: BatchNumber): boolean {
    const source = this.pickSource(docId, batchHint);
    if (!source) return false;
    source.map.delete(docId);
    this.cleanupProcessingIfEmpty();
    return true;
  }

  private async runLoop(): Promise<void> {
    while (true) {
      if (this.processingBatch.size === 0) {
        this.processingBatchNumber = null;
        if (this.stopped && this.pendingBatch.size === 0) break;
        if (this.pendingBatch.size === 0) {
          await this.waitForPending();
          if (this.stopped && this.pendingBatch.size === 0) break;
          continue;
        }
        this.processingBatch = this.pendingBatch;
        this.processingBatchNumber = this.pendingBatchNumber;
        this.pendingBatch = new Map();
        this.pendingBatchNumber += 1n;
      }
      const currentBatchNumber = this.processingBatchNumber!;
      let retries = 0;
      let docIds: DocId[];
      let docs: Map<DocId, DocState>;
      while (true) {
        docIds = Array.from(this.processingBatch.keys());
        if (!docIds.length) {
          docs = new Map();
          break;
        }
        try {
          docs = await this.loadDocs(docIds);
          break;
        } catch (error) {
          if (this.processingBatch.size === 0) continue;
          if (retries >= 3) {
            this.loadFailure = error instanceof Error ? error : new Error('Retrieval document load failed', { cause: error });
            throw this.loadFailure;
          }
          retries += 1;
          await this.delay(25);
        }
      }
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
      this.processingBatch.clear();
      this.processingBatchNumber = null;
      const delayMs = this.options.batchIntervalMs ?? 0;
      if (delayMs > 0) await this.delay(delayMs);
    }
  }

  private startLoop(): Promise<void> {
    const loop = this.runLoop();
    void loop.catch(error => {
      this.terminalFailure = error instanceof Error ? error : new Error('Retrieval worker failed', { cause: error });
      console.error('retrieval-job: worker stopped', this.terminalFailure);
    });
    return loop;
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
