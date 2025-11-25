import { DocId } from './limit-index/types';

export type BatchNumber = bigint;

export interface BatchSnapshot {
  batchNumber: BatchNumber;
  entries: Array<[DocId, number]>;
}

export interface RetrievalReceipt {
  batchNumber: BatchNumber;
  count: number;
}

export class RetrievalJobWorker {
  private pendingBatch = new Map<DocId, number>();
  private activeBatch = new Map<DocId, number>();
  private pendingBatchNumber: BatchNumber = 1n;
  private activeBatchNumber: BatchNumber | null = null;

  getCurrentBatchNumber(): BatchNumber {
    return this.pendingBatchNumber;
  }

  getActiveBatchNumber(): BatchNumber | null {
    return this.activeBatchNumber;
  }

  register(docId: DocId): BatchNumber {
    const next = (this.pendingBatch.get(docId) ?? 0) + 1;
    this.pendingBatch.set(docId, next);
    return this.pendingBatchNumber;
  }

  cancel(docId: DocId, batchNumber: BatchNumber): boolean {
    if (batchNumber !== this.pendingBatchNumber) {
      return false;
    }
    const count = this.pendingBatch.get(docId);
    if (count === undefined) {
      return false;
    }
    if (count <= 1) {
      this.pendingBatch.delete(docId);
    } else {
      this.pendingBatch.set(docId, count - 1);
    }
    return true;
  }

  startNextBatch(): BatchSnapshot | null {
    if (this.pendingBatch.size === 0) {
      return null;
    }
    if (this.activeBatch.size > 0) {
      throw new Error('active batch still processing');
    }
    this.activeBatch = this.pendingBatch;
    this.activeBatchNumber = this.pendingBatchNumber;
    const snapshot = Array.from(this.activeBatch.entries());
    this.pendingBatch = new Map();
    this.pendingBatchNumber += 1n;
    return { batchNumber: this.activeBatchNumber, entries: snapshot };
  }

  documentReceived(docId: DocId): RetrievalReceipt | null {
    if (this.activeBatchNumber !== null) {
      const activeCount = this.activeBatch.get(docId);
      if (activeCount !== undefined) {
        this.activeBatch.delete(docId);
        const batchNumber = this.activeBatchNumber;
        if (this.activeBatch.size === 0) {
          this.activeBatchNumber = null;
          this.activeBatch = new Map();
        }
        return { batchNumber, count: activeCount };
      }
    }

    const pendingCount = this.pendingBatch.get(docId);
    if (pendingCount !== undefined) {
      this.pendingBatch.delete(docId);
      return { batchNumber: this.pendingBatchNumber, count: pendingCount };
    }

    return null;
  }

  pendingSize(): number {
    return this.pendingBatch.size;
  }

  activeSize(): number {
    return this.activeBatch.size;
  }

  pendingCount(docId: DocId): number {
    return this.pendingBatch.get(docId) ?? 0;
  }

  activeCount(docId: DocId): number {
    return this.activeBatch.get(docId) ?? 0;
  }
}
