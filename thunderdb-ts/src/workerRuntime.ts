import { performance } from 'node:perf_hooks';
import { runLimitStreamAsync, StreamItem } from './limit-index/limitStream';
import { DownstreamEvent } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore, LmdbDurability } from './docStore';
import { SocketDocState, WorkerRunConfig, WorkerRunSummary } from './socketProtocol';

interface RunState {
  queue: AsyncStreamQueue;
  docStore?: LmdbDocStore<SocketDocState>;
  retrievalJob?: RetrievalJobWorker<SocketDocState>;
  matchEvents: number;
  evictions: number;
  retrievalBatches: number;
  retrievalDocs: number;
  eventsProcessed: number;
  startTime: number;
}

class AsyncStreamQueue {
  private buffer: StreamItem<SocketDocState>[] = [];
  private waiting: Array<() => void> = [];
  private closed = false;

  push(item: StreamItem<SocketDocState>): void {
    if (this.closed) throw new Error('queue already closed');
    this.buffer.push(item);
    this.flush();
  }

  close(): void {
    if (this.closed) return;
    this.closed = true;
    this.flush();
  }

  async *consume(): AsyncIterableIterator<StreamItem<SocketDocState>> {
    while (true) {
      if (this.buffer.length) {
        yield this.buffer.shift()!;
        continue;
      }
      if (this.closed) break;
      await new Promise<void>(resolve => this.waiting.push(resolve));
    }
  }

  private flush(): void {
    const waiter = this.waiting.shift();
    if (waiter) waiter();
  }
}

const getScore = (state: SocketDocState) => state.scoreValue;

const handleDownstreamEvent = (state: RunState, event: DownstreamEvent<SocketDocState>): void => {
  if (event.kind === 'match') {
    state.matchEvents += 1;
    state.evictions += event.evictions.length;
    return;
  }
  state.retrievalBatches += 1;
  state.retrievalDocs += event.docs.length;
};

const buildSummary = (state: RunState, durationMs: number): WorkerRunSummary => ({
  durationMs,
  eventsProcessed: state.eventsProcessed,
  matchEvents: state.matchEvents,
  evictions: state.evictions,
  retrievalBatches: state.retrievalBatches,
  retrievalDocs: state.retrievalDocs,
});

export interface WorkerRuntimeOptions {
  docStoreDurability?: LmdbDurability;
  progressStep?: number;
  log?: (message: string) => void;
}

const formatNumber = (value: number) => value.toLocaleString('en-US');

export class WorkerRuntime {
  private runState: RunState | null = null;
  private runPromise: Promise<WorkerRunSummary> | null = null;
  private readonly docStoreDurability: LmdbDurability;
  private readonly progressStep: number;
  private readonly log: (message: string) => void;

  constructor(options: WorkerRuntimeOptions = {}) {
    this.docStoreDurability = options.docStoreDurability ?? 'durable';
    this.progressStep = Math.max(1, options.progressStep ?? 10000);
    this.log = options.log ?? (() => {});
  }

  startRun(config: WorkerRunConfig): void {
    if (this.runPromise) throw new Error('run already in progress');
    const queue = new AsyncStreamQueue();
    const runState: RunState = {
      queue,
      matchEvents: 0,
      evictions: 0,
      retrievalBatches: 0,
      retrievalDocs: 0,
      eventsProcessed: 0,
      startTime: performance.now(),
    };
    if (config.enableRetrieval) {
      runState.docStore = new LmdbDocStore<SocketDocState>({ durability: this.docStoreDurability });
      runState.retrievalJob = new RetrievalJobWorker<SocketDocState>(
        ids => runState.docStore!.getMany(ids),
        event => {
          runState.retrievalBatches += 1;
          runState.retrievalDocs += event.docs.length;
        }
      );
    }
    this.runState = runState;
    this.runPromise = (async () => {
      try {
        await runLimitStreamAsync(queue.consume(), getScore, evt => handleDownstreamEvent(runState, evt), {
          retrievalJob: runState.retrievalJob,
          docStore: runState.docStore,
        });
        this.log('[worker] run completed');
        if (runState.retrievalJob) {
          await runState.retrievalJob.stop();
          this.log('[worker] retrieval job stopped');
        }
        const durationMs = performance.now() - runState.startTime;
        return buildSummary(runState, durationMs);
      } finally {
        queue.close();
      }
    })();
  }

  enqueue(item: StreamItem<SocketDocState>): void {
    const state = this.requireState();
    state.queue.push(item);
    state.eventsProcessed += 1;
    this.maybeLogProgress(state);
  }

  enqueueBatch(items: Iterable<StreamItem<SocketDocState>>): void {
    const state = this.requireState();
    for (const item of items) {
      state.queue.push(item);
      state.eventsProcessed += 1;
      this.maybeLogProgress(state);
    }
  }

  async finishRun(): Promise<WorkerRunSummary> {
    const promise = this.requireRunPromise();
    const state = this.requireState();
    state.queue.close();
    try {
      return await promise;
    } finally {
      this.clearRun();
    }
  }

  abortRun(): void {
    if (!this.runState) return;
    this.runState.queue.close();
    this.clearRun();
  }

  isRunning(): boolean {
    return this.runState !== null;
  }

  private maybeLogProgress(state: RunState): void {
    if (state.eventsProcessed === 0) return;
    if (state.eventsProcessed % this.progressStep === 0) {
      this.log(`[worker] processed ${formatNumber(state.eventsProcessed)} events`);
    }
  }

  private requireState(): RunState {
    if (!this.runState) throw new Error('no active run');
    return this.runState;
  }

  private requireRunPromise(): Promise<WorkerRunSummary> {
    if (!this.runPromise) throw new Error('no active run');
    return this.runPromise;
  }

  private clearRun(): void {
    this.runState = null;
    this.runPromise = null;
  }
}
