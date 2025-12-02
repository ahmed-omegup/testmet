import { performance } from 'node:perf_hooks';
import { runLimitStreamAsync, StreamItem } from './limit-index/limitStream';
import { DownstreamEvent } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore, LmdbDurability } from './docStore';
import { SocketDocState, WorkerRunConfig, WorkerRunSummary } from './socketProtocol';

interface RunState {
  docStore?: LmdbDocStore<SocketDocState>;
  retrievalJob?: RetrievalJobWorker<SocketDocState>;
  matchEvents: number;
  evictions: number;
  retrievalBatches: number;
  retrievalDocs: number;
  eventsProcessed: number;
  startTime: number;
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
  private runGenerator: Generator<void, WorkerRunSummary, StreamItem<SocketDocState>> | null = null;
  private readonly docStoreDurability: LmdbDurability;
  private readonly progressStep: number;
  private readonly log: (message: string) => void;

  constructor(options: WorkerRuntimeOptions = {}) {
    this.docStoreDurability = options.docStoreDurability ?? 'durable';
    this.progressStep = Math.max(1, options.progressStep ?? 10000);
    this.log = options.log ?? (() => { });
  }

  startRun(config: WorkerRunConfig): void {
    if (this.runGenerator) throw new Error('run already in progress');
    const runState: RunState = {
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
    const that = this;
    this.runGenerator = (function* () {
      yield* runLimitStreamAsync(getScore, evt => handleDownstreamEvent(runState, evt), {
        retrievalJob: runState.retrievalJob,
        docStore: runState.docStore,
      });
      that.log('[worker] run completed');
      if (runState.retrievalJob) {
        runState.retrievalJob.stop();
        that.log('[worker] retrieval job stopped');
      }
      const durationMs = performance.now() - runState.startTime;
      return buildSummary(runState, durationMs);
    })();
  }

  enqueue(item: StreamItem<SocketDocState>): void {
    const state = this.requireState();
    this.runGenerator!.next(item);
    state.eventsProcessed += 1;
    this.maybeLogProgress(state);
  }

  enqueueBatch(items: Iterable<StreamItem<SocketDocState>>): void {
    const state = this.requireState();
    for (const item of items) {
      this.runGenerator!.next(item);
      state.eventsProcessed += 1;
      this.maybeLogProgress(state);
    }
  }

  finishRun(): WorkerRunSummary {
    const res = this.runGenerator!.next()
    try {
      if (!res.done) throw new Error('run generator did not complete as expected');
      return res.value;
    } finally {
      this.clearRun();
    }
  }

  abortRun(): void {
    if (!this.runState) return;
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

  private clearRun(): void {
    this.runState = null;
    this.runGenerator = null;
  }
}
