import { performance } from 'node:perf_hooks';
import { runLimitStream, StreamItem } from './limit-index/limitStream';
import { DownstreamEvent } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore, LmdbDurability } from './docStore';
import { SocketDocState, WorkerRunSummary } from './socketProtocol';

const debugEvictions = process.env.PERF_DEBUG_EVICS === '1';

interface RunState {
  docStore?: LmdbDocStore<SocketDocState>;
  retrievalJob?: RetrievalJobWorker<SocketDocState>;
  matchEvents: number;
  evictions: number;
  retrievalBatches: number;
  retrievalDocs: number;
  eventsProcessed: number;
  startTime?: number;
}


const getScore = (state: SocketDocState) => state.scoreValue;

const handleDownstreamEvent = (state: RunState, event: DownstreamEvent<SocketDocState>): void => {
  if (debugEvictions) {
    if (event.kind === 'match') {
      event.matchesNew.sort();
      event.evictions.sort();
      event.matchesOld.sort();
    }
    if (event.kind === 'retrieval') {
      event.docs.sort();
    }
    console.log('>>', JSON.stringify(event, (k, v) => typeof v === 'bigint' ? String(v) : v));
  }
  if (event.kind === 'match') {
    state.matchEvents += 1;
    state.evictions += event.evictions.length;
    return;
  }
  state.retrievalBatches += 1;
  state.retrievalDocs += event.docs.length;
};

const buildSummary = (state: RunState, endTs: number): WorkerRunSummary => ({
  endTs,
  startTs: state.startTime ?? 0,
  eventsProcessed: state.eventsProcessed,
  matchEvents: state.matchEvents,
  evictions: state.evictions,
  retrievalBatches: state.retrievalBatches,
  retrievalDocs: state.retrievalDocs,
});

export interface WorkerRuntimeOptions {
  enableRetrieval?: boolean;
  docStoreDurability?: LmdbDurability;
  progressStep?: number;
  log?: (message: string) => void;
}

const formatNumber = (value: number) => value.toLocaleString('en-US');

export class WorkerRuntime {
  private runState: RunState;
  private runGenerator: Generator<void, WorkerRunSummary, StreamItem<SocketDocState>>;
  private readonly docStoreDurability: LmdbDurability;
  private readonly progressStep: number;
  private readonly log: (message: string) => void;

  constructor(options: WorkerRuntimeOptions = {}) {
    this.docStoreDurability = options.docStoreDurability ?? 'durable';
    this.progressStep = Math.max(1, options.progressStep ?? 10000);
    this.log = options.log ?? (() => { });
    const runState: RunState = {
      matchEvents: 0,
      evictions: 0,
      retrievalBatches: 0,
      retrievalDocs: 0,
      eventsProcessed: 0,
    };
    if (options.enableRetrieval) {
      runState.docStore = new LmdbDocStore<SocketDocState>({ durability: this.docStoreDurability });
      runState.retrievalJob = new RetrievalJobWorker<SocketDocState>(
        ids => runState.docStore!.getMany(ids),
        event => {
          runState.retrievalBatches += 1;
          runState.retrievalDocs += event.docs.length;
        },
        debugEvictions ? console.log : () => {}
      );
    }
    this.runState = runState;
    const that = this;
    this.runGenerator = (function* () {
      yield* runLimitStream(getScore, evt => handleDownstreamEvent(runState, evt), {
        retrievalJob: runState.retrievalJob,
        docStore: runState.docStore,
      });
      that.log('[worker] run completed');
      if (runState.retrievalJob) {
        runState.retrievalJob.stop();
        that.log('[worker] retrieval job stopped');
      }
      return buildSummary(runState, performance.now());
    })();
    this.runGenerator.next()
  }

  hello(): void {
    this.runState.startTime = performance.now();
  }

  enqueueBatch(items: Iterable<StreamItem<SocketDocState>>): void {
    const state = this.requireState();
    for (const item of items) {
      if (debugEvictions) {
        console.log('<<', JSON.stringify(item, (k, v) => typeof v === 'bigint' ? String(v) : v));
      }
      this.runGenerator!.next(item);
      state.eventsProcessed += 1;
      this.maybeLogProgress(state);
    }
  }

  finishRun(): WorkerRunSummary {
    const res = this.runGenerator!.next()
    if (!res.done) throw new Error('run generator did not complete as expected');
    return res.value;
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
}
