import dotenv from 'dotenv';
import net from 'node:net';
import readline from 'node:readline';
import { once } from 'node:events';
import { performance } from 'node:perf_hooks';
import { runLimitStream, StreamItem } from './limit-index/limitStream';
import { DocId, Score, QuerySpec, DownstreamEvent } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore } from './docStore';
import {
  ClientMessage,
  ServerMessage,
  SocketDocState,
  streamItemToWire,
  WorkerRunConfig,
  WorkerRunSummary,
} from './socketProtocol';

dotenv.config({ path: process.env.PERF_ENV || '.env' });

type PerfDocState = SocketDocState;

type PerfConfig = {
  seed: number;
  documents: number;
  customers: number;
  duration: number;
  updateRate: number;
  insertRate: number;
  deleteRate: number;
  queryLimit: number;
  rangeMin: number;
  rangeMax: number;
  density: number;
  enableRetrieval: boolean;
};

const debugEvictions = process.env.PERF_DEBUG_EVICS === '1';
const remoteWorkerHostEnv = process.env.PERF_WORKER_HOST;
const remoteWorkerToggle = process.env.PERF_REMOTE_WORKER;
const remoteWorkerEnabled = remoteWorkerToggle === '1' || (remoteWorkerToggle === undefined && Boolean(remoteWorkerHostEnv));
const remoteWorkerHost = remoteWorkerHostEnv ?? '127.0.0.1';
const remoteWorkerPort = Number(process.env.PERF_WORKER_PORT ?? 4040);
const remoteWorkerBatchSize = Math.max(1, Number(process.env.PERF_WORKER_BATCH_SIZE ?? 512));
const remoteWorkerBatchMs = Math.max(0, Number(process.env.PERF_WORKER_BATCH_MS ?? 4));
const progressStep = Math.max(1, Number(process.env.PERF_PROGRESS_STEP ?? 10000));

const config: PerfConfig & {
  range: number;
  updatesPerTick: number;
  insertsPerTick: number;
  deletesPerTick: number;
} = {
  seed: Number(process.env.PERF_SEED ?? 42),
  documents: Number(process.env.PERF_DOCUMENTS ?? 100000),
  customers: Number(process.env.PERF_CUSTOMERS ?? 5000),
  duration: Number(process.env.PERF_DURATION ?? 5),
  updateRate: Number(process.env.PERF_UPDATE_RATE ?? 0.02),
  insertRate: Number(process.env.PERF_INSERT_RATE ?? 0.005),
  deleteRate: Number(process.env.PERF_DELETE_RATE ?? 0.005),
  queryLimit: Number(process.env.PERF_QUERY_LIMIT ?? 50),
  rangeMin: Number(process.env.PERF_RANGE_MIN ?? 100),
  rangeMax: Number(process.env.PERF_RANGE_MAX ?? 600),
  density: Number(process.env.PERF_DENSITY ?? 10),
  enableRetrieval: process.env.PERF_ENABLE_RETRIEVAL !== 'false',
  range: 0,
  updatesPerTick: 0,
  insertsPerTick: 0,
  deletesPerTick: 0,
};

config.range = Math.max(1, Math.floor(config.documents / Math.max(1, config.density)));
config.updatesPerTick = Math.max(1, Math.floor(config.documents * config.updateRate));
config.insertsPerTick = Math.max(0, Math.floor(config.documents * config.insertRate));
config.deletesPerTick = Math.max(0, Math.floor(config.documents * config.deleteRate));

const toScore = (value: number): Score => value as Score;
const toDocId = (value: number): DocId => BigInt(value) as DocId;

const prng = (seed: number) => {
  let state = seed % 0x7fffffff;
  if (state <= 0) state += 0x7fffffff;
  return () => {
    state = (state * 48271) % 0x7fffffff;
    return state / 0x7fffffff;
  };
};

const randomScore = (rand: () => number) => Math.floor(rand() * config.range);
const createDoc = (score: number): PerfDocState => ({ scoreValue: toScore(score) } as PerfDocState);
const getScore = (doc: PerfDocState): Score => doc.scoreValue;

const docStates = new Map<DocId, PerfDocState>();
const docOrder: DocId[] = [];
const docIndex = new Map<DocId, number>();

const trackDoc = (id: DocId, state: PerfDocState) => {
  docStates.set(id, state);
  docIndex.set(id, docOrder.length);
  docOrder.push(id);
};

const updateDoc = (id: DocId, state: PerfDocState) => {
  docStates.set(id, state);
};

const removeDoc = (id: DocId) => {
  const idx = docIndex.get(id);
  if (idx === undefined) return false;
  const lastIdx = docOrder.length - 1;
  const lastId = docOrder[lastIdx]!;
  docOrder[idx] = lastId;
  docIndex.set(lastId, idx);
  docOrder.pop();
  docIndex.delete(id);
  docStates.delete(id);
  return true;
};

const pickDocId = (rand: () => number): DocId | null => {
  if (docOrder.length === 0) return null;
  const idx = Math.floor(rand() * docOrder.length);
  return docOrder[idx]!;
};

const customerRange = (rand: () => number): [number, number] => {
  const width = 100 + Math.min(rand() * 500);
  const a = rand() * (config.range - width);
  return [Math.floor(a), Math.floor(a + width)];
};

const SEED_BATCH_SIZE = Number(process.env.PERF_SEED_BATCH ?? 4096);

const buildEvents = function* (): Generator<StreamItem<PerfDocState>> {
  const rand = prng(config.seed);

  let nextDocNumericId = config.documents;
  const seedStart = performance.now();
  const seedBuffer: Array<{ id: DocId; state: PerfDocState }> = [];

  const flushSeed = () => {
    if (!seedBuffer.length) return;
    const batch = seedBuffer.splice(0, seedBuffer.length);
    return { kind: 'seed-docs', docs: batch } as StreamItem<PerfDocState>;
  };

  for (let i = 0; i < config.documents; i++) {
    const id = toDocId(i);
    const state = createDoc(randomScore(rand));
    trackDoc(id, state);
    seedBuffer.push({ id, state });
    if (seedBuffer.length >= SEED_BATCH_SIZE) {
      const event = flushSeed();
      if (event) yield event;
    }
  }
  const leftoverSeed = flushSeed();
  if (leftoverSeed) yield leftoverSeed;

  const queryStart = performance.now();
  if(!debugEvictions) console.log(`[perf] seeded ${config.documents.toLocaleString('en-US')} documents in ${(queryStart - seedStart).toFixed(2)} ms`);

  // Register queries (customers)
  const limit = BigInt(config.queryLimit);
  for (let i = 0; i < config.customers; i++) {
    const [min, max] = customerRange(rand);
    const spec: QuerySpec = { minScore: toScore(min), maxScore: toScore(max), limit };
    yield { kind: 'query-add', spec };
  }

  const upStart = performance.now();
  if(!debugEvictions) if(!debugEvictions) console.log(`[perf] seeding queries took ${(upStart - queryStart).toFixed(2)} ms`);

  // Periodic updates
  for (let tick = 0; tick < config.duration; tick++) {
    // updates
    for (let u = 0; u < config.updatesPerTick; u++) {
      const id = pickDocId(rand);
      if (!id) break;
      const old = docStates.get(id) ?? null;
      const updated = createDoc(randomScore(rand));
      updateDoc(id, updated);
      yield { kind: 'doc-change', change: { id, old, new: updated } };
    }

    // inserts
    for (let ins = 0; ins < config.insertsPerTick; ins++) {
      const id = toDocId(nextDocNumericId++);
      const state = createDoc(randomScore(rand));
      trackDoc(id, state);
      yield { kind: 'doc-change', change: { id, old: null, new: state } };
    }

    // deletes
    for (let del = 0; del < config.deletesPerTick; del++) {
      const id = pickDocId(rand);
      if (!id) break;
      const old = docStates.get(id) ?? null;
      if (!old) continue;
      removeDoc(id);
      yield { kind: 'doc-change', change: { id, old, new: null } };
    }
  }
  const end = performance.now();
  const nbEvents = config.duration * (config.updatesPerTick + config.insertsPerTick + config.deletesPerTick)
  if(!debugEvictions) if(!debugEvictions) console.log(`[perf] ${nbEvents} events processing took ${(end - upStart).toFixed(2)} ms`);
};

const formatNumber = (value: number) => value.toLocaleString('en-US');

async function main() {
  if(!debugEvictions) console.log('[perf] configuration:', {
    seed: config.seed,
    documents: config.documents,
    customers: config.customers,
    duration: config.duration,
    updateRate: config.updateRate,
    insertRate: config.insertRate,
    deleteRate: config.deleteRate,
    queryLimit: config.queryLimit,
    rangeMin: config.rangeMin,
    rangeMax: config.rangeMax,
    density: config.density,
    enableRetrieval: config.enableRetrieval,
  });

  const events = buildEvents();
  const seedEventCount = Math.ceil(config.documents / SEED_BATCH_SIZE);
  const nbEvents = config.duration * (config.updatesPerTick + config.insertsPerTick + config.deletesPerTick)
    + seedEventCount + config.customers;
  if(!debugEvictions) console.log(`[perf] generated ${formatNumber(nbEvents)} stream items`);

  const workerConfig: WorkerRunConfig = { enableRetrieval: config.enableRetrieval };
  let summary: WorkerRunSummary;
  if (remoteWorkerEnabled) {
    if(!debugEvictions) console.log(`[perf] using remote worker at ${remoteWorkerHost}:${remoteWorkerPort}`);
    summary = await runRemote(events, workerConfig, remoteWorkerHost, remoteWorkerPort);
  } else {
    summary = await runLocal(events, workerConfig, nbEvents);
  }

  if(!debugEvictions) logSummary(summary);
}

async function runLocal(
  events: Iterable<StreamItem<PerfDocState>>,
  workerConfig: WorkerRunConfig,
  nbEvents: number
): Promise<WorkerRunSummary> {
  let matchEvents = 0;
  let evictions = 0;
  let retrievalBatches = 0;
  let retrievalDocs = 0;

  const docStore = workerConfig.enableRetrieval
    ? new LmdbDocStore<PerfDocState>({ durability: 'relaxed' })
    : undefined;
  const retrievalJob = workerConfig.enableRetrieval && docStore
    ? new RetrievalJobWorker<PerfDocState>(
      ids => docStore.getMany(ids),
      event => {
        retrievalBatches += 1;
        retrievalDocs += event.docs.length;
      }
    )
    : undefined;

  const start = performance.now();
  let streamedEvents = 0;
  const instrumentedEvents = (function* () {
    for (const e of events) {
      streamedEvents += 1;
      if (!debugEvictions && streamedEvents % progressStep === 0) {
        console.log(`[perf] processed ${formatNumber(streamedEvents)} events (local)`);
      }
      if (debugEvictions) {
        console.log('<<', JSON.stringify(e, (k, v) => typeof v === 'bigint' ? String(v) : v));
      }
      yield e;
    }
  })();
  runLimitStream(
    instrumentedEvents,
    getScore,
    (event: DownstreamEvent<PerfDocState>) => {
      if (debugEvictions) {
        if(event.kind === 'match') {
          event.matchesNew.sort();
          event.evictions.sort();
          event.matchesOld.sort();
        }
        if(event.kind === 'retrieval') {
          event.docs.sort();
        }
        console.log('>>', JSON.stringify(event, (k, v) => typeof v === 'bigint' ? String(v) : v));
      }
      if (event.kind === 'match') {
        matchEvents += 1;
        evictions += event.evictions.length;
      }
    },
    {
      retrievalJob: retrievalJob ?? undefined,
      docStore,
    }
  );
  if (retrievalJob) {
    await retrievalJob.stop();
  }
  const durationMs = performance.now() - start;

  return {
    durationMs,
    eventsProcessed: nbEvents,
    matchEvents,
    evictions,
    retrievalBatches,
    retrievalDocs,
  };
}

async function runRemote(
  events: Iterable<StreamItem<PerfDocState>>,
  workerConfig: WorkerRunConfig,
  host: string,
  port: number
): Promise<WorkerRunSummary> {
  const socket = net.createConnection({ host, port });
  socket.setEncoding('utf8');
  socket.on('error', err => {
    console.error('[perf] worker socket error', err);
  });
  const rl = readline.createInterface({ input: socket, crlfDelay: Infinity });
  const messages = readServerMessages(rl);

  const awaitMessage = async (): Promise<ServerMessage> => {
    const { value, done } = await messages.next();
    if (done) throw new Error('worker disconnected');
    return value;
  };

  const waitFor = async (type: ServerMessage['type']): Promise<void> => {
    while (true) {
      const message = await awaitMessage();
      if (message.type === 'error') throw new Error(message.message);
      if (message.type === type) return;
    }
  };

  const closeConnection = () => {
    rl.close();
    socket.end();
    socket.destroy();
  };

  try {
    await new Promise<void>((resolve, reject) => {
      const onConnect = () => {
        socket.off('error', onError);
        resolve();
      };
      const onError = (err: Error) => {
        socket.off('connect', onConnect);
        reject(err);
      };
      socket.once('connect', onConnect);
      socket.once('error', onError);
    });

    await writeMessage(socket, { type: 'hello', role: 'client', version: 1 });
    await waitFor('hello');

    await writeMessage(socket, { type: 'run', config: workerConfig });
    await waitFor('run-accepted');

    const batch: ReturnType<typeof streamItemToWire>[] = [];
    let eventsSent = 0;
    let lastFlush = performance.now();
    const flushBatch = async () => {
      if (!batch.length) return;
      const payload = batch.splice(0, batch.length);
      await writeMessage(socket, { type: 'event-batch', items: payload });
      lastFlush = performance.now();
    };

    for (const item of events) {
      batch.push(streamItemToWire(item));
      eventsSent += 1;
      if (!debugEvictions && eventsSent % progressStep === 0) {
        console.log(`[perf] sent ${formatNumber(eventsSent)} events to worker`);
      }
      const now = remoteWorkerBatchMs > 0 ? performance.now() : 0;
      if (batch.length >= remoteWorkerBatchSize || (remoteWorkerBatchMs > 0 && now - lastFlush >= remoteWorkerBatchMs)) {
        await flushBatch();
      }
    }
    if (eventsSent && eventsSent % progressStep !== 0 && !debugEvictions) {
      console.log(`[perf] sent ${formatNumber(eventsSent)} events to worker`);
    }
    await flushBatch();
    console.log('batch flushed');
    await writeMessage(socket, { type: 'end' });

    while (true) {
      const message = await awaitMessage();
      console.log('message received', message);
      if (message.type === 'summary') {
        return message.summary;
      }
      if (message.type === 'error') {
        throw new Error(message.message);
      }
    }
  } finally {
    closeConnection();
  }
}

function logSummary(summary: WorkerRunSummary): void {
  const eventsPerSec = summary.durationMs === 0
    ? 'n/a'
    : (summary.eventsProcessed / (summary.durationMs / 1000)).toFixed(2);
  console.log('\n[perf] summary');
  console.log(`  duration: ${summary.durationMs.toFixed(2)} ms (~${eventsPerSec} events/s)`);
  console.log(`  match events: ${formatNumber(summary.matchEvents)} (evictions: ${formatNumber(summary.evictions)})`);
  if (config.enableRetrieval) {
    console.log(`  retrieval batches: ${formatNumber(summary.retrievalBatches)} (docs: ${formatNumber(summary.retrievalDocs)})`);
  } else {
    console.log('  retrieval batches: disabled');
  }
}

async function* readServerMessages(rl: readline.Interface): AsyncGenerator<ServerMessage> {
  for await (const line of rl) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    try {
      yield JSON.parse(trimmed) as ServerMessage;
    } catch (err) {
      console.error('[perf] worker emitted invalid json', err);
    }
  }
}

const writeMessage = async (socket: net.Socket, message: ClientMessage): Promise<void> => {
  if (!socket.writable) throw new Error('worker connection closed');
  const payload = `${JSON.stringify(message)}\n`;
  if (socket.write(payload)) return;
  await once(socket, 'drain');
};

main().catch(err => {
  console.error('[perf] failed', err);
  process.exit(1);
});
