import dotenv from 'dotenv';
import net from 'node:net';
import readline from 'node:readline';
import { once } from 'node:events';
import { performance } from 'node:perf_hooks';
import { runLimitStream, StreamItem } from './limit-index/limitStream';
import { DocId, Score, QuerySpec, LimitMatchEvent, QueryId } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore } from './docStore';
import {
  ClientMessage,
  fromDocId,
  ServerMessage,
  SocketDocState,
  WireDocChange,
  WireDocRef,
  WireQuerySpec,
  WireStreamItem,
  wireToStreamItem,
  WorkerRunSummary,
} from './socketProtocol';
import { createInProcessWorkerClient } from './transport';
import { isReadable } from 'node:stream';

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
  remoteWorkerEmbedded: boolean;
};

const checkQuery = process.env.CHECK_QUERY === '1';
const debugEvictions = process.env.PERF_DEBUG_EVICS === '1';
const remoteWorkerHostEnv = process.env.PERF_WORKER_HOST;
const remoteWorkerToggle = process.env.PERF_REMOTE_WORKER;
const remoteWorkerEnabled = remoteWorkerToggle === '1' || (remoteWorkerToggle === undefined && Boolean(remoteWorkerHostEnv));
const remoteWorkerHost = remoteWorkerHostEnv ?? '127.0.0.1';
const remoteWorkerPort = Number(process.env.PERF_WORKER_PORT ?? 4040);
const remoteWorkerEmbedded = process.env.PERF_EMBED_WORKER === '1';
const progressStep = Math.max(1, Number(process.env.PERF_PROGRESS_STEP ?? 10000));

const config: PerfConfig & {
  range: number;
  updatesPerTick: number;
  insertsPerTick: number;
  deletesPerTick: number;
} = {
  seed: Number(process.env.PERF_SEED ?? 42),
  documents: Number(process.env.PERF_DOCUMENTS ?? 1000),
  customers: Number(process.env.PERF_CUSTOMERS ?? 1000),
  duration: Number(process.env.PERF_DURATION ?? 5),
  updateRate: Number(process.env.PERF_UPDATE_RATE ?? 0.05),
  insertRate: Number(process.env.PERF_INSERT_RATE ?? 0.01),
  deleteRate: Number(process.env.PERF_DELETE_RATE ?? 0.01),
  queryLimit: Number(process.env.PERF_QUERY_LIMIT ?? 200),
  rangeMin: Number(process.env.PERF_RANGE_MIN ?? 100),
  rangeMax: Number(process.env.PERF_RANGE_MAX ?? 600),
  density: Number(process.env.PERF_DENSITY ?? 10),
  range: 0,
  updatesPerTick: 0,
  insertsPerTick: 0,
  deletesPerTick: 0,
  remoteWorkerEmbedded
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
  docStates.set(id, {scoreValue: docStates.get(id)!.scoreValue + 1 });
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

const buildEvents = function* (): Generator<WireStreamItem> {
  const rand = prng(config.seed);

  let nextDocNumericId = config.documents;
  const seedStart = performance.now();

  const createBuffer = <T, V>(batchSize: number, map: (batch: T[]) => V) => {
    const buffer: Array<T> = [];
    function* flush() {
      if (!buffer.length) return;
      const batch = buffer.splice(0, buffer.length);
      yield map(batch)
    };
    function* push(data: T) {
      buffer.push(data);
      if (buffer.length >= batchSize) {
        yield* flush();
      }
    }
    return { push, flush }
  }
  const { flush: flushSeed, push: pushSeed } = createBuffer<WireDocRef, WireStreamItem>(SEED_BATCH_SIZE, batch => ({ kind: 'seed-docs', docs: batch }))

  for (let i = 0; i < config.documents; i++) {
    const id = toDocId(i);
    const state = createDoc(randomScore(rand));
    trackDoc(id, state);
    yield* pushSeed({ id: fromDocId(id), state });
  }
  yield* flushSeed();

  const queryStart = performance.now();
  if (!debugEvictions) console.log(`[perf] seeded ${config.documents.toLocaleString('en-US')} documents in ${(queryStart - seedStart).toFixed(2)} ms`);

  // Register queries (customers)
  const limit = BigInt(config.queryLimit);
  const adds = createBuffer<WireQuerySpec, WireStreamItem>(config.customers, batch => ({
    kind: 'query-adds', specs: batch
  }))
  for (let i = 0; i < config.customers; i++) {
    const [min, max] = customerRange(rand);
    const spec: WireQuerySpec = { minScore: toScore(min), maxScore: toScore(max), limit: limit.toString() };
    yield* adds.push(spec)
  }
  yield* adds.flush()

  const upStart = performance.now();
  if (!debugEvictions) console.log(`[perf] seeding queries took ${(upStart - queryStart).toFixed(2)} ms`);

  const updates = createBuffer<WireDocChange, WireStreamItem>(SEED_BATCH_SIZE, batch => ({
    kind: 'doc-changes', changes: batch
  }))
  // Periodic updates
  for (let tick = 0; tick < config.duration; tick++) {
    // updates
    for (let u = 0; u < config.updatesPerTick; u++) {
      const id = pickDocId(rand);
      if (!id) break;
      const old = docStates.get(id) ?? null;
      const updated = createDoc(randomScore(rand));
      updateDoc(id, updated);
      yield* updates.push({ id: fromDocId(id), old, new: updated });
    }

    // inserts
    for (let ins = 0; ins < config.insertsPerTick; ins++) {
      const id = toDocId(nextDocNumericId++);
      const state = createDoc(randomScore(rand));
      trackDoc(id, state);
      yield* updates.push({ id: fromDocId(id), old: null, new: state });
    }

    // deletes
    for (let del = 0; del < config.deletesPerTick; del++) {
      const id = pickDocId(rand);
      if (!id) break;
      const old = docStates.get(id) ?? null;
      if (!old) continue;
      removeDoc(id);
      yield* updates.push({ id: fromDocId(id), old, new: null });
    }
  }
  yield* updates.flush()
  const end = performance.now();
  const nbEvents = config.duration * (config.updatesPerTick + config.insertsPerTick + config.deletesPerTick)
  if (!debugEvictions) console.log(`[perf] ${nbEvents} events processing took ${(end - upStart).toFixed(2)} ms`);
};

const formatNumber = (value: number) => value.toLocaleString('en-US');

async function main() {
  if (!debugEvictions) console.log('[perf] configuration:', config);

  const events = buildEvents();
  const seedEventCount = Math.ceil(config.documents / SEED_BATCH_SIZE);
  const nbEvents = config.duration * (config.updatesPerTick + config.insertsPerTick + config.deletesPerTick)
    + seedEventCount + config.customers;
  if (!debugEvictions) console.log(`[perf] generated ${formatNumber(nbEvents)} stream items`);

  let summary: WorkerRunSummary;
  const start = performance.now();
  if (remoteWorkerEnabled) {
    if (!debugEvictions) {
      if (remoteWorkerEmbedded) {
        console.log('[perf] using embedded worker transport');
      } else {
        console.log(`[perf] using remote worker at ${remoteWorkerHost}:${remoteWorkerPort}`);
      }
    }
    summary = await runRemote(events, {
      host: remoteWorkerHost,
      port: remoteWorkerPort,
      embedded: remoteWorkerEmbedded,
    });
  } else {
    summary = await runLocal((function* () {
      for (const e of events) yield* wireToStreamItem(e)
    })(), nbEvents);
  }

  if (!debugEvictions) logSummary(summary, start);
}

async function runLocal(
  events: Iterable<StreamItem<PerfDocState>>,
  nbEvents: number
): Promise<WorkerRunSummary> {
  const gen = runEmbed(nbEvents);
  gen.next();
  let i = 0
  for (const e of events) {
    gen.next(e);
    await new Promise(res => setImmediate(res))
    if (++i % 1000 === 0) console.log(i)
  }
  const p = gen.next();
  if (p.done || !(p.value instanceof Promise)) {
    throw new Error('expected final result to be a promise');
  }
  await p.value;
  const result = gen.next();
  if (!result.done) {
    throw new Error('expected generator to be done');
  }
  return result.value;
}



function* runEmbed(
  nbEvents: number
): Generator<void | Promise<void>, WorkerRunSummary, StreamItem<PerfDocState> | void> {
  let matchEvents = 0;
  let evictions = 0;
  let retrievalBatches = 0;
  let retrievalDocs = 0;


  const docs = checkQuery ? {
    db: new Map<DocId, PerfDocState>(), queries: new Map<QueryId, [QuerySpec, Map<DocId, PerfDocState>]>()
  } : undefined;

  (global as any)['docs'] = docs

  const docStore = new LmdbDocStore<PerfDocState>({ durability: 'relaxed' });
  const retrievalJob = new RetrievalJobWorker<PerfDocState>(
    ids => docStore.getMany(ids),
    event => {
      if (debugEvictions) {
        console.log('>>', JSON.stringify(event, (k, v) => typeof v === 'bigint' ? String(v) : v));
      }
      if (docs) {
        for (const { docId, queries, state } of event.docs) {
          for (const qId of queries) {
            if (ignore(qId)) continue;
            const [_, q] = docs.queries.get(qId)!;
            if (!q.has(docId)) q.set(docId, { ...state, ret: 1 } as any);
          }
        }
      }
      retrievalBatches += 1;
      retrievalDocs += event.docs.length;
    },
  );

  const start = performance.now();
  let streamedEvents = 0;
  const ignore = (qId: QueryId) => {
    return false
  }
  const gen = runLimitStream(
    getScore,
    (event: LimitMatchEvent<PerfDocState>) => {
      if (debugEvictions) {
        // event.matchesNew.sort();
        // event.evictions.sort();
        // event.matchesOld.sort();
        console.log('>>', JSON.stringify(event, (k, v) => typeof v === 'bigint' ? String(v) : v));
      }
      if (docs) {
        for (const qId of event.matchesOld) {
          if (!ignore(qId)) docs.queries.get(qId)![1].delete(event.docId);
        }
        for (const qId of event.matchesNew) {
          if (!ignore(qId)) {
            if (event.new) docs.queries.get(qId)![1].set(event.docId, event.new);
            else docs.queries.get(qId)![1].delete(event.docId);
          }
        }
        for (const [qId, evicted] of event.evictions) {
          if (!ignore(qId)) docs.queries.get(qId)![1].delete(evicted);
        }
      }
      if (event.kind === 'match') {
        matchEvents += 1;
        evictions += event.evictions.length;
      }
    },
    {
      retrievalJob: retrievalJob,
      docStore,
    }
  );
  gen.next();
  let qid = 0n;
  while (true) {
    const e = yield;
    if (!e) {
      gen.next();
      break;
    }

    streamedEvents += 1;
    if (!debugEvictions && streamedEvents % progressStep === 0) {
      console.log(`[perf] processed ${formatNumber(streamedEvents)} events (local)`);
    }
    if (debugEvictions) {
      console.log('<<', JSON.stringify(e, (k, v) => typeof v === 'bigint' ? String(v) : v));
    }
    if (docs) {
      if (e.kind === 'doc-change') {
        const { id, new: next } = e.change;
        if (next) {
          docs.db.set(id, next);
        } else {
          docs.db.delete(id);
        }
      } else if (e.kind === 'seed-docs') {
        for (const doc of e.docs) {
          docs.db.set(doc.id, doc.state);
        }
      } else if (e.kind === 'query-remove') {
        // no-op
      } else if (e.kind === 'query-add') {
        docs.queries.set(++qid, [e.spec, new Map()]);
      } else {
        const _: never = e;
      }
    }
    gen.next(e);
  }

  if (retrievalJob) {
    yield retrievalJob.stop();
  }

  if (docs) for (const [qId, [querySpec, query]] of docs.queries) {
    if (ignore(qId)) continue;
    if (!querySpec) throw new Error('missing query spec');
    const expectedMatches: Map<DocId, PerfDocState> = new Map();
    for (const [docId, state] of docs.db) {
      const score = getScore(state);
      if (score >= querySpec.minScore && score <= querySpec.maxScore) {
        expectedMatches.set(docId, state);
      }
    }
    for (const [k, q] of query) {
      if (q === null) query.delete(k);
    }
    const sortedMatches = Array.from(expectedMatches.entries()).sort((a, b) => {
      return getScore(a[1]) - getScore(b[1]);
    }).slice(0, Number(querySpec.limit));
    if (sortedMatches.length !== query.size) {
      console.log('query spec:', qId, querySpec);
      console.log('expected matches:', sortedMatches);
      console.log('actual matches:', Array.from(query.entries()));
      throw new Error(`mismatched number of query matches: expected ${sortedMatches.length}, got ${query.size}`);
    }
    for (const [docId, state] of sortedMatches) {
      const matchedState = query.get(docId);
      if (!matchedState) {
        throw new Error(`missing matched doc ${docId.toString()} ${JSON.stringify(state)}`);
      }
      if (getScore(matchedState) !== getScore(state)) {
        throw new Error(`mismatched state for doc ${docId.toString()}`);
      }
    }
  }

  return {
    endTs: performance.now(),
    eventsProcessed: nbEvents,
    matchEvents,
    evictions,
    retrievalBatches,
    retrievalDocs,
    startTs: start,
  };
}


interface RemoteConnection {
  write(message: ClientMessage): Promise<void>;
  nextMessage(): Promise<ServerMessage>;
  close(): void;
}

interface RemoteOptions {
  host: string;
  port: number;
  embedded?: boolean;
}

async function runRemote(
  events: Iterable<WireStreamItem>,
  options: RemoteOptions
): Promise<WorkerRunSummary> {
  const connection = options.embedded
    ? createEmbeddedRemoteConnection()
    : await createTcpRemoteConnection(options.host, options.port);

  const awaitMessage = async (): Promise<ServerMessage> => {
    return connection.nextMessage();
  };

  const write = (message: ClientMessage) => connection.write(message);

  try {
    await write({ type: 'hello', role: 'client', version: 1 });

    let eventsSent = 0;

    for (const item of events) {
      await write({ type: 'event', item });
      eventsSent += 1;
      if (!debugEvictions && eventsSent % progressStep === 0) {
        console.log(`[perf] sent ${formatNumber(eventsSent)} events to worker`);
      }
    }
    if (eventsSent && eventsSent % progressStep !== 0 && !debugEvictions) {
      console.log(`[perf] sent ${formatNumber(eventsSent)} events to worker`);
    }
    await write({ type: 'end' });

    while (true) {
      const message = await awaitMessage();
      if (message.type === 'summary') {
        return message.summary;
      }
      if (message.type === 'error') {
        throw new Error(message.message);
      }
    }
  } finally {
    connection.close();
  }
}

function logSummary(summary: WorkerRunSummary, start: number): void {
  const durationMs = summary.endTs - (summary.startTs ?? start);
  const eventsPerSec = durationMs === 0
    ? 'n/a'
    : (summary.eventsProcessed / (durationMs / 1000)).toFixed(2);
  console.log('\n[perf] summary');
  console.log(`  duration: ${durationMs.toFixed(2)} ms (~${eventsPerSec} events/s)`);
  console.log(`  match events: ${formatNumber(summary.matchEvents)} (evictions: ${formatNumber(summary.evictions)})`);
  console.log(`  retrieval batches: ${formatNumber(summary.retrievalBatches)} (docs: ${formatNumber(summary.retrievalDocs)})`);
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

class AsyncMessageQueue<T> {
  private queue: T[] = [];
  private waiters: Array<{ resolve: (value: T) => void; reject: (err: Error) => void }> = [];
  private closedError: Error | null = null;

  push(value: T): void {
    if (this.closedError) return;
    const waiter = this.waiters.shift();
    if (waiter) {
      waiter.resolve(value);
      return;
    }
    this.queue.push(value);
  }

  close(err?: Error): void {
    if (this.closedError) return;
    this.closedError = err ?? new Error('connection closed');
    while (this.waiters.length) {
      this.waiters.shift()!.reject(this.closedError);
    }
  }

  async next(): Promise<T> {
    if (this.queue.length) {
      return this.queue.shift()!;
    }
    if (this.closedError) throw this.closedError;
    return new Promise<T>((resolve, reject) => {
      this.waiters.push({ resolve, reject });
    });
  }
}

const createEmbeddedRemoteConnection = (): RemoteConnection => {
  const client = createInProcessWorkerClient();
  const queue = new AsyncMessageQueue<ServerMessage>();

  client.onLine(line => {
    try {
      queue.push(line);
    } catch (err) {
      console.error('[perf] embedded worker emitted invalid json', err);
    }
  });
  client.onClose(() => queue.close(new Error('worker disconnected')));
  client.onError(err => queue.close(err));

  return {
    write: async (message: ClientMessage) => {
      client.send(message);
    },
    nextMessage: () => queue.next(),
    close: () => client.close(),
  };
};

const createTcpRemoteConnection = async (host: string, port: number): Promise<RemoteConnection> => {
  const socket = net.createConnection({ host, port });
  socket.setEncoding('utf8');
  socket.on('error', err => {
    console.error('[perf] worker socket error', err);
  });
  const rl = readline.createInterface({ input: socket, crlfDelay: Infinity });
  const messages = readServerMessages(rl);

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

  return {
    write: (message: ClientMessage) => writeSocketMessage(socket, message),
    nextMessage: async () => {
      const { value, done } = await messages.next();
      if (done) throw new Error('worker disconnected');
      return value;
    },
    close: () => {
      rl.close();
      socket.end();
      socket.destroy();
    },
  };
};

const writeSocketMessage = async (socket: net.Socket, message: ClientMessage): Promise<void> => {
  if (!socket.writable) throw new Error('worker connection closed');
  const payload = `${JSON.stringify(message)}\n`;
  if (socket.write(payload)) return;
  await once(socket, 'drain');
};

main().catch(err => {
  console.error('[perf] failed', err);
  process.exit(1);
});
