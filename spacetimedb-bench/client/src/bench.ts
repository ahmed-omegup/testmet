import { performance } from 'node:perf_hooks';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { inspect } from 'node:util';
import { DbConnection, type SubscriptionHandle } from './module_bindings/index.js';

type Config = {
  seed: number;
  documents: number;
  customers: number;
  duration: number;
  updateRate: number;
  insertRate: number;
  deleteRate: number;
  density: number;
  seedBatch: number;
  queryLimit: number;
  queryBatch: number;
  settleMs: number;
  serverHttpUrl: string;
  serverWsUrl: string;
  databaseName: string;
  timeoutMs: number;
};

const workspaceRoot = path.resolve(path.dirname(new URL(import.meta.url).pathname), '..', '..');
const configDir = path.resolve(workspaceRoot);

const prng = (seed: number) => {
  let state = seed % 0x7fffffff;
  if (state <= 0) state += 0x7fffffff;
  return () => {
    state = (state * 48271) % 0x7fffffff;
    return state / 0x7fffffff;
  };
};

const parseNumber = (name: string, fallback: number) => Number(process.env[name] ?? fallback);

const loadDatabaseName = async (): Promise<string> => {
  if (process.env.STDB_DATABASE_NAME) return process.env.STDB_DATABASE_NAME;
  const localConfigPath = path.resolve(configDir, 'spacetime.local.json');
  const raw = await readFile(localConfigPath, 'utf8');
  const parsed = JSON.parse(raw) as { database?: string };
  if (!parsed.database) {
    throw new Error(`missing database name in ${localConfigPath}`);
  }
  return parsed.database;
};

const makeConfig = async (): Promise<Config & {
  range: number;
  updatesPerTick: number;
  insertsPerTick: number;
  deletesPerTick: number;
}> => {
  const databaseName = await loadDatabaseName();
  const documents = parseNumber('PERF_DOCUMENTS', 10000);
  const density = parseNumber('PERF_DENSITY', 10);
  const duration = parseNumber('PERF_DURATION', 10);
  const updateRate = parseNumber('PERF_UPDATE_RATE', 0.05);
  const insertRate = parseNumber('PERF_INSERT_RATE', 0.01);
  const deleteRate = parseNumber('PERF_DELETE_RATE', 0.01);
  const range = Math.max(1, Math.floor(documents / Math.max(1, density)));
  return {
    seed: parseNumber('PERF_SEED', 42),
    documents,
    customers: parseNumber('PERF_CUSTOMERS', 1000),
    duration,
    updateRate,
    insertRate,
    deleteRate,
    density,
    seedBatch: parseNumber('PERF_SEED_BATCH', 2048),
    queryLimit: parseNumber('PERF_QUERY_LIMIT', 50),
    queryBatch: parseNumber('PERF_QUERY_BATCH', 128),
    settleMs: parseNumber('PERF_SETTLE_MS', 50),
    serverHttpUrl: process.env.STDB_HTTP_URL ?? 'http://127.0.0.1:3001',
    serverWsUrl: process.env.STDB_WS_URL ?? 'ws://127.0.0.1:3001',
    databaseName,
    timeoutMs: parseNumber('PERF_TIMEOUT_MS', 300000),
    range,
    updatesPerTick: Math.max(1, Math.floor(documents * updateRate)),
    insertsPerTick: Math.max(0, Math.floor(documents * insertRate)),
    deletesPerTick: Math.max(0, Math.floor(documents * deleteRate)),
  };
};

const customerRange = (rand: () => number, range: number): [number, number] => {
  const width = 100 + Math.min(rand() * 500, 500);
  const start = rand() * Math.max(1, range - width);
  return [Math.floor(start), Math.floor(start + width)];
};

const sleep = (ms: number) => new Promise<void>(resolve => setTimeout(resolve, ms));

const createConnection = async (config: Config): Promise<DbConnection> => {
  return await new Promise<DbConnection>((resolve, reject) => {
    const connection = DbConnection.builder()
      .withUri(config.serverWsUrl)
      .withDatabaseName(config.databaseName)
      .withConfirmedReads(false)
      .onConnect(conn => resolve(conn))
      .onConnectError((_ctx, error) => {
        reject(error instanceof Error ? error : new Error(String(error)));
      })
      .onDisconnect((_ctx, error) => {
        if (error) {
          reject(error instanceof Error ? error : new Error(String(error)));
        }
      })
      .build();

    void connection;
  });
};

const seedDocuments = async (
  rand: () => number,
  config: Awaited<ReturnType<typeof makeConfig>>,
  connection: DbConnection,
): Promise<void> => {
  await connection.reducers.clearAll({});

  for (let start = 0; start < config.documents; start += config.seedBatch) {
    const ids: bigint[] = [];
    const scores: number[] = [];
    const timestamps: number[] = [];
    const end = Math.min(start + config.seedBatch, config.documents);
    for (let id = start; id < end; id += 1) {
      ids.push(BigInt(id));
      scores.push(Math.floor(rand() * config.range));
      timestamps.push(id);
    }
    await connection.reducers.seedBatch({ ids, scores, timestamps });
  }
};

const registerQueries = async (
  rand: () => number,
  config: Awaited<ReturnType<typeof makeConfig>>,
  connection: DbConnection,
): Promise<SubscriptionHandle[]> => {
  const pending: Promise<void>[] = [];
  const handles: SubscriptionHandle[] = [];
  for (let start = 0; start < config.customers; start += config.queryBatch) {
    const queries: string[] = [];
    const end = Math.min(start + config.queryBatch, config.customers);
    for (let id = start; id < end; id += 1) {
      const [minScore, maxScore] = customerRange(rand, config.range);
      queries.push(`SELECT * FROM doc WHERE score >= ${minScore} AND score <= ${maxScore}`);
    }
    pending.push(new Promise<void>((resolve, reject) => {
      const handle = connection.subscriptionBuilder()
        .onApplied(() => resolve())
        .onError((ctx: any) => {
          const detail = ctx?.event?.error ?? ctx?.event ?? ctx;
          const error = detail instanceof Error
            ? detail
            : new Error(`subscription error: ${inspect(detail, { depth: 4, breakLength: 120 })}`);
          reject(error);
        })
        .subscribe(queries);
      handles.push(handle);
    }));
  }
  const timeout = new Promise<never>((_, reject) => {
    setTimeout(() => reject(new Error(`timeout registering ${config.customers} queries`)), config.timeoutMs);
  });
  await Promise.race([Promise.all(pending), timeout]);
  return handles;
};

const runTick = async (
  rand: () => number,
  config: Awaited<ReturnType<typeof makeConfig>>,
  connection: DbConnection,
  docOrder: number[],
  docState: Map<number, number>,
  nextDocIdRef: { value: number },
  tick: number,
): Promise<void> => {
  const updateIds: bigint[] = [];
  const updateScores: number[] = [];
  const updateTimestamps: number[] = [];
  const insertIds: bigint[] = [];
  const insertScores: number[] = [];
  const insertTimestamps: number[] = [];
  const deleteIds: bigint[] = [];

  const pickDoc = () => {
    if (docOrder.length === 0) return null;
    const index = Math.floor(rand() * docOrder.length);
    return docOrder[index] ?? null;
  };

  for (let index = 0; index < config.updatesPerTick; index += 1) {
    const id = pickDoc();
    if (id === null) break;
    const score = Math.floor(rand() * config.range);
    docState.set(id, score);
    updateIds.push(BigInt(id));
    updateScores.push(score);
    updateTimestamps.push(tick);
  }

  for (let index = 0; index < config.insertsPerTick; index += 1) {
    const id = nextDocIdRef.value;
    nextDocIdRef.value += 1;
    const score = Math.floor(rand() * config.range);
    docOrder.push(id);
    docState.set(id, score);
    insertIds.push(BigInt(id));
    insertScores.push(score);
    insertTimestamps.push(tick);
  }

  for (let index = 0; index < config.deletesPerTick; index += 1) {
    const id = pickDoc();
    if (id === null) break;
    const orderIndex = docOrder.indexOf(id);
    if (orderIndex === -1) continue;
    docOrder.splice(orderIndex, 1);
    docState.delete(id);
    deleteIds.push(BigInt(id));
  }

  await connection.reducers.applyTick({
    updateIds,
    updateScores,
    updateTimestamps,
    insertIds,
    insertScores,
    insertTimestamps,
    deleteIds,
  });
};

async function main(): Promise<void> {
  const config = await makeConfig();
  console.log('[stdb] configuration:', config);

  const seedRand = prng(config.seed);
  const customerRand = prng(config.seed);
  const updateRand = prng(config.seed);
  const connection = await createConnection(config);

  let lastCacheEventAt = performance.now();
  connection.db.doc.onInsert(() => {
    lastCacheEventAt = performance.now();
  });
  connection.db.doc.onDelete(() => {
    lastCacheEventAt = performance.now();
  });
  connection.db.doc.onUpdate(() => {
    lastCacheEventAt = performance.now();
  });

  const seedStart = performance.now();
  await seedDocuments(seedRand, config, connection);
  const seedDuration = performance.now() - seedStart;
  console.log(`[stdb] seeded ${config.documents} documents in ${seedDuration.toFixed(2)} ms`);

  const customerStart = performance.now();
  const handles = await registerQueries(customerRand, config, connection);
  const customerDuration = performance.now() - customerStart;
  console.log(`[stdb] registered ${config.customers} active queries on one connection in ${customerDuration.toFixed(2)} ms`);

  const docOrder = Array.from({ length: config.documents }, (_, id) => id);
  const docState = new Map<number, number>();
  const nextDocIdRef = { value: config.documents };
  for (const id of docOrder) {
    docState.set(id, 0);
  }

  const updatesStart = performance.now();
  for (let tick = 0; tick < config.duration; tick += 1) {
    await runTick(updateRand, config, connection, docOrder, docState, nextDocIdRef, tick);
    if ((tick + 1) % Math.max(1, Math.floor(config.duration / 5)) === 0 || tick + 1 === config.duration) {
      console.log(`[stdb] tick ${tick + 1}/${config.duration} committed`);
    }
  }
  while (performance.now() - lastCacheEventAt < config.settleMs) {
    await sleep(config.settleMs);
  }
  const updatesDuration = performance.now() - updatesStart;
  const eventsPerTick = config.updatesPerTick + config.insertsPerTick + config.deletesPerTick;
  const totalEvents = config.duration * eventsPerTick;

  console.log(`\n[stdb] summary`);
  console.log(`  seed duration: ${seedDuration.toFixed(2)} ms`);
  console.log(`  query registration duration: ${customerDuration.toFixed(2)} ms`);
  console.log(`  event processing + settle duration: ${updatesDuration.toFixed(2)} ms (~${(totalEvents / (updatesDuration / 1000)).toFixed(2)} events/s)`);
  console.log(`  processed events: ${totalEvents}`);
  void handles;
  connection.disconnect();
}

main().catch(error => {
  console.error('[stdb] failed', error);
  process.exitCode = 1;
});