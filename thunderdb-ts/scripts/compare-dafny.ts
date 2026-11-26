import { spawn, spawnSync } from 'node:child_process';
import { performance } from 'node:perf_hooks';
import { runLimitStream, StreamItem } from '../src/limit-index/limitStream';
import { DocId, DocStateDom, DownstreamEvent, QueryId, Score } from '../src/limit-index/types';
import { RetrievalJobWorker } from '../src/retrievalJob';

type State = DocStateDom & { value: Score };
type Input =
  | { kind: 'seed-docs'; docs: Array<{ id: number; score: number }> }
  | { kind: 'query-add'; minScore: number; maxScore: number; limit: number }
  | { kind: 'query-remove'; id: number }
  | { kind: 'doc-change'; id: number; old: number | null; new: number | null };
type TraceEvent =
  | { kind: 'match'; docId: number; old: number | null; new: number | null; matchesOld: number[]; matchesNew: number[]; evictions: number[][] }
  | { kind: 'retrieval'; docs: Array<{ docId: number; score: number; queries: number[] }> };
type TraceRecord = { input: Input; queryId: number; events: TraceEvent[] };

const docId = (value: number): DocId => BigInt(value) as DocId;
const queryId = (value: number): QueryId => BigInt(value) as QueryId;
const score = (value: number): Score => value as Score;
const state = (value: number): State => ({ value: score(value) });
const maybeState = (value: number | null): State | null => value === null ? null : state(value);

function normalize(event: DownstreamEvent<State>): TraceEvent {
  if (event.kind === 'match') {
    return {
      kind: event.kind,
      docId: Number(event.docId),
      old: event.old?.value ?? null,
      new: event.new?.value ?? null,
      matchesOld: event.matchesOld.map(Number),
      matchesNew: event.matchesNew.map(Number),
      evictions: event.evictions.map(([query, doc]) => [Number(query), Number(doc)]),
    };
  }
  return {
    kind: event.kind,
    docs: event.docs.map(doc => ({
      docId: Number(doc.docId),
      score: doc.state.value,
      queries: doc.queries.map(Number),
    })),
  };
}

function canonicalize(event: TraceEvent): TraceEvent {
  if (event.kind === 'match') {
    return {
      ...event,
      matchesOld: [...event.matchesOld].sort((left, right) => left - right),
      matchesNew: [...event.matchesNew].sort((left, right) => left - right),
      evictions: [...event.evictions].sort((left, right) => left[0]! - right[0]! || left[1]! - right[1]!),
    };
  }
  return {
    kind: event.kind,
    docs: event.docs.map(doc => ({ ...doc, queries: [...doc.queries].sort((left, right) => left - right) }))
      .sort((left, right) => left.docId - right.docId || left.score - right.score),
  };
}

async function compare(records: TraceRecord[], validate: boolean): Promise<{ mismatches: number; orderingDifferences: number; durationMs: number }> {
  const docs = new Map<DocId, State>();
  let emitted: DownstreamEvent<State>[] = [];
  const retrieval = new RetrievalJobWorker<State>(
    async ids => new Map(ids.flatMap(id => {
      const value = docs.get(id);
      return value ? [[id, value] as const] : [];
    })),
    event => { if (validate) emitted.push(event); },
  );
  const stream = runLimitStream<State>(value => value.value, event => { if (validate) emitted.push(event); }, { retrievalJob: retrieval });
  stream.next();
  let nextQueryId = 1;
  let mismatches = 0;
  let orderingDifferences = 0;
  const start = performance.now();

  try {
    for (const [index, record] of records.entries()) {
      emitted = [];
      const input = record.input;
      let item: StreamItem<State>;
      let expectedQueryId = 0;
      switch (input.kind) {
        case 'seed-docs': {
          const seeded = input.docs.map(doc => ({ id: docId(doc.id), state: state(doc.score) }));
          for (const doc of seeded) docs.set(doc.id, doc.state);
          item = { kind: 'seed-docs', docs: seeded };
          break;
        }
        case 'query-add':
          expectedQueryId = nextQueryId++;
          item = { kind: 'query-add', spec: { minScore: score(input.minScore), maxScore: score(input.maxScore), limit: BigInt(input.limit) } };
          break;
        case 'query-remove':
          item = { kind: 'query-remove', id: queryId(input.id) };
          break;
        case 'doc-change': {
          const id = docId(input.id);
          const previous = docs.get(id)?.value ?? null;
          if (previous !== input.old) throw new Error(`Step ${index + 1} has inconsistent old document state`);
          const next = maybeState(input.new);
          if (next) docs.set(id, next); else docs.delete(id);
          item = { kind: 'doc-change', change: { id, old: maybeState(input.old), new: next } };
          break;
        }
      }

      stream.next(item);
      await new Promise<void>(resolve => setImmediate(resolve));
      if (!validate) continue;
      const actual = emitted.map(normalize);
      const differentOrder = JSON.stringify(record.events) !== JSON.stringify(actual);
      const differentContent = record.queryId !== expectedQueryId ||
        JSON.stringify(record.events.map(canonicalize)) !== JSON.stringify(actual.map(canonicalize));
      if (differentContent) {
        mismatches += 1;
        if (mismatches <= 5) {
          console.error(`step ${index + 1}: ${JSON.stringify(input)}`);
          console.error(`  Dafny: ${JSON.stringify({ queryId: record.queryId, events: record.events })}`);
          console.error(`  TypeScript: ${JSON.stringify({ queryId: expectedQueryId, events: actual })}`);
        }
      } else if (differentOrder) {
        orderingDifferences += 1;
      }
    }
  } finally {
    stream.next();
    await retrieval.stop();
  }
  return { mismatches, orderingDifferences, durationMs: performance.now() - start };
}

function measureDafny(command: string, args: string[]): Promise<number> {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, { stdio: ['ignore', 'pipe', 'pipe'] });
    const timer = setTimeout(() => child.kill('SIGKILL'), 120_000);
    let remaining = '';
    let errorOutput = '';
    let start: number | undefined;
    let duration: number | undefined;
    let invalidOutput = false;
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', (chunk: string) => {
      remaining += chunk;
      const lines = remaining.split('\n');
      remaining = lines.pop()!;
      for (const line of lines) {
        if (line === 'benchmark-start' && start === undefined) start = performance.now();
        else if (line === 'benchmark-end' && start !== undefined && duration === undefined) duration = performance.now() - start;
        else invalidOutput = true;
      }
    });
    child.stderr.on('data', (chunk: string) => { errorOutput += chunk; });
    child.on('error', error => {
      clearTimeout(timer);
      reject(error);
    });
    child.on('close', code => {
      clearTimeout(timer);
      if (code !== 0 || invalidOutput || remaining !== '' || duration === undefined) {
        reject(new Error(`Dafny benchmark failed (${code}): ${errorOutput || 'invalid timing markers'}`));
      } else {
        resolve(duration);
      }
    });
  });
}

async function main(): Promise<void> {
  const argumentsList = process.argv.slice(2);
  const benchmark = argumentsList[0] === '--benchmark';
  if (benchmark) argumentsList.shift();
  const timedIndex = argumentsList.indexOf('--timed');
  const timedCommand = timedIndex < 0 ? [] : argumentsList.splice(timedIndex + 1);
  if (timedIndex >= 0) argumentsList.pop();
  if (timedIndex >= 0 && (!benchmark || timedCommand.length === 0)) throw new Error('--timed requires --benchmark and a command');
  const [command, ...args] = argumentsList;
  if (!command) throw new Error('Provide the Dafny trace executable and its arguments');
  const result = spawnSync(command, args, { encoding: 'utf8', maxBuffer: 32 * 1024 * 1024, timeout: 120_000 });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`Trace command failed (${result.status}): ${result.stderr}`);
  const output = result.stdout.trim();
  if (!output) throw new Error('Trace contains no inputs');
  const records = output.split('\n').map(line => JSON.parse(line, (_key, value: unknown) => {
    if (typeof value === 'number' && !Number.isSafeInteger(value)) throw new Error('Trace contains an unsafe integer');
    return value;
  }) as TraceRecord);
  if (!records[0]?.input) throw new Error('Trace contains no inputs');
  const comparison = await compare(records, true);
  console.log(`Compared ${records.length} steps: ${comparison.mismatches} content mismatches, ${comparison.orderingDifferences} ordering-only differences`);
  if (comparison.mismatches) {
    process.exitCode = 1;
  } else if (benchmark) {
    const durations: number[] = [];
    for (let run = 0; run < 3; run++) durations.push((await compare(records, false)).durationMs);
    console.log(`TypeScript replay wall time (ms): ${durations.map(duration => duration.toFixed(2)).join(', ')}`);
    if (timedCommand.length) {
      const [executable, ...timedArgs] = timedCommand;
      const dafnyDurations: number[] = [];
      for (let run = 0; run < 3; run++) dafnyDurations.push(await measureDafny(executable!, timedArgs));
      console.log(`Dafny replay wall time (ms): ${dafnyDurations.map(duration => duration.toFixed(2)).join(', ')}`);
    }
  }
}

main().catch(error => {
  console.error(error);
  process.exitCode = 1;
});