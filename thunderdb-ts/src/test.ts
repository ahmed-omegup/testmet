import assert from 'node:assert';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { runLimitStream, StreamItem } from './limit-index/limitStream';
import { QuerySpec, LimitMatchEvent, DocId, Score, DocStateDom, QueryId, DownstreamEvent, RetrievalEvent } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore } from './docStore';
import { DynamicRangeQueries } from './limit-index/LimitQueries';

// Cast helpers for branded types
const did = (n: number) => BigInt(n) as DocId;
const qid = (n: number) => BigInt(n) as QueryId;
const score = (n: number) => n as Score;
type DemoDocState = DocStateDom & { value: Score };
const docState = (s: number): DemoDocState => ({ value: score(s) } as DemoDocState);
const getScore = (s: DemoDocState) => s.value;

function testDifferenceRespectsLowerBound() {
  const queries = new DynamicRangeQueries();
  queries.seedDocuments([{ id: did(1), score: score(41) }]);
  const id = queries.addQuery(score(40), 2n, score(60));
  assert.deepStrictEqual(queries.getQueriesCoveringButNot(score(41), did(1), score(16), did(1)), [id]);
  assert.deepStrictEqual(queries.getQueriesCoveringButNot(score(16), did(1), score(41), did(1)), []);
}

function testQueryDifferenceMatchesSeparateLookups() {
  const queries = new DynamicRangeQueries();
  queries.seedDocuments([
    { id: did(0), score: score(1) },
    { id: did(1), score: score(2) },
    { id: did(2), score: score(2) },
    { id: did(3), score: score(4) },
  ]);
  for (const minimum of [0, 2, 4]) {
    for (const maximum of [2, 4, 6]) {
      if (minimum <= maximum) {
        for (const limit of [0n, 1n, 3n]) queries.addQuery(score(minimum), limit, score(maximum));
      }
    }
  }
  const ordered = (ids: QueryId[]) => ids.map(String).sort();
  for (const included of [0, 1, 2, 3, 4, 5]) {
    for (const excluded of [0, 1, 2, 3, 4, 5]) {
      for (const includeId of [null, did(0), did(2), did(4)]) {
        for (const excludeId of [null, did(0), did(2), did(4)]) {
          const exclude = new Set(queries.getQueriesCovering(score(excluded), excludeId));
          const expected = queries.getQueriesCovering(score(included), includeId).filter(query => !exclude.has(query));
          const actual = queries.getQueriesCoveringButNot(score(included), includeId, score(excluded), excludeId);
          assert.deepStrictEqual(ordered(actual), ordered(expected), `include=${included}/${includeId} exclude=${excluded}/${excludeId}`);
        }
      }
    }
  }
}

function testScoreChangePreservesSharedMatches() {
  const events = collect([
    { kind: 'seed-docs', docs: [{ id: did(1), state: docState(10) }] },
    { kind: 'query-add', spec: { minScore: score(0), maxScore: score(100), limit: 2n } },
    { kind: 'doc-change', change: { id: did(1), old: docState(10), new: docState(20) } },
  ]);
  assert.strictEqual(events.length, 1);
  assert.deepStrictEqual(events[0]!.matchesOld, [qid(1)]);
  assert.deepStrictEqual(events[0]!.matchesNew, [qid(1)]);
}

function testUnmatchedSameScoreIsSilent() {
  const events = collect([
    { kind: 'seed-docs', docs: [{ id: did(1), state: docState(10) }] },
    { kind: 'query-add', spec: { minScore: score(20), maxScore: score(100), limit: 2n } },
    { kind: 'doc-change', change: { id: did(1), old: docState(10), new: docState(10) } },
  ]);
  assert.strictEqual(events.length, 0);
}

function testZeroDocumentGapAndEviction() {
  const queries = new DynamicRangeQueries();
  queries.seedDocuments([{ id: did(0), score: score(20) }, { id: did(1), score: score(10) }]);
  const query = queries.addQuery(score(0), 1n, score(100));
  queries.removeDocument(score(10), did(1));
  assert.strictEqual(queries.fillGap(query), did(0));

  const events = collect([
    { kind: 'seed-docs', docs: [{ id: did(0), state: docState(10) }] },
    { kind: 'query-add', spec: { minScore: score(0), maxScore: score(100), limit: 1n } },
    { kind: 'doc-change', change: { id: did(1), old: null, new: docState(5) } },
  ]);
  assert.deepStrictEqual(events[0]!.evictions, [[qid(1), did(0)]]);
}

async function testZeroDocumentGapRetrieval() {
  const docs = new Map<DocId, DemoDocState>([[did(0), docState(20)], [did(1), docState(10)]]);
  const events: RetrievalEvent<DemoDocState>[] = [];
  const worker = new RetrievalJobWorker<DemoDocState>(
    async ids => new Map(ids.flatMap(id => {
      const value = docs.get(id);
      return value ? [[id, value] as const] : [];
    })),
    event => events.push(event),
  );
  const stream = runLimitStream(getScore, () => {}, { retrievalJob: worker });
  try {
    stream.next();
    stream.next({ kind: 'seed-docs', docs: [...docs].map(([id, value]) => ({ id, state: value })) });
    stream.next({ kind: 'query-add', spec: { minScore: score(0), maxScore: score(100), limit: 1n } });
    await new Promise<void>(resolve => setImmediate(resolve));
    docs.delete(did(1));
    stream.next({ kind: 'doc-change', change: { id: did(1), old: docState(10), new: null } });
    await new Promise<void>(resolve => setImmediate(resolve));
    assert(events.some(event => event.docs.some(doc => doc.docId === did(0) && doc.queries.includes(qid(1)))));
  } finally {
    stream.next();
    await worker.stop();
  }
}

function collect(items: StreamItem<DemoDocState>[]): LimitMatchEvent<DemoDocState>[] {
  const out: LimitMatchEvent<DemoDocState>[] = [];
  const gen = runLimitStream(getScore, e => {
    if (e.kind === 'match') out.push(e);
  });
  gen.next()
  for (const item of items) {
    gen.next(item);
  }
  gen.next()
  return out;
}

// Basic scenario: one query, two docs within range, then remove one.
function testBasic() {
  const q: QuerySpec = { minScore: score(10), maxScore: score(100), limit: 10n };
  const events = collect([
    { kind: 'query-add', spec: q },
    { kind: 'doc-change', change: { id: did(1), old: null, new: docState(12) } },
    { kind: 'doc-change', change: { id: did(2), old: null, new: docState(50) } },
    { kind: 'doc-change', change: { id: did(1), old: docState(12), new: null } },
  ]);
  assert(events.length === 3, 'expected 3 emitted events');
  assert(events[0]!.matchesOld.length === 0 && events[0]!.matchesNew.length === 1 && events[0]!.evictions.length === 0);
  assert(events[1]!.matchesOld.length === 0 && events[1]!.matchesNew.length === 1 && events[1]!.evictions.length === 0);
  assert(events[2]!.matchesOld.length === 1 && events[2]!.matchesNew.length === 0 && events[2]!.evictions.length === 0);
}

// Query limit effect: limit=1, adding second doc should still add but eviction list TBD (currently empty)
function testLimitPlaceholder() {
  const q: QuerySpec = { minScore: score(0), maxScore: score(100), limit: 1n };
  const events = collect([
    { kind: 'query-add', spec: q },
    { kind: 'doc-change', change: { id: did(10), old: null, new: docState(5) } },
    { kind: 'doc-change', change: { id: did(11), old: null, new: docState(6) } },
  ]);
  assert(events.length === 1, 'expected one event emitted');
  assert(events[0]!.matchesNew.length === 1 && events[0]!.matchesOld.length === 0 && events[0]!.evictions.length === 0);
}

function testEvictions() {
  const q: QuerySpec = { minScore: score(0), maxScore: score(100), limit: 1n };
  const events = collect([
    { kind: 'query-add', spec: q },
    { kind: 'doc-change', change: { id: did(1), old: null, new: docState(5) } },
    { kind: 'doc-change', change: { id: did(2), old: null, new: docState(3) } },
  ]);
  assert(events.length === 2, 'expected two events emitted');
  const evictionEvent = events[1]!;
  assert(evictionEvent.matchesNew.length === 1, 'new doc should match');
  assert(evictionEvent.evictions.length === 1, 'eviction should be reported');
  assert(evictionEvent.evictions[0]![1] === did(1), 'older doc should be evicted');
}

async function waitFor(condition: () => boolean, timeoutMs = 200): Promise<void> {
  const start = Date.now();
  while (Date.now() - start < timeoutMs) {
    if (condition()) return;
    await new Promise(resolve => setTimeout(resolve, 5));
  }
  throw new Error('Timed out waiting for condition');
}

async function testRetrievalJobWorker() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'thunderdb-rj-'));
  const store = new LmdbDocStore<DemoDocState>(dir);
  const retrievalEvents: RetrievalEvent<DemoDocState>[] = [];
  const worker = new RetrievalJobWorker<DemoDocState>(
    ids => store.getMany(ids),
    e => retrievalEvents.push(e),
    { batchIntervalMs: 1 }
  );

  store.put(did(100), docState(5));
  worker.register(did(100), qid(1));
  await waitFor(() => retrievalEvents.length === 1);
  assert(retrievalEvents[0]!.docs.length === 1);
  assert(retrievalEvents[0]!.docs[0]!.docId === did(100));
  assert(retrievalEvents[0]!.docs[0]!.queries.includes(qid(1)));

  store.put(did(200), docState(7));
  const batchTwo = worker.register(did(200), qid(2));
  assert(!worker.cancel(did(200), qid(2), batchTwo + 1n), 'mismatched batch should not cancel');
  assert(worker.cancel(did(200), qid(2), batchTwo), 'matching batch cancels');
  await new Promise(resolve => setTimeout(resolve, 15));
  assert(retrievalEvents.length === 1, 'canceled doc should not emit');

  store.put(did(300), docState(11));
  worker.register(did(300), qid(3));
  await waitFor(() => retrievalEvents.length === 2);
  assert(retrievalEvents[1]!.docs.some(doc => doc.queries.includes(qid(3))));
  await worker.stop();
}

async function testQueryAddSeedsRetrievals() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'thunderdb-stream-'));
  const store = new LmdbDocStore<DemoDocState>(dir);
  const events: DownstreamEvent<DemoDocState>[] = [];
  const worker = new RetrievalJobWorker<DemoDocState>(
    ids => store.getMany(ids),
    e => events.push(e),
    { batchIntervalMs: 1 }
  );
  const q: QuerySpec = { minScore: score(0), maxScore: score(100), limit: 2n };
  const items: StreamItem<DemoDocState>[] = [
    { kind: 'doc-change', change: { id: did(1), old: null, new: docState(10) } },
    { kind: 'doc-change', change: { id: did(2), old: null, new: docState(20) } },
    { kind: 'query-add', spec: q },
  ];
  const gen = runLimitStream(getScore, e => events.push(e), { retrievalJob: worker, docStore: store });
  gen.next()
  for (const item of items) {
    gen.next(item);
  }
  gen.next()
  await waitFor(() => events.some(evt => evt.kind === 'retrieval' && (evt as RetrievalEvent<DemoDocState>).docs.length >= 2), 500);
  const retrievalEvents = events.filter(evt => evt.kind === 'retrieval') as RetrievalEvent<DemoDocState>[];
  const docIds = retrievalEvents.flatMap(evt => evt.docs.map(doc => doc.docId.toString()));
  assert(docIds.includes(did(1).toString()));
  assert(docIds.includes(did(2).toString()));
  await worker.stop();
}

async function testGapFillRegistersRetrievals() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'thunderdb-gap-'));
  const store = new LmdbDocStore<DemoDocState>(dir);
  const events: DownstreamEvent<DemoDocState>[] = [];
  const worker = new RetrievalJobWorker<DemoDocState>(
    ids => store.getMany(ids),
    e => events.push(e),
    { batchIntervalMs: 1 }
  );
  const q: QuerySpec = { minScore: score(0), maxScore: score(100), limit: 2n };
  const items: StreamItem<DemoDocState>[] = [
    { kind: 'doc-change', change: { id: did(1), old: null, new: docState(10) } },
    { kind: 'doc-change', change: { id: did(2), old: null, new: docState(20) } },
    { kind: 'doc-change', change: { id: did(3), old: null, new: docState(30) } },
    { kind: 'query-add', spec: q },
    { kind: 'doc-change', change: { id: did(2), old: docState(20), new: null } },
  ];
  const gen = runLimitStream(getScore, e => events.push(e), { retrievalJob: worker, docStore: store });
  gen.next()
  for (const item of items) {
    gen.next(item);
  }
  gen.next()
  await waitFor(
    () => events.some(evt => evt.kind === 'retrieval' && (evt as RetrievalEvent<DemoDocState>).docs.some(doc => doc.docId === did(3))),
    500
  );
  const retrievalEvents = events.filter(evt => evt.kind === 'retrieval') as RetrievalEvent<DemoDocState>[];
  const gapEvent = retrievalEvents.find(evt => evt.docs.some(doc => doc.docId === did(3)));
  assert(gapEvent, 'expected retrieval event for replacement doc');
  assert(gapEvent.docs.some(doc => doc.docId === did(3) && doc.queries.includes(qid(1))), 'replacement doc should target query');
  await worker.stop();
}

async function main() {
  testDifferenceRespectsLowerBound();
  testQueryDifferenceMatchesSeparateLookups();
  testScoreChangePreservesSharedMatches();
  testUnmatchedSameScoreIsSilent();
  testZeroDocumentGapAndEviction();
  await testZeroDocumentGapRetrieval();
  testBasic();
  testLimitPlaceholder();
  testEvictions();
  await testRetrievalJobWorker();
  await testQueryAddSeedsRetrievals();
  await testGapFillRegistersRetrievals();
  console.log('Tests passed');
}

main().catch(err => {
  console.error(err);
  process.exitCode = 1;
});
