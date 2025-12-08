import assert from 'node:assert';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { runLimitStream, StreamItem } from './limit-index/limitStream';
import { QuerySpec, LimitMatchEvent, DocId, Score, DocStateDom, QueryId, DownstreamEvent, RetrievalEvent } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore } from './docStore';

// Cast helpers for branded types
const did = (n: number) => BigInt(n) as DocId;
const qid = (n: number) => BigInt(n) as QueryId;
const score = (n: number) => n as Score;
type DemoDocState = DocStateDom & { value: Score };
const docState = (s: number): DemoDocState => ({ value: score(s) } as DemoDocState);
const getScore = (s: DemoDocState) => s.value;


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
  await testRetrievalJobWorker();
  await testQueryAddSeedsRetrievals();
  await testGapFillRegistersRetrievals();
  console.log('Tests passed');
}

main().catch(err => {
  console.error(err);
  process.exitCode = 1;
});
