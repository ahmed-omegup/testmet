import assert from 'node:assert';
import { runLimitStream, fromArray, StreamItem } from './limit-index/limitStream';
import { QuerySpec, LimitMatchEvent, DocId, Score, DocStateDom } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';

// Cast helpers for branded types
const did = (n: number) => BigInt(n) as DocId;
const score = (n: number) => n as Score;
type DemoDocState = DocStateDom & { value: Score };
const docState = (s: number): DemoDocState => ({ value: score(s) } as DemoDocState);
const getScore = (s: DemoDocState) => s.value;

async function collect(items: StreamItem<DemoDocState>[]): Promise<LimitMatchEvent<DemoDocState>[]> {
  const out: LimitMatchEvent<DemoDocState>[] = [];
  await runLimitStream(fromArray(items), getScore, e => out.push(e));
  return out;
}

// Basic scenario: one query, two docs within range, then remove one.
async function testBasic() {
  const q: QuerySpec = { minScore: score(10), maxScore: score(100), limit: 10n };
  const events = await collect([
    { kind: 'query-add', spec: q },
    { kind: 'doc-change', change: { id: did(1), old: null, new: docState(12) } },
    { kind: 'doc-change', change: { id: did(2), old: null, new: docState(50) } },
    { kind: 'doc-change', change: { id: did(1), old: docState(12), new: null } },
  ]);
  assert(events.length === 3, 'expected 3 emitted events');
  assert(events[0].matchesOld.length === 0 && events[0].matchesNew.length === 1 && events[0].evictions.length === 0);
  assert(events[1].matchesOld.length === 0 && events[1].matchesNew.length === 1 && events[1].evictions.length === 0);
  assert(events[2].matchesOld.length === 1 && events[2].matchesNew.length === 0 && events[2].evictions.length === 0);
}

// Query limit effect: limit=1, adding second doc should still add but eviction list TBD (currently empty)
async function testLimitPlaceholder() {
  const q: QuerySpec = { minScore: score(0), maxScore: score(100), limit: 1n };
  const events = await collect([
    { kind: 'query-add', spec: q },
    { kind: 'doc-change', change: { id: did(10), old: null, new: docState(5) } },
    { kind: 'doc-change', change: { id: did(11), old: null, new: docState(6) } },
  ]);
  assert(events.length === 1, 'expected one event emitted');
  assert(events[0].matchesNew.length === 1 && events[0].matchesOld.length === 0 && events[0].evictions.length === 0);
}

async function testEvictions() {
  const q: QuerySpec = { minScore: score(0), maxScore: score(100), limit: 1n };
  const events = await collect([
    { kind: 'query-add', spec: q },
    { kind: 'doc-change', change: { id: did(1), old: null, new: docState(5) } },
    { kind: 'doc-change', change: { id: did(2), old: null, new: docState(3) } },
  ]);
  assert(events.length === 2, 'expected two events emitted');
  const evictionEvent = events[1];
  assert(evictionEvent.matchesNew.length === 1, 'new doc should match');
  assert(evictionEvent.evictions.length === 1, 'eviction should be reported');
  assert(evictionEvent.evictions[0][1] === did(1), 'older doc should be evicted');
}

async function testRetrievalJobWorker() {
  const worker = new RetrievalJobWorker();
  const docA = did(100);
  const docB = did(200);
  const docC = did(300);
  const docD = did(400);

  const batchOne = worker.register(docA);
  worker.register(docA);
  assert(worker.pendingCount(docA) === 2, 'docA should have two pending registrations');

  assert(!worker.cancel(docA, batchOne + 1n), 'cancel with mismatched batch must be ignored');
  assert(worker.pendingCount(docA) === 2, 'mismatched cancel must not change count');

  assert(worker.cancel(docA, batchOne), 'cancel with matching batch should succeed');
  assert(worker.pendingCount(docA) === 1, 'one registration should remain for docA');

  const firstSnapshot = worker.startNextBatch();
  assert(firstSnapshot && firstSnapshot.batchNumber === batchOne, 'first batch should promote docA');
  assert.deepStrictEqual(firstSnapshot.entries, [[docA, 1]], 'docA should be the only entry in first batch');

  const currentBatchAfterRotate = worker.getCurrentBatchNumber();
  assert(currentBatchAfterRotate === batchOne + 1n, 'batch number should advance after rotation');

  const batchTwo = worker.register(docB);
  assert(batchTwo === currentBatchAfterRotate, 'docB must register against current batch');

  const receiptA = worker.documentReceived(docA);
  assert(receiptA && receiptA.batchNumber === batchOne && receiptA.count === 1, 'docA receipt should drain active batch');
  assert(worker.activeSize() === 0, 'active batch should now be empty');

  const secondSnapshot = worker.startNextBatch();
  assert(secondSnapshot && secondSnapshot.batchNumber === batchTwo, 'second batch should promote docB');
  assert.deepStrictEqual(secondSnapshot.entries, [[docB, 1]], 'docB should be the only entry in second batch');

  const batchThree = worker.getCurrentBatchNumber();
  const regBatchThree = worker.register(docC);
  assert(regBatchThree === batchThree, 'docC should see the latest batch number');

  let threw = false;
  try {
    worker.startNextBatch();
  } catch (err) {
    threw = true;
  }
  assert(threw, 'cannot start next batch while previous one is active');

  const receiptB = worker.documentReceived(docB);
  assert(receiptB && receiptB.batchNumber === batchTwo, 'docB receipt should be associated to batch two');

  const thirdSnapshot = worker.startNextBatch();
  assert(thirdSnapshot && thirdSnapshot.batchNumber === batchThree, 'docC batch should promote once previous completes');

  const receiptC = worker.documentReceived(docC);
  assert(receiptC && receiptC.batchNumber === batchThree, 'docC receipt should reference batch three');

  const batchFour = worker.getCurrentBatchNumber();
  const regBatchFour = worker.register(docD);
  assert(regBatchFour === batchFour, 'docD registration should reference new batch');

  const pendingReceipt = worker.documentReceived(docD);
  assert(pendingReceipt && pendingReceipt.batchNumber === batchFour, 'docD removal should happen while pending');
  assert(worker.pendingSize() === 0, 'pending batch should be empty after docD removal');

  assert(worker.documentReceived(did(999)) === null, 'unknown doc receipts should noop');
  assert(!worker.cancel(docB, batchTwo), 'cancelling using stale batch number should be ignored');
}

async function main() {
  await testBasic();
  await testLimitPlaceholder();
  await testEvictions();
  await testRetrievalJobWorker();
  console.log('Tests passed');
}

main().catch(err => {
  console.error(err);
  process.exitCode = 1;
});
