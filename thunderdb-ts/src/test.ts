import assert from 'node:assert';
import { runLimitStream, fromArray, StreamItem } from './limit-index/limitStream';
import { QuerySpec, LimitEvent, DocId, Score, DocStateDom } from './limit-index/types';

// Cast helpers for branded types
const did = (n: number) => BigInt(n) as DocId;
const score = (n: number) => n as Score;
type DemoDocState = DocStateDom & { value: Score };
const docState = (s: number): DemoDocState => ({ value: score(s) } as DemoDocState);
const getScore = (s: DemoDocState) => s.value;

async function collect(items: StreamItem<DemoDocState>[]): Promise<LimitEvent[]> {
  const out: LimitEvent[] = [];
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
  console.log('Events:', events);   
  // Expect two additions and one removal events
  assert(events.length === 3, 'expected 3 emitted events');
  assert(events[0].addedTo.length === 1 && events[0].docId === did(1));
  assert(events[1].addedTo.length === 1 && events[1].docId === did(2));
  assert(events[2].removedFrom.length === 1 && events[2].docId === did(1));
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
  assert(events[0].evictions.length === 0, 'evictions placeholder should be empty');
}

async function main() {
  await testBasic();
  await testLimitPlaceholder();
  console.log('Tests passed');
}

main().catch(err => {
  console.error(err);
  process.exitCode = 1;
});
