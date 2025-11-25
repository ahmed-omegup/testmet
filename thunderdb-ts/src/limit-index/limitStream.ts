import { DocStateDom, QuerySpec, LimitMatchEvent, DocChange, Score, QueryId, DocId } from './types';
import { DynamicRangeQueries } from './LimitQueries';

// Event union the operator consumes
export type StreamItem<DocState extends DocStateDom> =
  | { kind: 'doc-change'; change: DocChange<DocState> }
  | { kind: 'query-add'; spec: QuerySpec }
  | { kind: 'query-remove'; id: QueryId };

// Stateless limit stream operator (stores only per-query counts already tracked in DynamicRangeQueries)
export async function runLimitStream<DocState extends DocStateDom>(
  items: AsyncIterable<StreamItem<DocState>>,
  getScore: (state: DocState) => Score,
  emit: (e: LimitMatchEvent<DocState>) => void
): Promise<void> {
  const queries = new DynamicRangeQueries();
  for await (const item of items) {
    switch (item.kind) {
      case 'query-add': {
        const id = queries.addQuery(item.spec.minScore, item.spec.limit, item.spec.maxScore);
        break;
      }
      case 'query-remove': {
        queries.removeQuery(item.id);
        break;
      }
      case 'doc-change': {
        const { id, old, new: next } = item.change;

        const matchesOld: QueryId[] = [];
        const matchesNew: QueryId[] = [];
        const evictions: Array<[QueryId, DocId]> = [];

        if (old) {
          const oldScore = getScore(old);
          if (next && oldScore === getScore(next)) {
            const covering = queries.getQueriesCovering(oldScore);
            emit({
              docId: id,
              old,
              new: next,
              matchesOld: [...covering],
              matchesNew: [...covering],
              evictions: [],
            });
            break;
          }
          const removed = queries.removeDocument(oldScore, id);
          matchesOld.push(...removed);
        }
        if (next) {
          const newScore = getScore(next);
          const { matched, evicted } = queries.addDocument(newScore, id);
          matchesNew.push(...matched);
          evictions.push(...evicted);
        }

        if (matchesOld.length || matchesNew.length || evictions.length) {
          emit({
            docId: id,
            old,
            new: next,
            matchesOld,
            matchesNew,
            evictions,
          });
        }
        break;
      }
    }
  }
}

// Helper to build an async iterable from an array (tests / demos)
export async function* fromArray<DocState extends DocStateDom>(items: StreamItem<DocState>[]): AsyncIterable<StreamItem<DocState>> {
  for (const i of items) yield i;
}
