import { DocStateDom, QuerySpec, LimitEvent, DocChange, Score, QueryId } from './types';
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
  emit: (e: LimitEvent) => void
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
        const removedSet = new Set<QueryId>();
        const addedSet = new Set<QueryId>();

        if (old) {
          const score = getScore(old);
          const covering = queries.getQueriesCovering(score);
          queries.removeDocument(score, id);
          covering.forEach(q => removedSet.add(q));
        }
        if (next) {
          const score = getScore(next);
          queries.addDocument(score, id);
          const covering = queries.getQueriesCovering(score);
          covering.forEach(q => addedSet.add(q));
        }

        // Remove intersections so that queries keeping the doc don't double emit
        for (const q of addedSet) {
          if (removedSet.has(q)) {
            addedSet.delete(q);
            removedSet.delete(q);
          }
        }

        if (removedSet.size || addedSet.size) {
          emit({
            docId: id,
            addedTo: Array.from(addedSet),
            removedFrom: Array.from(removedSet),
            evictions: [],
          });
        }
        break;
      }
    }
  }
}

// Helper to build an async iterable from an array (tests / demos)
export async function *fromArray<DocState extends DocStateDom>(items: StreamItem<DocState>[]): AsyncIterable<StreamItem<DocState>> {
  for (const i of items) yield i;
}
