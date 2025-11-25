import { DocStateDom, QuerySpec, LimitMatchEvent, DocChange, Score, QueryId, DocId, DownstreamEvent } from './types';
import { DynamicRangeQueries } from './LimitQueries';
import { RetrievalJobWorker } from '../retrievalJob';
import { LmdbDocStore } from '../docStore';

// Event union the operator consumes
export type StreamItem<DocState extends DocStateDom> =
  | { kind: 'doc-change'; change: DocChange<DocState> }
  | { kind: 'query-add'; spec: QuerySpec }
  | { kind: 'query-remove'; id: QueryId };

export interface LimitStreamOptions<DocState extends DocStateDom> {
  retrievalJob?: RetrievalJobWorker<DocState>;
  docStore?: LmdbDocStore<DocState>;
}

// Stateless limit stream operator (stores only per-query counts already tracked in DynamicRangeQueries)
export async function runLimitStream<DocState extends DocStateDom>(
  items: AsyncIterable<StreamItem<DocState>>,
  getScore: (state: DocState) => Score,
  emit: (e: DownstreamEvent<DocState>) => void,
  options: LimitStreamOptions<DocState> = {}
): Promise<void> {
  const queries = new DynamicRangeQueries();
  const retrievalJob = options.retrievalJob;
  const docStore = options.docStore;
  for await (const item of items) {
    switch (item.kind) {
      case 'query-add': {
        const id = queries.addQuery(item.spec.minScore, item.spec.limit, item.spec.maxScore);
        if (retrievalJob) {
          const seedDocs = queries.getDocsForQuery(id);
          for (const docId of seedDocs) {
            retrievalJob.register(docId, id);
          }
        }
        break;
      }
      case 'query-remove': {
        queries.removeQuery(item.id);
        break;
      }
      case 'doc-change': {
        const { id, old, new: next } = item.change;
        const oldScore = old ? getScore(old) : null;
        const newScore = next ? getScore(next) : null;

        const notifyRetrieval = async () => {
          if (retrievalJob) {
            await retrievalJob.resolveDoc(id);
          }
        };

        if (docStore) {
          if (next) docStore.put(id, next);
          else docStore.delete(id);
        }

        const matchesOld: QueryId[] = [];
        const matchesNew: QueryId[] = [];
        const evictions: Array<[QueryId, DocId]> = [];

        if (oldScore !== null) {
          if (next && newScore !== null && oldScore === newScore) {
            const covering = queries.getQueriesCovering(oldScore);
            emit({
              kind: 'match',
              docId: id,
              old,
              new: next,
              matchesOld: [...covering],
              matchesNew: [...covering],
              evictions: [],
            });
            await notifyRetrieval();
            break;
          }
          const removed = queries.removeDocument(oldScore, id);
          matchesOld.push(...removed);
        }
        if (newScore !== null && next) {
          const { matched, evicted } = queries.addDocument(newScore, id);
          matchesNew.push(...matched);
          evictions.push(...evicted);
        }

        if (matchesOld.length || matchesNew.length || evictions.length) {
          emit({
            kind: 'match',
            docId: id,
            old,
            new: next,
            matchesOld,
            matchesNew,
            evictions,
          });
        }
        await notifyRetrieval();
        break;
      }
    }
  }
}

// Helper to build an async iterable from an array (tests / demos)
export async function* fromArray<DocState extends DocStateDom>(items: StreamItem<DocState>[]): AsyncIterable<StreamItem<DocState>> {
  for (const i of items) yield i;
}
