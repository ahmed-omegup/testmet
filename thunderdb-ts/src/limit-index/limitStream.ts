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


const handleChange = <DocState extends DocStateDom>(
  item: DocChange<DocState>,
  queries: DynamicRangeQueries,
  getScore: (state: DocState) => Score,
  emit: (e: DownstreamEvent<DocState>) => void,
  options: LimitStreamOptions<DocState> = {}
) => {
  const { id, old, new: next } = item;
  const oldScore = old ? getScore(old) : null;
  const retrievalJob = options.retrievalJob;
  const docStore = options.docStore;

  const notifyRetrieval = () => {
    if (retrievalJob) {
      retrievalJob.resolveDoc(id);
    }
  };

  if (docStore) {
    if (next) docStore.put(id, next);
    else docStore.delete(id);
  }

  const matchesOld: QueryId[] = [];
  const matchesNew: QueryId[] = [];
  const evictions: Array<[QueryId, DocId]> = [];
  const blockedCandidates: QueryId[] = [];

  if (oldScore !== null) {
    if (next && oldScore === getScore(next)) {
      const covering = queries.getQueriesCovering(oldScore);
      emit({
        kind: 'match',
        docId: id,
        old,
        new: next,
        matchesOld: covering,
        matchesNew: covering,
        evictions: [],
      });
      notifyRetrieval();
      return;
    }
    const removed = queries.removeDocument(oldScore, id);
    matchesOld.push(...removed);
  }
  if (next) {
    const { matched, blocked } = queries.addDocument(getScore(next), id);
    matchesNew.push(...matched);
    blockedCandidates.push(...blocked);
  }

  const matchesOldSet = new Set(matchesOld);
  const matchesNewSet = new Set(matchesNew);

  // Gap filling: queries that lost this doc should pull the next best candidate.
  const lostQueries = new Set<QueryId>();
  for (const q of matchesOld) {
    if (!matchesNewSet.has(q)) lostQueries.add(q);
  }
  for (const q of lostQueries) {
    const replacement = queries.fillGap(q);
    if (replacement && retrievalJob) {
      retrievalJob.register(replacement, q);
    }
  }

  // Evictions: queries that only gained this doc and are already full.
  const overflowQueries = new Set<QueryId>();
  for (const q of blockedCandidates) {
    if (!matchesOldSet.has(q)) overflowQueries.add(q);
  }
  for (const q of overflowQueries) {
    const evictedDoc = queries.pickOverflowDoc(q);
    if (evictedDoc) {
      evictions.push([q, evictedDoc]);
    }
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
  notifyRetrieval();
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
          if (BigInt(seedDocs.length) !== queries.getQueryInfo(id)?.currentMatches) throw new Error('Inconsistent query state detected when adding query');
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
        handleChange(item.change, queries, getScore, emit, options); 
        break;
      }
    }
  }
}

// Helper to build an async iterable from an array (tests / demos)
export async function* fromIterable<DocState extends DocStateDom>(items: Iterable<StreamItem<DocState>>): AsyncIterable<StreamItem<DocState>> {
  for (const i of items) yield i;
}
