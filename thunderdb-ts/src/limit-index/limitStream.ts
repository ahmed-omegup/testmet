import { DocStateDom, QuerySpec, LimitMatchEvent, DocChange, Score, QueryId, DocId } from './types';
import { DynamicRangeQueries } from './LimitQueries';
import { RetrievalJobWorker } from '../retrievalJob';
import { LmdbDocStore } from '../docStore';

// Event union the operator consumes
export type StreamItem<DocState extends DocStateDom> =
  | { kind: 'doc-change'; change: DocChange<DocState> }
  | { kind: 'query-add'; spec: QuerySpec }
  | { kind: 'query-remove'; id: QueryId }
  | { kind: 'seed-docs'; docs: Array<{ id: DocId; state: DocState }> };

export interface LimitStreamOptions<DocState extends DocStateDom> {
  retrievalJob: RetrievalJobWorker<DocState>;
  docStore?: LmdbDocStore<DocState>;
}

const DEBUG_QUERY_ID = process.env.LIMIT_DEBUG_QUERY ? (BigInt(process.env.LIMIT_DEBUG_QUERY) as QueryId) : null;


const handleChange = <DocState extends DocStateDom>(
  item: DocChange<DocState>,
  queries: DynamicRangeQueries,
  getScore: (state: DocState) => Score,
  emit: (e: LimitMatchEvent<DocState>) => void,
  options: LimitStreamOptions<DocState>
) => {
  const { id, old, new: next } = item;
  const oldScore = old ? getScore(old) : null;
  const retrievalJob = options.retrievalJob;

  const notifyRetrieval = () => {
    retrievalJob.resolveDoc(id);
  };

  const matchesOld: QueryId[] = [];
  const matchesNew: QueryId[] = [];
  const evictions: Array<[QueryId, DocId]> = [];
  const blockedCandidates: QueryId[] = [];

  if (oldScore !== null) {
    if (next && oldScore === getScore(next)) {
      const covering = queries.getQueriesCovering(oldScore, id);
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
  if (DEBUG_QUERY_ID !== null && lostQueries.has(DEBUG_QUERY_ID)) {
    console.error('[debug lostQueries]', {
      docId: id.toString(),
      lostId: DEBUG_QUERY_ID.toString(),
      matchesOld,
      matchesNew,
    });
  }
  for (const q of lostQueries) {
    const replacement = queries.fillGap(q);
    if (replacement && retrievalJob) {
      if (DEBUG_QUERY_ID !== null && q === DEBUG_QUERY_ID) {
        console.error('[debug fillGap replacement]', {
          docId: id.toString(),
          queryId: q.toString(),
          replacement: replacement.toString(),
        });
      }
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
      retrievalJob.cancel(evictedDoc, q);
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
  queries.debugVerifyState(`handleChange doc=${id.toString()}`);
  notifyRetrieval();
}

const handleItem = <DocState extends DocStateDom>(
  item: StreamItem<DocState>,
  queries: DynamicRangeQueries,
  getScore: (state: DocState) => Score,
  emit: (e: LimitMatchEvent<DocState>) => void,
  options: LimitStreamOptions<DocState>
) => {
  const retrievalJob = options.retrievalJob;
  const docStore = options.docStore;
  switch (item.kind) {
    case 'query-add': {
      const id = queries.addQuery(item.spec.minScore, item.spec.limit, item.spec.maxScore);
      const seedDocs = queries.getDocsForQuery(id);
      if (BigInt(seedDocs.length) !== queries.getQueryInfo(id)?.currentMatches) throw new Error('Inconsistent query state detected when adding query');
      for (const docId of seedDocs) {
        retrievalJob.register(docId, id);
      }
      break;
    }
    case 'query-remove': {
      queries.removeQuery(item.id);
      break;
    }
    case 'seed-docs': {
      if (docStore && item.docs.length) {
        const entries: Array<[DocId, DocState]> = item.docs.map(doc => [doc.id, doc.state]);
        docStore.putMany(entries);
      }
      queries.seedDocuments(item.docs.map(doc => ({ id: doc.id, score: getScore(doc.state) })));
      break;
    }
    case 'doc-change': {
      if (docStore) {
        const { id, new: next } = item.change;
        if (next) docStore.put(id, next);
        else docStore.delete(id);
      }
      handleChange(item.change, queries, getScore, emit, options);
      break;
    }
  }
}


// Stateless limit stream operator (stores only per-query counts already tracked in DynamicRangeQueries)
export function* runLimitStream<DocState extends DocStateDom>(
  getScore: (state: DocState) => Score,
  emit: (e: LimitMatchEvent<DocState>) => void,
  options: LimitStreamOptions<DocState>
): Generator<void, void, StreamItem<DocState> | void> {
  const queries = new DynamicRangeQueries();
  while (true) {
    const item = yield;
    if (!item) break;
    handleItem(item, queries, getScore, emit, options);
  }
}


// Helper to build an async iterable from an array (tests / demos)
export async function* fromIterable<DocState extends DocStateDom>(items: Iterable<StreamItem<DocState>>): AsyncIterable<StreamItem<DocState>> {
  for (const i of items) yield i;
}

export function fromArray<DocState extends DocStateDom>(items: StreamItem<DocState>[]): AsyncIterable<StreamItem<DocState>> {
  return fromIterable(items);
}
