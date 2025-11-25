export type DocStateDom = { readonly __brand?: "DocState" };
export type DocId = { readonly __brand?: "DocId" } & bigint;
export type QueryId = { readonly __brand?: "QueryId" } & bigint;
export type Score = { readonly __brand?: "Score" } & number;
export type BatchNumber = bigint;

export type DocChange<DocState extends DocStateDom> = {
  id: DocId;
  old: DocState | null;
  new: DocState | null;
}

export interface QuerySpec {
  minScore: Score;
  maxScore: Score;
  limit: bigint;
}

export interface LimitMatchEvent<DocState extends DocStateDom> {
  kind: 'match';
  docId: DocId;
  old: DocState | null;
  new: DocState | null;
  matchesOld: QueryId[];
  matchesNew: QueryId[];
  evictions: Array<[QueryId, DocId]>;
}

export interface RetrievalBatchDoc<DocState extends DocStateDom> {
  docId: DocId;
  state: DocState;
  queries: QueryId[];
}

export interface RetrievalEvent<DocState extends DocStateDom> {
  kind: 'retrieval';
  batchNumber: BatchNumber;
  docs: RetrievalBatchDoc<DocState>[];
}

export type DownstreamEvent<DocState extends DocStateDom> = LimitMatchEvent<DocState> | RetrievalEvent<DocState>;

