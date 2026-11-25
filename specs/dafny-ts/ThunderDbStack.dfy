include "DocsIndexModel.dfy"

module ThunderDbStack {
  import opened DocsIndexModel

  type QueryId = int
  type BatchNumber = nat

  datatype DocState = DocState(scoreValue: Score)
  datatype MaybeDocState = NoState | HasState(state: DocState)
  datatype SeedDoc = SeedDoc(id: DocId, state: DocState)
  datatype QuerySpec = QuerySpec(minScore: Score, maxScore: Score, limit: nat)
  datatype Eviction = Eviction(queryId: QueryId, docId: DocId)
  datatype MatchPayload = MatchPayload(docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, matchesOld: seq<QueryId>, matchesNew: seq<QueryId>, evictions: seq<Eviction>)
  datatype RetrievalDoc = RetrievalDoc(docId: DocId, state: DocState, queries: seq<QueryId>)
  datatype DownstreamEvent = MatchEvent(payload: MatchPayload) | RetrievalEvent(batchNumber: BatchNumber, docs: seq<RetrievalDoc>)
  datatype StreamItem =
    | DocChangeItem(id: DocId, oldState: MaybeDocState, newState: MaybeDocState)
    | QueryAddItem(spec: QuerySpec)
    | QueryRemoveItem(id: QueryId)
    | SeedDocsItem(docs: seq<SeedDoc>)

  function GetScore(state: DocState): Score {
    state.scoreValue
  }

  function LookupState(store: map<DocId, DocState>, id: DocId): MaybeDocState {
    if id in store then HasState(store[id]) else NoState
  }

  function PutStoredDoc(store: map<DocId, DocState>, id: DocId, state: DocState): map<DocId, DocState> {
    store[id := state]
  }

  function RemoveStoredDoc(store: map<DocId, DocState>, id: DocId): map<DocId, DocState> {
    map key | key in store && key != id :: store[key]
  }

  function ContainsId(ids: seq<DocId>, id: DocId): bool {
    if |ids| == 0 then false
    else ids[0] == id || ContainsId(ids[1..], id)
  }

  function ContainsQueryId(ids: seq<QueryId>, id: QueryId): bool {
    if |ids| == 0 then false
    else ids[0] == id || ContainsQueryId(ids[1..], id)
  }

  function AppendQueryIdUnique(ids: seq<QueryId>, id: QueryId): seq<QueryId> {
    if ContainsQueryId(ids, id) then ids else ids + [id]
  }

  function UniqueDocIds(ids: seq<DocId>): bool {
    if |ids| == 0 then true
    else !ContainsId(ids[1..], ids[0]) && UniqueDocIds(ids[1..])
  }

  function AppendDocIdIfMissing(ids: seq<DocId>, id: DocId): seq<DocId> {
    if ContainsId(ids, id) then ids else ids + [id]
  }

  function RemoveDocId(ids: seq<DocId>, id: DocId): seq<DocId> {
    if |ids| == 0 then []
    else if ids[0] == id then ids[1..]
    else [ids[0]] + RemoveDocId(ids[1..], id)
  }
}