include "../dafny/ThunderDbStack.dfy"

module CleanPendingRuntime {
  import opened DocsIndexModel
  import opened ThunderDbStack

  datatype PendingState = PendingState(
    byQuery: map<QueryId, seq<DocId>>,
    byDoc: map<DocId, seq<QueryId>>,
    docOrder: seq<DocId>)

  function EmptyPendingState(): PendingState {
    PendingState(map[], map[], [])
  }

  function RemoveQueryId(ids: seq<QueryId>, id: QueryId): seq<QueryId> {
    if |ids| == 0 then []
    else if ids[0] == id then ids[1..]
    else [ids[0]] + RemoveQueryId(ids[1..], id)
  }

  function RemovePendingDoc(state: PendingState, docId: DocId): PendingState {
    PendingState(state.byQuery, map key | key in state.byDoc && key != docId :: state.byDoc[key], RemoveDocId(state.docOrder, docId))
  }

  function RegisterPending(state: PendingState, docId: DocId, queryId: QueryId): PendingState {
    var docsForQuery := if queryId in state.byQuery then AppendDocIdIfMissing(state.byQuery[queryId], docId) else [docId];
    var queriesForDoc := if docId in state.byDoc then AppendQueryIdUnique(state.byDoc[docId], queryId) else [queryId];
    PendingState(
      state.byQuery[queryId := docsForQuery],
      state.byDoc[docId := queriesForDoc],
      AppendDocIdIfMissing(state.docOrder, docId))
  }

  function CancelPending(state: PendingState, docId: DocId, queryId: QueryId): PendingState {
    var byQuery2 :=
      if queryId in state.byQuery && ContainsId(state.byQuery[queryId], docId) then
        var nextDocs := RemoveDocId(state.byQuery[queryId], docId);
        if |nextDocs| == 0 then map key | key in state.byQuery && key != queryId :: state.byQuery[key]
        else state.byQuery[queryId := nextDocs]
      else
        state.byQuery;
    var byDoc2 :=
      if docId in state.byDoc && ContainsQueryId(state.byDoc[docId], queryId) then
        var nextQueries := RemoveQueryId(state.byDoc[docId], queryId);
        if |nextQueries| == 0 then map key | key in state.byDoc && key != docId :: state.byDoc[key]
        else state.byDoc[docId := nextQueries]
      else
        state.byDoc;
    var order2 := if docId in byDoc2 then state.docOrder else RemoveDocId(state.docOrder, docId);
    PendingState(byQuery2, byDoc2, order2)
  }

  function ResolvePendingForDoc(state: PendingState, docId: DocId): PendingState {
    if !(docId in state.byDoc) then state
    else
      var queriesForDoc := state.byDoc[docId];
      var byQuery2 := RemoveDocFromQueries(state.byQuery, queriesForDoc, docId);
      PendingState(byQuery2, map key | key in state.byDoc && key != docId :: state.byDoc[key], RemoveDocId(state.docOrder, docId))
  }

  function RemoveDocFromQueries(byQuery: map<QueryId, seq<DocId>>, queries: seq<QueryId>, docId: DocId): map<QueryId, seq<DocId>>
    decreases |queries|
  {
    if |queries| == 0 then byQuery
    else
      var nextByQuery :=
        if queries[0] in byQuery then
          var nextDocs := RemoveDocId(byQuery[queries[0]], docId);
          if |nextDocs| == 0 then map key | key in byQuery && key != queries[0] :: byQuery[key]
          else byQuery[queries[0] := nextDocs]
        else
          byQuery;
      RemoveDocFromQueries(nextByQuery, queries[1..], docId)
  }

  function BuildGroupedRetrievals(order: seq<DocId>, byDoc: map<DocId, seq<QueryId>>, store: map<DocId, DocState>): seq<RetrievalDoc>
    decreases |order|
  {
    if |order| == 0 then []
    else if !(order[0] in byDoc) then BuildGroupedRetrievals(order[1..], byDoc, store)
    else
      match LookupState(store, order[0])
      case NoState => BuildGroupedRetrievals(order[1..], byDoc, store)
      case HasState(state) => [RetrievalDoc(order[0], state, byDoc[order[0]])] + BuildGroupedRetrievals(order[1..], byDoc, store)
  }

  class PendingRegistry {
    var state: PendingState

    constructor ()
      ensures this.state == EmptyPendingState()
    {
      this.state := EmptyPendingState();
    }

    method Register(docId: DocId, queryId: QueryId)
      modifies this
    {
      this.state := RegisterPending(this.state, docId, queryId);
    }

    method Cancel(docId: DocId, queryId: QueryId) returns (removed: bool)
      modifies this
    {
      removed := docId in this.state.byDoc && ContainsQueryId(this.state.byDoc[docId], queryId);
      this.state := CancelPending(this.state, docId, queryId);
    }

    method ResolveDoc(docId: DocId)
      modifies this
    {
      this.state := ResolvePendingForDoc(this.state, docId);
    }

    method PendingQueries(docId: DocId) returns (queries: seq<QueryId>) {
      queries := if docId in this.state.byDoc then this.state.byDoc[docId] else [];
    }

    method PendingDocs(queryId: QueryId) returns (docs: seq<DocId>) {
      docs := if queryId in this.state.byQuery then this.state.byQuery[queryId] else [];
    }

    method DrainGrouped(store: map<DocId, DocState>) returns (docs: seq<RetrievalDoc>)
      modifies this
    {
      docs := BuildGroupedRetrievals(this.state.docOrder, this.state.byDoc, store);
      this.state := EmptyPendingState();
    }
  }
}