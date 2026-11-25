include "CleanPendingRuntime.dfy"

module CleanPendingLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened CleanPendingRuntime

  lemma RemoveQueryIdDoesNotGrow(ids: seq<QueryId>, id: QueryId)
    ensures |RemoveQueryId(ids, id)| <= |ids|
    decreases |ids|
  {
    if |ids| == 0 {
    } else if ids[0] == id {
    } else {
      RemoveQueryIdDoesNotGrow(ids[1..], id);
    }
  }

  lemma ResolvePendingDropsDoc(state: PendingState, docId: DocId)
    ensures !(docId in ResolvePendingForDoc(state, docId).byDoc)
  {
  }

  lemma AppendedDocIsPresent(ids: seq<DocId>, docId: DocId)
    ensures ContainsId(ids + [docId], docId)
    decreases |ids|
  {
    if |ids| > 0 {
      AppendedDocIsPresent(ids[1..], docId);
      assert (ids + [docId])[1..] == ids[1..] + [docId];
    }
  }

  lemma AppendedQueryIsPresent(ids: seq<QueryId>, queryId: QueryId)
    ensures ContainsQueryId(ids + [queryId], queryId)
    decreases |ids|
  {
    if |ids| > 0 {
      AppendedQueryIsPresent(ids[1..], queryId);
      assert (ids + [queryId])[1..] == ids[1..] + [queryId];
    }
  }

  lemma RegisterPendingAddsPair(state: PendingState, docId: DocId, queryId: QueryId)
    ensures queryId in RegisterPending(state, docId, queryId).byQuery
    ensures docId in RegisterPending(state, docId, queryId).byDoc
    ensures ContainsId(RegisterPending(state, docId, queryId).byQuery[queryId], docId)
    ensures ContainsQueryId(RegisterPending(state, docId, queryId).byDoc[docId], queryId)
    ensures ContainsId(RegisterPending(state, docId, queryId).docOrder, docId)
  {
    if queryId in state.byQuery {
      AppendedDocIsPresent(state.byQuery[queryId], docId);
    }
    if docId in state.byDoc {
      AppendedQueryIsPresent(state.byDoc[docId], queryId);
    }
    AppendedDocIsPresent(state.docOrder, docId);
  }

  lemma RegisterPendingIsIdempotent(state: PendingState, docId: DocId, queryId: QueryId)
    ensures RegisterPending(RegisterPending(state, docId, queryId), docId, queryId) == RegisterPending(state, docId, queryId)
  {
    RegisterPendingAddsPair(state, docId, queryId);
  }

  lemma CancelPendingPreservesUnrelated(state: PendingState, docId: DocId, queryId: QueryId)
    ensures forall otherDoc :: otherDoc != docId ==>
      ((otherDoc in CancelPending(state, docId, queryId).byDoc <==> otherDoc in state.byDoc) &&
       (otherDoc in state.byDoc ==> CancelPending(state, docId, queryId).byDoc[otherDoc] == state.byDoc[otherDoc]))
    ensures forall otherQuery :: otherQuery != queryId ==>
      ((otherQuery in CancelPending(state, docId, queryId).byQuery <==> otherQuery in state.byQuery) &&
       (otherQuery in state.byQuery ==> CancelPending(state, docId, queryId).byQuery[otherQuery] == state.byQuery[otherQuery]))
  {
  }
}