include "CleanPendingRuntime.dfy"

module CleanPendingLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened CleanPendingRuntime

  ghost predicate PendingPairsAgree(state: PendingState) {
    forall docId: DocId, queryId: QueryId ::
      (queryId in state.byQuery && docId in state.byQuery[queryId]) <==>
      (docId in state.byDoc && queryId in state.byDoc[docId])
  }

  ghost predicate Distinct<T>(values: seq<T>) {
    forall left, right :: 0 <= left < right < |values| ==> values[left] != values[right]
  }

  ghost predicate PendingOrderAgree(state: PendingState) {
    Distinct(state.docOrder) &&
    (forall docId: DocId :: docId in state.byDoc <==> docId in state.docOrder)
  }

  ghost predicate PendingEntriesValid(state: PendingState) {
    (forall queryId: QueryId :: queryId in state.byQuery ==>
      |state.byQuery[queryId]| > 0 && Distinct(state.byQuery[queryId])) &&
    (forall docId: DocId :: docId in state.byDoc ==>
      |state.byDoc[docId]| > 0 && Distinct(state.byDoc[docId]))
  }

  ghost predicate PendingConsistent(state: PendingState) {
    PendingPairsAgree(state) && PendingOrderAgree(state) && PendingEntriesValid(state)
  }

  lemma AppendUniquePreservesDistinct<T>(values: seq<T>, value: T)
    requires Distinct(values)
    ensures Distinct(if value in values then values else values + [value])
  {
  }

  lemma EmptyPendingPairsAgree()
    ensures PendingPairsAgree(EmptyPendingState())
    ensures PendingOrderAgree(EmptyPendingState())
    ensures PendingEntriesValid(EmptyPendingState())
  {
  }

  lemma RegisterPreservesPendingPairs(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingPairsAgree(state)
    ensures PendingPairsAgree(RegisterPending(state, docId, queryId))
  {
  }

  lemma RegisterPreservesPendingOrder(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingOrderAgree(state)
    ensures PendingOrderAgree(RegisterPending(state, docId, queryId))
  {
    AppendUniquePreservesDistinct(state.docOrder, docId);
  }

  lemma RegisterPreservesPendingEntries(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingEntriesValid(state)
    ensures PendingEntriesValid(RegisterPending(state, docId, queryId))
  {
    if queryId in state.byQuery {
      AppendUniquePreservesDistinct(state.byQuery[queryId], docId);
    }
    if docId in state.byDoc {
      AppendUniquePreservesDistinct(state.byDoc[docId], queryId);
    }
  }

  lemma RegisterPreservesPendingConsistency(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingConsistent(state)
    ensures PendingConsistent(RegisterPending(state, docId, queryId))
  {
    RegisterPreservesPendingPairs(state, docId, queryId);
    RegisterPreservesPendingOrder(state, docId, queryId);
    RegisterPreservesPendingEntries(state, docId, queryId);
  }

  lemma RemoveDocReferenceProperties(ids: seq<DocId>, id: DocId)
    requires Distinct(ids)
    ensures Distinct(RemoveDocIdReference(ids, id))
    ensures forall other: DocId :: other in RemoveDocIdReference(ids, id) <==> other in ids && other != id
    decreases |ids|
  {
    if |ids| > 0 && ids[0] != id {
      RemoveDocReferenceProperties(ids[1..], id);
      var tail := RemoveDocIdReference(ids[1..], id);
      forall index | 0 <= index < |tail|
        ensures ids[0] != tail[index]
      {
        assert tail[index] in ids[1..];
        assert exists oldIndex :: 1 <= oldIndex < |ids| && ids[oldIndex] == tail[index];
      }
      assert Distinct([ids[0]] + tail);
    }
  }

  lemma RemoveAbsentDocId(ids: seq<DocId>, id: DocId)
    requires id !in ids
    ensures RemoveDocId(ids, id) == ids
    decreases |ids|
  {
    if |ids| > 0 {
      RemoveAbsentDocId(ids[1..], id);
      assert ids == [ids[0]] + ids[1..];
    }
  }

  lemma RemoveQueryMatchesDocReference(ids: seq<QueryId>, id: QueryId)
    ensures RemoveQueryId(ids, id) == RemoveDocIdReference(ids, id)
    decreases |ids|
  {
    if |ids| > 0 && ids[0] != id {
      RemoveQueryMatchesDocReference(ids[1..], id);
    }
  }

  lemma CancelPreservesPendingPairs(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingPairsAgree(state)
    requires PendingEntriesValid(state)
    ensures PendingPairsAgree(CancelPending(state, docId, queryId))
  {
    if queryId in state.byQuery {
      RemoveDocReferenceProperties(state.byQuery[queryId], docId);
    }
    if docId in state.byDoc {
      RemoveDocReferenceProperties(state.byDoc[docId], queryId);
      RemoveQueryMatchesDocReference(state.byDoc[docId], queryId);
    }
  }

  lemma CancelPreservesPendingOrder(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingOrderAgree(state)
    ensures PendingOrderAgree(CancelPending(state, docId, queryId))
  {
    RemoveDocReferenceProperties(state.docOrder, docId);
  }

  lemma CancelPreservesPendingEntries(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingEntriesValid(state)
    ensures PendingEntriesValid(CancelPending(state, docId, queryId))
  {
    if queryId in state.byQuery {
      RemoveDocReferenceProperties(state.byQuery[queryId], docId);
    }
    if docId in state.byDoc {
      RemoveDocReferenceProperties(state.byDoc[docId], queryId);
      RemoveQueryMatchesDocReference(state.byDoc[docId], queryId);
    }
  }

  lemma CancelPreservesPendingConsistency(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingConsistent(state)
    ensures PendingConsistent(CancelPending(state, docId, queryId))
  {
    CancelPreservesPendingPairs(state, docId, queryId);
    CancelPreservesPendingOrder(state, docId, queryId);
    CancelPreservesPendingEntries(state, docId, queryId);
  }

  lemma CancelPendingPairMembership(state: PendingState, docId: DocId, queryId: QueryId)
    requires PendingConsistent(state)
    ensures forall otherDoc: DocId, otherQuery: QueryId ::
      (otherQuery in CancelPending(state, docId, queryId).byQuery &&
        otherDoc in CancelPending(state, docId, queryId).byQuery[otherQuery]) <==>
      (otherQuery in state.byQuery && otherDoc in state.byQuery[otherQuery] &&
        (otherDoc != docId || otherQuery != queryId))
  {
    if queryId in state.byQuery {
      RemoveDocReferenceProperties(state.byQuery[queryId], docId);
    }
  }

  lemma CancelAddsNoQueryKeys(state: PendingState, docId: DocId, queryId: QueryId)
    ensures forall otherQuery: QueryId :: otherQuery in CancelPending(state, docId, queryId).byQuery ==> otherQuery in state.byQuery
  {
  }

  lemma CancelAddsNoDocKeys(state: PendingState, docId: DocId, queryId: QueryId)
    ensures forall otherDoc: DocId :: otherDoc in CancelPending(state, docId, queryId).byDoc ==> otherDoc in state.byDoc
  {
  }

  lemma RemoveDocFromQueriesProperties(byQuery: map<QueryId, seq<DocId>>, queries: seq<QueryId>, docId: DocId)
    requires forall queryId: QueryId :: queryId in byQuery ==> |byQuery[queryId]| > 0 && Distinct(byQuery[queryId])
    ensures forall queryId: QueryId :: queryId in RemoveDocFromQueries(byQuery, queries, docId) ==>
      |RemoveDocFromQueries(byQuery, queries, docId)[queryId]| > 0 && Distinct(RemoveDocFromQueries(byQuery, queries, docId)[queryId])
    ensures forall queryId: QueryId, otherDoc: DocId ::
      (queryId in RemoveDocFromQueries(byQuery, queries, docId) && otherDoc in RemoveDocFromQueries(byQuery, queries, docId)[queryId]) <==>
      (queryId in byQuery && otherDoc in byQuery[queryId] && (otherDoc != docId || queryId !in queries))
    decreases |queries|
  {
    if |queries| > 0 {
      var queryId := queries[0];
      if queryId in byQuery {
        RemoveDocReferenceProperties(byQuery[queryId], docId);
      }
      var nextByQuery :=
        if queryId in byQuery then
          var nextDocs := RemoveDocId(byQuery[queryId], docId);
          if |nextDocs| == 0 then byQuery - {queryId} else byQuery[queryId := nextDocs]
        else byQuery;
      RemoveDocFromQueriesProperties(nextByQuery, queries[1..], docId);
      forall otherQuery: QueryId, otherDoc: DocId
        ensures (otherQuery in RemoveDocFromQueries(byQuery, queries, docId) &&
          otherDoc in RemoveDocFromQueries(byQuery, queries, docId)[otherQuery]) <==>
          (otherQuery in byQuery && otherDoc in byQuery[otherQuery] && (otherDoc != docId || otherQuery !in queries))
      {
        assert (otherQuery in nextByQuery && otherDoc in nextByQuery[otherQuery]) <==>
          (otherQuery in byQuery && otherDoc in byQuery[otherQuery] && (otherDoc != docId || otherQuery != queryId));
        assert (otherQuery !in queries) <==> (otherQuery != queryId && otherQuery !in queries[1..]);
      }
    }
  }

  lemma ResolvePreservesPendingConsistency(state: PendingState, docId: DocId)
    requires PendingConsistent(state)
    ensures PendingConsistent(ResolvePendingForDoc(state, docId))
    ensures forall queryId: QueryId :: queryId in ResolvePendingForDoc(state, docId).byQuery ==>
      docId !in ResolvePendingForDoc(state, docId).byQuery[queryId]
  {
    if docId in state.byDoc {
      RemoveDocReferenceProperties(state.docOrder, docId);
      RemoveDocFromQueriesProperties(state.byQuery, state.byDoc[docId], docId);
      var next := ResolvePendingForDoc(state, docId);
      forall otherDoc: DocId, queryId: QueryId
        ensures (queryId in next.byQuery && otherDoc in next.byQuery[queryId]) <==>
          (otherDoc in next.byDoc && queryId in next.byDoc[otherDoc])
      {
        assert (queryId in next.byQuery && otherDoc in next.byQuery[queryId]) <==>
          (queryId in state.byQuery && otherDoc in state.byQuery[queryId] &&
            (otherDoc != docId || queryId !in state.byDoc[docId]));
        assert (otherDoc in next.byDoc && queryId in next.byDoc[otherDoc]) <==>
          (otherDoc != docId && otherDoc in state.byDoc && queryId in state.byDoc[otherDoc]);
        assert (queryId in state.byQuery && otherDoc in state.byQuery[queryId]) <==>
          (otherDoc in state.byDoc && queryId in state.byDoc[otherDoc]);
        if otherDoc == docId {
          assert queryId in state.byQuery && docId in state.byQuery[queryId] ==> queryId in state.byDoc[docId];
        }
      }
    }
  }

  lemma ResolveAddsNoQueryKeys(state: PendingState, docId: DocId)
    requires PendingConsistent(state)
    ensures forall queryId: QueryId :: queryId in ResolvePendingForDoc(state, docId).byQuery ==> queryId in state.byQuery
  {
    if docId in state.byDoc {
      RemoveDocFromQueriesProperties(state.byQuery, state.byDoc[docId], docId);
      forall queryId: QueryId | queryId in ResolvePendingForDoc(state, docId).byQuery
        ensures queryId in state.byQuery
      {
        var next := ResolvePendingForDoc(state, docId);
        assert |next.byQuery[queryId]| > 0;
        var otherDoc := next.byQuery[queryId][0];
        assert otherDoc in next.byQuery[queryId];
      }
    }
  }

  lemma GroupedRetrievalsSoundAndComplete(order: seq<DocId>, byDoc: map<DocId, seq<QueryId>>, store: map<DocId, DocState>)
    ensures forall entry: RetrievalDoc :: entry in BuildGroupedRetrievals(order, byDoc, store) ==>
      entry.docId in order && entry.docId in byDoc && entry.docId in store &&
      entry.state == store[entry.docId] && entry.queries == byDoc[entry.docId]
    ensures forall docId: DocId :: docId in order && docId in byDoc && docId in store ==>
      RetrievalDoc(docId, store[docId], byDoc[docId]) in BuildGroupedRetrievals(order, byDoc, store)
    decreases |order|
  {
    if |order| > 0 {
      GroupedRetrievalsSoundAndComplete(order[1..], byDoc, store);
    }
  }

  ghost predicate GroupedPairsDelivered(state: PendingState, store: map<DocId, DocState>, docs: seq<RetrievalDoc>) {
    forall queryId: QueryId, docId: DocId ::
      (queryId in state.byQuery && docId in state.byQuery[queryId]) ==>
        (docId in store && docId in state.byDoc && queryId in state.byDoc[docId] &&
         RetrievalDoc(docId, store[docId], state.byDoc[docId]) in docs)
  }

  lemma GroupedRetrievalsDeliverPairs(state: PendingState, store: map<DocId, DocState>)
    requires PendingConsistent(state)
    requires forall docId: DocId :: docId in state.byDoc ==> docId in store
    ensures GroupedPairsDelivered(state, store, BuildGroupedRetrievals(state.docOrder, state.byDoc, store))
  {
    GroupedRetrievalsSoundAndComplete(state.docOrder, state.byDoc, store);
    forall queryId: QueryId, docId: DocId | queryId in state.byQuery && docId in state.byQuery[queryId]
      ensures docId in store && docId in state.byDoc && queryId in state.byDoc[docId] &&
        RetrievalDoc(docId, store[docId], state.byDoc[docId]) in BuildGroupedRetrievals(state.docOrder, state.byDoc, store)
    {
      assert docId in state.byDoc;
      assert docId in state.docOrder;
    }
  }

  ghost predicate GroupedPairsExact(state: PendingState, docs: seq<RetrievalDoc>) {
    forall queryId: QueryId, docId: DocId ::
      (queryId in state.byQuery && docId in state.byQuery[queryId]) <==>
      (exists entry: RetrievalDoc :: entry in docs && entry.docId == docId && queryId in entry.queries)
  }

  lemma GroupedRetrievalsHaveExactPairs(state: PendingState, store: map<DocId, DocState>)
    requires PendingConsistent(state)
    requires forall docId: DocId :: docId in state.byDoc ==> docId in store
    ensures GroupedPairsExact(state, BuildGroupedRetrievals(state.docOrder, state.byDoc, store))
  {
    GroupedRetrievalsDeliverPairs(state, store);
    GroupedRetrievalsSoundAndComplete(state.docOrder, state.byDoc, store);
    var docs := BuildGroupedRetrievals(state.docOrder, state.byDoc, store);
    forall queryId: QueryId, docId: DocId
      ensures (queryId in state.byQuery && docId in state.byQuery[queryId]) <==>
        (exists entry: RetrievalDoc :: entry in docs && entry.docId == docId && queryId in entry.queries)
    {
      if queryId in state.byQuery && docId in state.byQuery[queryId] {
        assert RetrievalDoc(docId, store[docId], state.byDoc[docId]) in docs;
      }
      if exists entry: RetrievalDoc :: entry in docs && entry.docId == docId && queryId in entry.queries {
        var entry: RetrievalDoc :| entry in docs && entry.docId == docId && queryId in entry.queries;
        assert docId in state.byDoc && queryId in state.byDoc[docId];
      }
    }
  }

  lemma GroupedRetrievalsHaveUniqueDocs(order: seq<DocId>, byDoc: map<DocId, seq<QueryId>>, store: map<DocId, DocState>)
    requires Distinct(order)
    ensures forall left, right :: 0 <= left < right < |BuildGroupedRetrievals(order, byDoc, store)| ==>
      BuildGroupedRetrievals(order, byDoc, store)[left].docId != BuildGroupedRetrievals(order, byDoc, store)[right].docId
    decreases |order|
  {
    if |order| > 0 {
      GroupedRetrievalsHaveUniqueDocs(order[1..], byDoc, store);
      GroupedRetrievalsSoundAndComplete(order[1..], byDoc, store);
    }
  }

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