include "CleanPendingLemmas.dfy"

module CleanLimitEngine {
  import opened DocsIndexModel
  import opened DocsIndexTreap
  import opened ThunderDbStack
  import opened CleanPendingRuntime
  import opened CleanPendingLemmas

  datatype CleanQueryState = CleanQueryState(spec: QuerySpec, currentMatches: nat)

  ghost predicate TreeMatchesStore(t: Treap, store: map<DocId, DocState>) {
    forall entry: Entry :: entry in Entries(t) <==>
      (entry.id in store && entry.score == GetScore(store[entry.id]))
  }

  ghost predicate ChangeMatchesStore(store: map<DocId, DocState>, id: DocId, oldState: MaybeDocState) {
    match oldState
    case NoState => id !in store
    case HasState(value) => id in store && store[id] == value
  }

  ghost predicate ItemMatchesStore(store: map<DocId, DocState>, item: StreamItem) {
    match item
    case DocChangeItem(id, oldState, _) => ChangeMatchesStore(store, id, oldState)
    case QueryAddItem(_) => true
    case QueryRemoveItem(_) => true
    case SeedDocsItem(_) => true
  }

  lemma ReplaceTreeEntryMatchesStore(t: Treap, store: map<DocId, DocState>, id: DocId, state: DocState)
    requires ValidTreap(t)
    requires TreeMatchesStore(t, store)
    ensures ValidTreap(Add(if id in store then Remove(t, GetScore(store[id]), id) else t,
      GetScore(state), id, PriorityFor(GetScore(state), id)))
    ensures TreeMatchesStore(Add(if id in store then Remove(t, GetScore(store[id]), id) else t,
      GetScore(state), id, PriorityFor(GetScore(state), id)), store[id := state])
  {
    if id in store {
      RemovePreservesValidTreap(t, GetScore(store[id]), id);
    }
    var beforeAdd := if id in store then Remove(t, GetScore(store[id]), id) else t;
    AddPreservesValidTreap(beforeAdd, GetScore(state), id, PriorityFor(GetScore(state), id));
    forall entry: Entry
      ensures entry in Entries(Add(beforeAdd, GetScore(state), id, PriorityFor(GetScore(state), id))) <==>
        (entry.id in store[id := state] && entry.score == GetScore(store[id := state][entry.id]))
    {
      AddPreservesEntryMembership(beforeAdd, GetScore(state), id, PriorityFor(GetScore(state), id), entry);
      if id in store {
        RemovePreservesEntryMembership(t, NoScore, NoScore, GetScore(store[id]), id, entry);
      }
    }
  }

  lemma RemoveTreeEntryMatchesStore(t: Treap, store: map<DocId, DocState>, id: DocId)
    requires ValidTreap(t)
    requires TreeMatchesStore(t, store)
    requires id in store
    ensures ValidTreap(Remove(t, GetScore(store[id]), id))
    ensures TreeMatchesStore(Remove(t, GetScore(store[id]), id), store - {id})
  {
    RemovePreservesValidTreap(t, GetScore(store[id]), id);
    forall entry: Entry
      ensures entry in Entries(Remove(t, GetScore(store[id]), id)) <==>
        (entry.id in store - {id} && entry.score == GetScore((store - {id})[entry.id]))
    {
      RemovePreservesEntryMembership(t, NoScore, NoScore, GetScore(store[id]), id, entry);
    }
  }

  lemma TreapRangeMembersStored(t: Treap, store: map<DocId, DocState>, minScore: Score, maxScore: Score, limit: nat)
    requires ValidTreap(t)
    requires TreeMatchesStore(t, store)
    ensures forall docId: DocId :: docId in TreapCollectRange(t, minScore, maxScore, limit) ==> docId in store
  {
    ValidTreapCollectRangeRefinesModel(t, minScore, maxScore, limit);
    CollectRangeSound(Entries(t), minScore, maxScore, limit);
    forall docId: DocId | docId in TreapCollectRange(t, minScore, maxScore, limit)
      ensures docId in store
    {
      var entry: Entry :| entry in Entries(t) && entry.id == docId && minScore <= entry.score <= maxScore;
    }
  }

  function DocVisibleInTreap(t: Treap, spec: QuerySpec, score: Score, id: DocId): bool
    requires SumConsistent(t)
  {
    if score < spec.minScore || score > spec.maxScore then false
    else
      var startRank := TreapRank(t, spec.minScore, NoDoc);
      var docRank := TreapRank(t, score, SomeDoc(id));
      var upper := TreapCountAtMost(t, spec.maxScore);
      docRank < upper && startRank <= docRank && docRank - startRank < spec.limit
  }

  ghost function VisibleQueryIds(t: Treap, ids: seq<QueryId>, queries: map<QueryId, CleanQueryState>, score: Score, id: DocId): seq<QueryId>
    requires SumConsistent(t)
    decreases |ids|
  {
    if |ids| == 0 then []
    else ((if ids[0] in queries && DocVisibleInTreap(t, queries[ids[0]].spec, score, id) then [ids[0]] else []) +
      VisibleQueryIds(t, ids[1..], queries, score, id))
  }

  lemma VisibleQueryIdsAppend(t: Treap, ids: seq<QueryId>, queries: map<QueryId, CleanQueryState>, score: Score, id: DocId, queryId: QueryId)
    requires SumConsistent(t)
    ensures VisibleQueryIds(t, ids + [queryId], queries, score, id) ==
      VisibleQueryIds(t, ids, queries, score, id) +
      (if queryId in queries && DocVisibleInTreap(t, queries[queryId].spec, score, id) then [queryId] else [])
    decreases |ids|
  {
    if |ids| > 0 {
      assert (ids + [queryId])[1..] == ids[1..] + [queryId];
      VisibleQueryIdsAppend(t, ids[1..], queries, score, id, queryId);
    }
  }

  class CleanEngine {
    var docs: Treap
    var store: map<DocId, DocState>
    var docIds: seq<DocId>
    var queries: map<QueryId, CleanQueryState>
    var queryIds: seq<QueryId>
    var pendingState: PendingState
    var nextQueryId: QueryId

    constructor ()
      ensures this.docs == Empty
      ensures this.store == map[]
      ensures this.docIds == []
      ensures this.queries == map[]
      ensures this.queryIds == []
      ensures this.pendingState == EmptyPendingState()
      ensures PendingConsistent(this.pendingState)
      ensures this.nextQueryId == 1
      ensures this.Ready()
      ensures ValidTreap(this.docs)
      ensures this.DocumentsConsistent()
      ensures this.QueryRegistryConsistent()
      ensures this.PendingQueriesRegistered()
      ensures this.PendingDocsStored()
      ensures this.RegistriesConsistent()
      ensures this.StructuralStateConsistent()
    {
      this.docs := Empty;
      this.store := map[];
      this.docIds := [];
      this.queries := map[];
      this.queryIds := [];
      this.pendingState := EmptyPendingState();
      EmptyPendingPairsAgree();
      this.nextQueryId := 1;
    }

    predicate Ready()
      reads this
    {
      SumConsistent(this.docs)
    }

    ghost predicate QueryRegistryConsistent()
      reads this
    {
      Distinct(this.queryIds) &&
      (forall queryId: QueryId :: queryId in this.queries <==> queryId in this.queryIds) &&
      1 <= this.nextQueryId &&
      (forall queryId: QueryId :: queryId in this.queries ==> 1 <= queryId < this.nextQueryId)
    }

    ghost predicate PendingQueriesRegistered()
      reads this
    {
      forall queryId: QueryId :: queryId in this.pendingState.byQuery ==> queryId in this.queries
    }

    ghost predicate PendingDocsStored()
      reads this
    {
      forall docId: DocId :: docId in this.pendingState.byDoc ==> docId in this.store
    }

    ghost predicate PendingDocsStoredExcept(excluded: DocId)
      reads this
    {
      forall docId: DocId :: docId in this.pendingState.byDoc ==> docId == excluded || docId in this.store
    }

    ghost predicate RegistriesConsistent()
      reads this
    {
      this.QueryRegistryConsistent() && PendingConsistent(this.pendingState) && this.PendingQueriesRegistered()
    }

    ghost predicate DocumentsConsistent()
      reads this
    {
      ValidTreap(this.docs) && TreeMatchesStore(this.docs, this.store) && Distinct(this.docIds) &&
      (forall docId: DocId :: docId in this.store <==> docId in this.docIds)
    }

    ghost predicate StructuralStateConsistent()
      reads this
    {
      this.RegistriesConsistent() && this.DocumentsConsistent() && this.PendingDocsStored()
    }

    method SeedDocs(input: seq<SeedDoc>)
      requires this.Ready()
      ensures this.Ready()
      ensures this.pendingState == old(this.pendingState)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
      ensures old(ValidTreap(this.docs)) ==> ValidTreap(this.docs)
      ensures old(this.DocumentsConsistent()) ==> this.DocumentsConsistent()
      ensures old(this.PendingDocsStored()) ==> this.PendingDocsStored()
      modifies this
    {
      var i := 0;
      while i < |input|
        invariant 0 <= i <= |input|
        invariant SumConsistent(this.docs)
        invariant this.pendingState == old(this.pendingState)
        invariant old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
        invariant old(this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
        invariant old(ValidTreap(this.docs)) ==> ValidTreap(this.docs)
        invariant old(this.DocumentsConsistent()) ==> this.DocumentsConsistent()
        invariant old(this.PendingDocsStored()) ==> this.PendingDocsStored()
      {
        ghost var beforeTree := this.docs;
        ghost var beforeStore := this.store;
        if old(this.DocumentsConsistent()) {
          ReplaceTreeEntryMatchesStore(beforeTree, beforeStore, input[i].id, input[i].state);
          AppendUniquePreservesDistinct(this.docIds, input[i].id);
        }
        if input[i].id in this.store {
          var previousScore := GetScore(this.store[input[i].id]);
          if old(ValidTreap(this.docs)) {
            RemovePreservesValidTreap(this.docs, previousScore, input[i].id);
          }
          this.docs := Remove(this.docs, previousScore, input[i].id);
        }
        this.store := this.store[input[i].id := input[i].state];
        this.docIds := AppendDocIdIfMissing(this.docIds, input[i].id);
        if old(ValidTreap(this.docs)) {
          AddPreservesValidTreap(this.docs, input[i].state.scoreValue, input[i].id, PriorityFor(input[i].state.scoreValue, input[i].id));
        }
        this.docs := Add(this.docs, input[i].state.scoreValue, input[i].id, PriorityFor(input[i].state.scoreValue, input[i].id));
        i := i + 1;
      }
    }

    method QueryVisible(queryId: QueryId) returns (visible: seq<DocId>)
      requires this.Ready()
      ensures ValidTreap(this.docs) ==> SortedEntries(Entries(this.docs))
      ensures queryId !in this.queries ==> visible == []
      ensures ValidTreap(this.docs) && queryId in this.queries ==>
        visible == CollectRange(Entries(this.docs), this.queries[queryId].spec.minScore,
          this.queries[queryId].spec.maxScore, this.queries[queryId].spec.limit)
      ensures this.DocumentsConsistent() && queryId in this.queries ==> |visible| <= this.queries[queryId].spec.limit
      ensures this.DocumentsConsistent() && queryId in this.queries ==>
        (forall docId: DocId :: docId in visible ==> (docId in this.store &&
          this.queries[queryId].spec.minScore <= GetScore(this.store[docId]) <= this.queries[queryId].spec.maxScore))
    {
      if ValidTreap(this.docs) {
        EntriesSortedFromTree(this.docs, NoScore, NoScore);
      }
      if queryId in this.queries {
        var spec := this.queries[queryId].spec;
        if ValidTreap(this.docs) {
          ValidTreapCollectRangeRefinesModel(this.docs, spec.minScore, spec.maxScore, spec.limit);
        }
        visible := TreapCollectRange(this.docs, spec.minScore, spec.maxScore, spec.limit);
        if this.DocumentsConsistent() {
          CollectRangeSound(Entries(this.docs), spec.minScore, spec.maxScore, spec.limit);
          forall docId: DocId | docId in visible
            ensures docId in this.store && spec.minScore <= GetScore(this.store[docId]) <= spec.maxScore
          {
            var entry: Entry :| entry in Entries(this.docs) && entry.id == docId && spec.minScore <= entry.score <= spec.maxScore;
          }
        }
      } else {
        visible := [];
      }
    }

    method QueryDocAtOffset(spec: QuerySpec, offset: nat) returns (doc: MaybeDocId)
      requires this.Ready()
      ensures offset >= Sum(this.docs) ==> doc.NoDoc?
      ensures this.DocumentsConsistent() && doc.SomeDoc? ==> doc.doc in this.store
    {
      var startRank := TreapRank(this.docs, spec.minScore, NoDoc);
      TreapGetAtRankReturnsEntry(this.docs, startRank + offset);
      SumEqualsEntriesLength(this.docs);
      match TreapGetAtRank(this.docs, startRank + offset)
      case Missing => {
        doc := NoDoc;
      }
      case Found(score, id, pos) => {
        if this.DocumentsConsistent() {
          assert startRank + offset < |Entries(this.docs)|;
          assert Entry(score, id) in Entries(this.docs);
        }
        if score <= spec.maxScore {
          doc := SomeDoc(id);
        } else {
          doc := NoDoc;
        }
      }
    }

    method CollectVisibleQueriesInTreap(t: Treap, id: DocId, state: DocState) returns (matches: seq<QueryId>)
      requires SumConsistent(t)
      ensures matches == VisibleQueryIds(t, this.queryIds, this.queries, GetScore(state), id)
    {
      matches := [];
      var i := 0;
      while i < |this.queryIds|
        invariant 0 <= i <= |this.queryIds|
        invariant matches == VisibleQueryIds(t, this.queryIds[..i], this.queries, GetScore(state), id)
        invariant SumConsistent(t)
      {
        var queryId := this.queryIds[i];
        VisibleQueryIdsAppend(t, this.queryIds[..i], this.queries, GetScore(state), id, queryId);
        if queryId in this.queries {
          var spec := this.queries[queryId].spec;
          if DocVisibleInTreap(t, spec, GetScore(state), id) {
            matches := matches + [queryId];
          }
        }
        assert this.queryIds[..i] + [queryId] == this.queryIds[..i + 1];
        i := i + 1;
      }
      assert i == |this.queryIds|;
      assert this.queryIds[..i] == this.queryIds;
      assert matches == VisibleQueryIds(t, this.queryIds, this.queries, GetScore(state), id);
    }

    method FillGap(queryId: QueryId) returns (registered: bool)
      requires this.Ready()
      ensures this.Ready()
      ensures old(PendingConsistent(this.pendingState)) ==> PendingConsistent(this.pendingState)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
      ensures this.docs == old(this.docs)
      ensures this.store == old(this.store) && this.docIds == old(this.docIds)
      ensures old(this.DocumentsConsistent() && this.PendingDocsStored()) ==> this.PendingDocsStored()
      ensures old(this.DocumentsConsistent()) ==>
        (forall docId: DocId :: docId in this.pendingState.byDoc ==> docId in old(this.pendingState).byDoc || docId in this.store)
      modifies this
    {
      ghost var wasPendingConsistent := PendingConsistent(this.pendingState);
      ghost var wasQueryRegistryConsistent := this.QueryRegistryConsistent();
      ghost var werePendingQueriesRegistered := this.PendingQueriesRegistered();
      ghost var werePendingDocsValid := this.DocumentsConsistent() && this.PendingDocsStored();
      ghost var beforePending := this.pendingState;
      registered := false;
      if queryId in this.queries {
        var query := this.queries[queryId];
        if query.currentMatches < query.spec.limit {
          var offset := query.currentMatches;
          var initialDocs := this.docs;
          while !registered
            modifies this
            invariant SumConsistent(this.docs)
            invariant this.docs == initialDocs
            invariant this.store == old(this.store) && this.docIds == old(this.docIds)
            invariant queryId in this.queries
            invariant wasPendingConsistent ==> PendingConsistent(this.pendingState)
            invariant wasQueryRegistryConsistent ==> this.QueryRegistryConsistent()
            invariant werePendingQueriesRegistered ==> this.PendingQueriesRegistered()
            invariant werePendingDocsValid ==> this.DocumentsConsistent() && this.PendingDocsStored()
            invariant old(this.DocumentsConsistent()) ==> this.DocumentsConsistent()
            invariant old(this.DocumentsConsistent()) ==>
              (forall docId: DocId :: docId in this.pendingState.byDoc ==> docId in beforePending.byDoc || docId in this.store)
            decreases if registered then 0 else if offset < Sum(initialDocs) then Sum(initialDocs) - offset + 1 else 1
          {
            var candidate := this.QueryDocAtOffset(query.spec, offset);
            match candidate
            case NoDoc => {
              return;
            }
            case SomeDoc(docId) => {
              var alreadyPending := queryId in this.pendingState.byQuery && ContainsId(this.pendingState.byQuery[queryId], docId);
              if alreadyPending {
                offset := offset + 1;
              } else {
                this.queries := this.queries[queryId := CleanQueryState(query.spec, query.currentMatches + 1)];
                if wasPendingConsistent {
                  RegisterPreservesPendingConsistency(this.pendingState, docId, queryId);
                }
                this.pendingState := RegisterPending(this.pendingState, docId, queryId);
                registered := true;
              }
            }
          }
        }
      }
    }

    method PickOverflowDoc(queryId: QueryId) returns (doc: seq<DocId>)
      requires this.Ready()
    {
      doc := [];
      if queryId in this.queries {
        var query := this.queries[queryId];
        if query.currentMatches >= query.spec.limit {
          var candidate := this.QueryDocAtOffset(query.spec, query.spec.limit);
          match candidate
          case NoDoc => {
          }
          case SomeDoc(docId) => {
            doc := [docId];
          }
        }
      }
    }

    method AddQueryDeferred(spec: QuerySpec) returns (queryId: QueryId, events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      ensures old(PendingConsistent(this.pendingState)) ==> PendingConsistent(this.pendingState)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
      ensures this.docs == old(this.docs)
      ensures this.store == old(this.store) && this.docIds == old(this.docIds)
      ensures old(this.DocumentsConsistent() && this.PendingDocsStored()) ==> this.PendingDocsStored()
      ensures queryId == old(this.nextQueryId)
      ensures this.nextQueryId == old(this.nextQueryId) + 1
      ensures this.queryIds == old(this.queryIds) + [queryId]
      ensures queryId in this.queries && this.queries[queryId].spec == spec
      modifies this
    {
      ghost var wasPendingConsistent := PendingConsistent(this.pendingState);
      ghost var wasQueryRegistryConsistent := this.QueryRegistryConsistent();
      ghost var werePendingQueriesRegistered := this.PendingQueriesRegistered();
      ghost var werePendingDocsValid := this.DocumentsConsistent() && this.PendingDocsStored();
      if wasQueryRegistryConsistent {
        assert this.nextQueryId !in this.queryIds;
        AppendUniquePreservesDistinct(this.queryIds, this.nextQueryId);
      }
      queryId := this.nextQueryId;
      this.nextQueryId := this.nextQueryId + 1;
      this.queryIds := this.queryIds + [queryId];
      var visible := TreapCollectRange(this.docs, spec.minScore, spec.maxScore, spec.limit);
      if werePendingDocsValid {
        TreapRangeMembersStored(this.docs, this.store, spec.minScore, spec.maxScore, spec.limit);
      }
      this.queries := this.queries[queryId := CleanQueryState(spec, |visible|)];
      ghost var addedQueries := this.queries;
      ghost var addedQueryIds := this.queryIds;
      ghost var followingQueryId := this.nextQueryId;
      var i := 0;
      while i < |visible|
        modifies this
        invariant 0 <= i <= |visible|
        invariant SumConsistent(this.docs)
        invariant wasPendingConsistent ==> PendingConsistent(this.pendingState)
        invariant wasQueryRegistryConsistent ==> this.QueryRegistryConsistent()
        invariant werePendingQueriesRegistered ==> this.PendingQueriesRegistered()
        invariant queryId in this.queries
        invariant werePendingDocsValid ==> this.PendingDocsStored()
        invariant werePendingDocsValid ==> (forall docId: DocId :: docId in visible ==> docId in this.store)
        invariant this.queries == addedQueries
        invariant this.queryIds == addedQueryIds
        invariant this.nextQueryId == followingQueryId
        invariant this.docs == old(this.docs)
        invariant this.store == old(this.store) && this.docIds == old(this.docIds)
      {
        if wasPendingConsistent {
          RegisterPreservesPendingConsistency(this.pendingState, visible[i], queryId);
        }
        this.pendingState := RegisterPending(this.pendingState, visible[i], queryId);
        i := i + 1;
      }
      events := [];
    }

    method RemoveQueryDeferred(queryId: QueryId) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      ensures old(PendingConsistent(this.pendingState)) ==> PendingConsistent(this.pendingState)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(PendingConsistent(this.pendingState) && this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
      ensures this.docs == old(this.docs)
      ensures this.store == old(this.store) && this.docIds == old(this.docIds)
      ensures old(this.PendingDocsStored()) ==> this.PendingDocsStored()
      ensures queryId !in this.queries
      ensures old(PendingConsistent(this.pendingState) && queryId in this.queries) ==> queryId !in this.pendingState.byQuery
      ensures old(PendingConsistent(this.pendingState) && queryId in this.queries) ==>
        (forall docId: DocId :: docId in this.pendingState.byDoc ==> queryId !in this.pendingState.byDoc[docId])
      modifies this
    {
      ghost var wasPendingConsistent := PendingConsistent(this.pendingState);
      ghost var wasQueryRegistryConsistent := this.QueryRegistryConsistent();
      ghost var werePendingQueriesRegistered := this.PendingQueriesRegistered();
      ghost var werePendingDocsStored := this.PendingDocsStored();
      if queryId in this.queries {
        if wasQueryRegistryConsistent {
          RemoveDocReferenceProperties(this.queryIds, queryId);
          RemoveQueryMatchesDocReference(this.queryIds, queryId);
        }
        this.queries := map key | key in this.queries && key != queryId :: this.queries[key];
        this.queryIds := RemoveQueryId(this.queryIds, queryId);
        if queryId in this.pendingState.byQuery {
          var pendingDocs := this.pendingState.byQuery[queryId];
          var i := 0;
          while i < |pendingDocs|
            modifies this
            invariant 0 <= i <= |pendingDocs|
            invariant SumConsistent(this.docs)
            invariant wasPendingConsistent ==> PendingConsistent(this.pendingState)
            invariant wasQueryRegistryConsistent ==> this.QueryRegistryConsistent()
            invariant wasPendingConsistent && werePendingQueriesRegistered ==>
              (forall otherQuery: QueryId :: otherQuery in this.pendingState.byQuery && otherQuery != queryId ==> otherQuery in this.queries)
            invariant werePendingDocsStored ==> this.PendingDocsStored()
            invariant queryId !in this.queries
            invariant this.docs == old(this.docs)
            invariant this.store == old(this.store) && this.docIds == old(this.docIds)
            invariant wasPendingConsistent && queryId in this.pendingState.byQuery ==>
              (forall docId: DocId :: docId in this.pendingState.byQuery[queryId] ==> docId in pendingDocs[i..])
          {
            if wasPendingConsistent {
              CancelPreservesPendingConsistency(this.pendingState, pendingDocs[i], queryId);
              CancelPendingPairMembership(this.pendingState, pendingDocs[i], queryId);
            }
            if wasPendingConsistent && werePendingQueriesRegistered {
              CancelAddsNoQueryKeys(this.pendingState, pendingDocs[i], queryId);
            }
            if werePendingDocsStored {
              CancelAddsNoDocKeys(this.pendingState, pendingDocs[i], queryId);
            }
            this.pendingState := CancelPending(this.pendingState, pendingDocs[i], queryId);
            i := i + 1;
          }
          if wasPendingConsistent && queryId in this.pendingState.byQuery {
            assert i == |pendingDocs|;
            assert pendingDocs[i..] == [];
            assert |this.pendingState.byQuery[queryId]| > 0;
            var remainingDoc := this.pendingState.byQuery[queryId][0];
            assert remainingDoc in pendingDocs[i..];
            assert false;
          }
        }
      }
      events := [];
    }

    method DrainPendingRetrievalsGrouped() returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      ensures PendingConsistent(this.pendingState)
      ensures this.PendingQueriesRegistered()
      ensures this.PendingDocsStored()
      ensures this.docs == old(this.docs)
      ensures this.store == old(this.store) && this.docIds == old(this.docIds)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures this.pendingState == EmptyPendingState()
      ensures events == (if |BuildGroupedRetrievals(old(this.pendingState).docOrder, old(this.pendingState).byDoc, old(this.store))| == 0 then []
        else [RetrievalEvent(BuildGroupedRetrievals(old(this.pendingState).docOrder, old(this.pendingState).byDoc, old(this.store)))])
      ensures |events| <= 1
      ensures |events| == 1 ==> (events[0].RetrievalEvent? &&
        (forall doc: RetrievalDoc :: doc in events[0].docs ==>
          old(doc.docId in this.pendingState.byDoc && doc.docId in this.store) &&
          doc.state == old(this.store[doc.docId]) && doc.queries == old(this.pendingState.byDoc[doc.docId])))
      ensures old(PendingConsistent(this.pendingState)) ==>
        (forall docId: DocId :: old(docId in this.pendingState.byDoc && docId in this.store) ==>
          |events| == 1 && events[0].RetrievalEvent? &&
          RetrievalDoc(docId, old(this.store[docId]), old(this.pendingState.byDoc[docId])) in events[0].docs)
      ensures old(PendingConsistent(this.pendingState)) && |events| > 0 ==>
        events[0].RetrievalEvent? &&
        (forall left, right :: 0 <= left < right < |events[0].docs| ==> events[0].docs[left].docId != events[0].docs[right].docId)
      modifies this
    {
      var docs := BuildGroupedRetrievals(this.pendingState.docOrder, this.pendingState.byDoc, this.store);
      GroupedRetrievalsSoundAndComplete(this.pendingState.docOrder, this.pendingState.byDoc, this.store);
      if PendingConsistent(this.pendingState) {
        GroupedRetrievalsHaveUniqueDocs(this.pendingState.docOrder, this.pendingState.byDoc, this.store);
      }
      this.pendingState := EmptyPendingState();
      EmptyPendingPairsAgree();
      if |docs| == 0 {
        events := [];
      } else {
        events := [RetrievalEvent(docs)];
      }
    }

    method ApplyDocChangeDeferred(id: DocId, oldState: MaybeDocState, newState: MaybeDocState) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      ensures old(PendingConsistent(this.pendingState)) ==> PendingConsistent(this.pendingState)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(ValidTreap(this.docs)) ==> ValidTreap(this.docs)
      ensures old(this.DocumentsConsistent() && ChangeMatchesStore(this.store, id, oldState)) ==> this.DocumentsConsistent()
      ensures old(this.DocumentsConsistent() && this.PendingDocsStored() && ChangeMatchesStore(this.store, id, oldState)) ==> this.PendingDocsStored()
      ensures |events| <= 1
      ensures |events| == 1 ==> (events[0].MatchEvent? && events[0].payload.docId == id &&
        events[0].payload.oldState == oldState && events[0].payload.newState == newState)
      ensures old(PendingConsistent(this.pendingState) && this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
      ensures old(PendingConsistent(this.pendingState)) ==> id !in this.pendingState.byDoc
      ensures old(PendingConsistent(this.pendingState)) ==>
        (forall queryId: QueryId :: queryId in this.pendingState.byQuery ==> id !in this.pendingState.byQuery[queryId])
      modifies this
    {
      ghost var wasPendingConsistent := PendingConsistent(this.pendingState);
      ghost var wasQueryRegistryConsistent := this.QueryRegistryConsistent();
      ghost var werePendingQueriesRegistered := this.PendingQueriesRegistered();
      ghost var wasValidTreap := ValidTreap(this.docs);
      ghost var wereDocumentsConsistent := this.DocumentsConsistent() && ChangeMatchesStore(this.store, id, oldState);
      ghost var werePendingDocsValid := wereDocumentsConsistent && this.PendingDocsStored();
      ghost var beforeTree := this.docs;
      ghost var beforeStore := this.store;
      if wereDocumentsConsistent {
        if newState.HasState? {
          ReplaceTreeEntryMatchesStore(beforeTree, beforeStore, id, newState.state);
          AppendUniquePreservesDistinct(this.docIds, id);
        } else if id in beforeStore {
          RemoveTreeEntryMatchesStore(beforeTree, beforeStore, id);
          RemoveDocReferenceProperties(this.docIds, id);
        } else {
          RemoveAbsentDocId(this.docIds, id);
        }
      }
      events := [];
      if oldState.HasState? && newState.HasState? && GetScore(oldState.state) == GetScore(newState.state) {
        this.store := this.store[id := newState.state];
        var covering := this.CollectVisibleQueriesInTreap(this.docs, id, newState.state);
        if wasPendingConsistent {
          ResolvePreservesPendingConsistency(this.pendingState, id);
          ResolvePendingDropsDoc(this.pendingState, id);
          ResolveAddsNoQueryKeys(this.pendingState, id);
        }
        this.pendingState := ResolvePendingForDoc(this.pendingState, id);
        if |covering| > 0 {
          events := [MatchEvent(MatchPayload(id, oldState, newState, covering, covering, []))];
        }
        return;
      }

      var docsBefore := this.docs;
      var oldMatches: seq<QueryId> := [];
      var newMatches: seq<QueryId> := [];
      var blockedCandidates: seq<QueryId> := [];

      if oldState.HasState? {
        oldMatches := this.CollectVisibleQueriesInTreap(docsBefore, id, oldState.state);
        if wasValidTreap {
          RemovePreservesValidTreap(this.docs, GetScore(oldState.state), id);
        }
        this.docs := Remove(this.docs, GetScore(oldState.state), id);
      }

      if newState.HasState? {
        if wasValidTreap {
          AddPreservesValidTreap(this.docs, GetScore(newState.state), id, PriorityFor(GetScore(newState.state), id));
        }
        this.docs := Add(this.docs, GetScore(newState.state), id, PriorityFor(GetScore(newState.state), id));
        this.store := this.store[id := newState.state];
        this.docIds := AppendDocIdIfMissing(this.docIds, id);
        newMatches := this.CollectVisibleQueriesInTreap(this.docs, id, newState.state);
      } else {
        this.store := RemoveStoredDoc(this.store, id);
        this.docIds := RemoveDocId(this.docIds, id);
      }

      var oldMatchMap: map<QueryId, bool> := map[];
      var newMatchMap: map<QueryId, bool> := map[];
      var i := 0;
      while i < |oldMatches|
        invariant 0 <= i <= |oldMatches|
      {
        oldMatchMap := oldMatchMap[oldMatches[i] := true];
        i := i + 1;
      }
      i := 0;
      while i < |newMatches|
        invariant 0 <= i <= |newMatches|
      {
        newMatchMap := newMatchMap[newMatches[i] := true];
        i := i + 1;
      }

      i := 0;
      while i < |oldMatches|
        modifies this
        invariant 0 <= i <= |oldMatches|
        invariant SumConsistent(this.docs)
        invariant wasPendingConsistent ==> PendingConsistent(this.pendingState)
        invariant wasQueryRegistryConsistent ==> this.QueryRegistryConsistent()
        invariant wasPendingConsistent && werePendingQueriesRegistered ==> this.PendingQueriesRegistered()
        invariant wasValidTreap ==> ValidTreap(this.docs)
        invariant wereDocumentsConsistent ==> this.DocumentsConsistent()
        invariant werePendingDocsValid ==> this.PendingDocsStoredExcept(id)
      {
        if oldMatches[i] in this.queries {
          var query := this.queries[oldMatches[i]];
          if query.currentMatches > 0 {
            this.queries := this.queries[oldMatches[i] := CleanQueryState(query.spec, query.currentMatches - 1)];
          }
        }
        i := i + 1;
      }

      i := 0;
      while i < |newMatches|
        invariant 0 <= i <= |newMatches|
        invariant SumConsistent(this.docs)
        invariant wasPendingConsistent ==> PendingConsistent(this.pendingState)
        invariant wasQueryRegistryConsistent ==> this.QueryRegistryConsistent()
        invariant wasPendingConsistent && werePendingQueriesRegistered ==> this.PendingQueriesRegistered()
        invariant wasValidTreap ==> ValidTreap(this.docs)
        invariant wereDocumentsConsistent ==> this.DocumentsConsistent()
        invariant werePendingDocsValid ==> this.PendingDocsStoredExcept(id)
      {
        if newMatches[i] in this.queries {
          var query := this.queries[newMatches[i]];
          var alreadyPending := id in this.pendingState.byDoc && ContainsQueryId(this.pendingState.byDoc[id], newMatches[i]);
          if alreadyPending {
          } else if query.currentMatches < query.spec.limit {
            this.queries := this.queries[newMatches[i] := CleanQueryState(query.spec, query.currentMatches + 1)];
          } else {
            blockedCandidates := blockedCandidates + [newMatches[i]];
          }
        }
        i := i + 1;
      }

      var evictions: seq<Eviction> := [];
      i := 0;
      while i < |oldMatches|
        invariant 0 <= i <= |oldMatches|
        invariant SumConsistent(this.docs)
        invariant wasPendingConsistent ==> PendingConsistent(this.pendingState)
        invariant wasQueryRegistryConsistent ==> this.QueryRegistryConsistent()
        invariant wasPendingConsistent && werePendingQueriesRegistered ==> this.PendingQueriesRegistered()
        invariant wasValidTreap ==> ValidTreap(this.docs)
        invariant wereDocumentsConsistent ==> this.DocumentsConsistent()
        invariant werePendingDocsValid ==> this.PendingDocsStoredExcept(id)
      {
        if !(oldMatches[i] in newMatchMap) {
          var gapRegistered := this.FillGap(oldMatches[i]);
        }
        i := i + 1;
      }

      i := 0;
      while i < |blockedCandidates|
        modifies this
        invariant 0 <= i <= |blockedCandidates|
        invariant SumConsistent(this.docs)
        invariant wasPendingConsistent ==> PendingConsistent(this.pendingState)
        invariant wasQueryRegistryConsistent ==> this.QueryRegistryConsistent()
        invariant wasPendingConsistent && werePendingQueriesRegistered ==> this.PendingQueriesRegistered()
        invariant wasValidTreap ==> ValidTreap(this.docs)
        invariant wereDocumentsConsistent ==> this.DocumentsConsistent()
        invariant werePendingDocsValid ==> this.PendingDocsStoredExcept(id)
      {
        if !(blockedCandidates[i] in oldMatchMap) {
          var evicted := this.PickOverflowDoc(blockedCandidates[i]);
          if |evicted| > 0 {
            evictions := evictions + [Eviction(blockedCandidates[i], evicted[0])];
            var cancelled := evicted[0] in this.pendingState.byDoc && ContainsQueryId(this.pendingState.byDoc[evicted[0]], blockedCandidates[i]);
            if wasPendingConsistent {
              CancelPreservesPendingConsistency(this.pendingState, evicted[0], blockedCandidates[i]);
              CancelAddsNoQueryKeys(this.pendingState, evicted[0], blockedCandidates[i]);
            }
            if werePendingDocsValid {
              CancelAddsNoDocKeys(this.pendingState, evicted[0], blockedCandidates[i]);
            }
            this.pendingState := CancelPending(this.pendingState, evicted[0], blockedCandidates[i]);
            if cancelled {
              var replacement := this.FillGap(blockedCandidates[i]);
            }
          }
        }
        i := i + 1;
      }

      if wasPendingConsistent {
        ResolvePreservesPendingConsistency(this.pendingState, id);
        ResolvePendingDropsDoc(this.pendingState, id);
        ResolveAddsNoQueryKeys(this.pendingState, id);
      }
      this.pendingState := ResolvePendingForDoc(this.pendingState, id);

      var payload := MatchPayload(id, oldState, newState, oldMatches, newMatches, evictions);
      if HasAnyMatchChange(payload) {
        events := [MatchEvent(payload)];
      }
    }

    method ProcessItemDeferred(item: StreamItem) returns (events: seq<DownstreamEvent>, queryId: QueryId)
      requires this.Ready()
      ensures this.Ready()
      ensures old(PendingConsistent(this.pendingState)) ==> PendingConsistent(this.pendingState)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(PendingConsistent(this.pendingState) && this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
      ensures old(this.RegistriesConsistent()) ==> this.RegistriesConsistent()
      ensures old(ValidTreap(this.docs)) ==> ValidTreap(this.docs)
      ensures old(this.DocumentsConsistent() && ItemMatchesStore(this.store, item)) ==> this.DocumentsConsistent()
      ensures old(this.DocumentsConsistent() && this.PendingDocsStored() && ItemMatchesStore(this.store, item)) ==> this.PendingDocsStored()
      ensures old(this.StructuralStateConsistent() && ItemMatchesStore(this.store, item)) ==> this.StructuralStateConsistent()
      ensures match item
        case QueryRemoveItem(removedId) =>
          old(PendingConsistent(this.pendingState) && removedId in this.queries) ==>
            removedId !in this.pendingState.byQuery &&
            (forall docId: DocId :: docId in this.pendingState.byDoc ==> removedId !in this.pendingState.byDoc[docId])
        case DocChangeItem(changedId, _, _) =>
          old(PendingConsistent(this.pendingState)) ==>
            changedId !in this.pendingState.byDoc &&
            (forall pendingQuery: QueryId :: pendingQuery in this.pendingState.byQuery ==> changedId !in this.pendingState.byQuery[pendingQuery])
        case QueryAddItem(_) => true
        case SeedDocsItem(_) => true
      ensures match item
        case QueryAddItem(spec) => queryId == old(this.nextQueryId) &&
          this.nextQueryId == old(this.nextQueryId) + 1 &&
          queryId in this.queries && this.queries[queryId].spec == spec
        case QueryRemoveItem(removedId) => removedId !in this.queries
        case DocChangeItem(_, _, _) => true
        case SeedDocsItem(_) => true
      modifies this
    {
      events := [];
      queryId := 0;
      match item
      case SeedDocsItem(docs) => {
        this.SeedDocs(docs);
      }
      case QueryAddItem(spec) => {
        queryId, events := this.AddQueryDeferred(spec);
      }
      case QueryRemoveItem(id) => {
        events := this.RemoveQueryDeferred(id);
      }
      case DocChangeItem(id, oldState, newState) => {
        events := this.ApplyDocChangeDeferred(id, oldState, newState);
      }
    }

    method ProcessItem(item: StreamItem) returns (events: seq<DownstreamEvent>, queryId: QueryId)
      requires this.Ready()
      ensures this.Ready()
      ensures PendingConsistent(this.pendingState)
      ensures this.PendingQueriesRegistered()
      ensures this.PendingDocsStored()
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(this.RegistriesConsistent()) ==> this.RegistriesConsistent()
      ensures old(ValidTreap(this.docs)) ==> ValidTreap(this.docs)
      ensures old(this.DocumentsConsistent() && ItemMatchesStore(this.store, item)) ==> this.DocumentsConsistent()
      ensures old(this.StructuralStateConsistent() && ItemMatchesStore(this.store, item)) ==> this.StructuralStateConsistent()
      modifies this
    {
      events, queryId := this.ProcessItemDeferred(item);
      var retrievalEvents := this.DrainPendingRetrievalsGrouped();
      events := events + retrievalEvents;
    }

    method ProcessItemWhenReady(item: StreamItem) returns (events: seq<DownstreamEvent>, queryId: QueryId)
      ensures old(this.Ready()) ==> this.Ready()
      ensures old(this.Ready()) ==> PendingConsistent(this.pendingState)
      ensures old(PendingConsistent(this.pendingState)) ==> PendingConsistent(this.pendingState)
      ensures old(this.QueryRegistryConsistent()) ==> this.QueryRegistryConsistent()
      ensures old(this.Ready()) ==> this.PendingQueriesRegistered()
      ensures old(this.Ready()) ==> this.PendingDocsStored()
      ensures old(PendingConsistent(this.pendingState) && this.PendingQueriesRegistered()) ==> this.PendingQueriesRegistered()
      ensures old(this.RegistriesConsistent()) ==> this.RegistriesConsistent()
      ensures old(ValidTreap(this.docs)) ==> ValidTreap(this.docs)
      ensures old(this.DocumentsConsistent() && ItemMatchesStore(this.store, item)) ==> this.DocumentsConsistent()
      ensures old(this.StructuralStateConsistent() && ItemMatchesStore(this.store, item)) ==> this.StructuralStateConsistent()
      modifies this
    {
      if this.Ready() {
        events, queryId := this.ProcessItem(item);
      } else {
        events := [];
        queryId := 0;
      }
    }
  }
}