include "CleanPendingRuntime.dfy"

module CleanLimitEngine {
  import opened DocsIndexModel
  import opened DocsIndexTreap
  import opened ThunderDbStack
  import opened CleanPendingRuntime

  datatype CleanQueryState = CleanQueryState(spec: QuerySpec, currentMatches: nat)

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
      ensures this.nextQueryId == 1
      ensures this.Ready()
    {
      this.docs := Empty;
      this.store := map[];
      this.docIds := [];
      this.queries := map[];
      this.queryIds := [];
      this.pendingState := EmptyPendingState();
      this.nextQueryId := 1;
    }

    predicate Ready()
      reads this
    {
      SumConsistent(this.docs)
    }

    method SeedDocs(input: seq<SeedDoc>)
      requires this.Ready()
      ensures this.Ready()
      modifies this
    {
      var i := 0;
      while i < |input|
        invariant 0 <= i <= |input|
        invariant SumConsistent(this.docs)
      {
        this.store := this.store[input[i].id := input[i].state];
        this.docIds := AppendDocIdIfMissing(this.docIds, input[i].id);
        this.docs := Add(this.docs, input[i].state.scoreValue, input[i].id, PriorityFor(input[i].state.scoreValue, input[i].id));
        i := i + 1;
      }
    }

    method QueryVisible(queryId: QueryId) returns (visible: seq<DocId>)
      requires this.Ready()
    {
      if queryId in this.queries {
        var spec := this.queries[queryId].spec;
        visible := TreapCollectRange(this.docs, spec.minScore, spec.maxScore, spec.limit);
      } else {
        visible := [];
      }
    }

    method QueryDocAtOffset(spec: QuerySpec, offset: nat) returns (doc: MaybeDocId)
      requires this.Ready()
    {
      var startRank := TreapRank(this.docs, spec.minScore, NoDoc);
      match TreapGetAtRank(this.docs, startRank + offset)
      case Missing => {
        doc := NoDoc;
      }
      case Found(score, id, pos) => {
        if score <= spec.maxScore {
          doc := SomeDoc(id);
        } else {
          doc := NoDoc;
        }
      }
    }

    method CollectVisibleQueriesInTreap(t: Treap, id: DocId, state: DocState) returns (matches: seq<QueryId>)
      requires SumConsistent(t)
      decreases *
    {
      matches := [];
      var i := 0;
      while i < |this.queryIds|
        invariant 0 <= i <= |this.queryIds|
        invariant SumConsistent(t)
      {
        var queryId := this.queryIds[i];
        if queryId in this.queries {
          var spec := this.queries[queryId].spec;
          if DocVisibleInTreap(t, spec, GetScore(state), id) {
            matches := matches + [queryId];
          }
        }
        i := i + 1;
      }
    }

    method FillGap(queryId: QueryId) returns (registered: bool)
      requires this.Ready()
      ensures this.Ready()
      modifies this
      decreases *
    {
      registered := false;
      if queryId in this.queries {
        var query := this.queries[queryId];
        if query.currentMatches < query.spec.limit {
          var offset := query.currentMatches;
          while !registered
            modifies this
            decreases *
            invariant SumConsistent(this.docs)
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
      modifies this
    {
      queryId := this.nextQueryId;
      this.nextQueryId := this.nextQueryId + 1;
      this.queryIds := this.queryIds + [queryId];
      var visible := TreapCollectRange(this.docs, spec.minScore, spec.maxScore, spec.limit);
      this.queries := this.queries[queryId := CleanQueryState(spec, |visible|)];
      var i := 0;
      while i < |visible|
        modifies this
        invariant 0 <= i <= |visible|
        invariant SumConsistent(this.docs)
      {
        this.pendingState := RegisterPending(this.pendingState, visible[i], queryId);
        i := i + 1;
      }
      events := [];
    }

    method RemoveQueryDeferred(queryId: QueryId) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      modifies this
    {
      if queryId in this.queries {
        this.queries := map key | key in this.queries && key != queryId :: this.queries[key];
        this.queryIds := RemoveQueryId(this.queryIds, queryId);
        if queryId in this.pendingState.byQuery {
          var pendingDocs := this.pendingState.byQuery[queryId];
          var i := 0;
          while i < |pendingDocs|
            modifies this
            invariant 0 <= i <= |pendingDocs|
            invariant SumConsistent(this.docs)
          {
            this.pendingState := CancelPending(this.pendingState, pendingDocs[i], queryId);
            i := i + 1;
          }
        }
      }
      events := [];
    }

    method DrainPendingRetrievalsGrouped() returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      modifies this
    {
      var docs := BuildGroupedRetrievals(this.pendingState.docOrder, this.pendingState.byDoc, this.store);
      this.pendingState := EmptyPendingState();
      if |docs| == 0 {
        events := [];
      } else {
        events := [RetrievalEvent(docs)];
      }
    }

    method ApplyDocChangeDeferred(id: DocId, oldState: MaybeDocState, newState: MaybeDocState) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      modifies this
      decreases *
    {
      events := [];
      if oldState.HasState? && newState.HasState? && GetScore(oldState.state) == GetScore(newState.state) {
        this.store := this.store[id := newState.state];
        var covering := this.CollectVisibleQueriesInTreap(this.docs, id, newState.state);
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
        this.docs := Remove(this.docs, GetScore(oldState.state), id);
      }

      if newState.HasState? {
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
      {
        if !(blockedCandidates[i] in oldMatchMap) {
          var evicted := this.PickOverflowDoc(blockedCandidates[i]);
          if |evicted| > 0 {
            evictions := evictions + [Eviction(blockedCandidates[i], evicted[0])];
            var cancelled := evicted[0] in this.pendingState.byDoc && ContainsQueryId(this.pendingState.byDoc[evicted[0]], blockedCandidates[i]);
            this.pendingState := CancelPending(this.pendingState, evicted[0], blockedCandidates[i]);
            if cancelled {
              var replacement := this.FillGap(blockedCandidates[i]);
            }
          }
        }
        i := i + 1;
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
      modifies this
      decreases *
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
      modifies this
      decreases *
    {
      events, queryId := this.ProcessItemDeferred(item);
      var retrievalEvents := this.DrainPendingRetrievalsGrouped();
      events := events + retrievalEvents;
    }

    method ProcessItemWhenReady(item: StreamItem) returns (events: seq<DownstreamEvent>, queryId: QueryId)
      ensures old(this.Ready()) ==> this.Ready()
      modifies this
      decreases *
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