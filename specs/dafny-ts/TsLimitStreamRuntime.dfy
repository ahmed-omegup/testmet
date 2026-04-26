include "TsLimitQueriesRuntime.dfy"
include "TsRetrievalRuntime.dfy"

module TsLimitStreamRuntime {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsDocsRuntime
  import opened TsLimitQueriesRuntime
  import opened TsRetrievalRuntime

  datatype LimitStreamState = LimitStreamState(
    store: map<DocId, DocState>,
    queries: LimitQueriesState,
    retrieval: RetrievalWorkerState)

  datatype StreamStep = StreamStep(state: LimitStreamState, events: seq<DownstreamEvent>)
  datatype OverflowResult = OverflowResult(state: LimitStreamState, evictions: seq<Eviction>)

  function EmptyLimitStreamState(): LimitStreamState {
    LimitStreamState(map[], EmptyLimitQueriesState(), EmptyWorkerState())
  }

  predicate LimitStreamConsistent(state: LimitStreamState) {
    LimitQueriesConsistent(state.queries) &&
    WorkerConsistent(state.retrieval)
  }

  function SetQueries(state: LimitStreamState, queries: LimitQueriesState): LimitStreamState
    ensures LimitQueriesConsistent(queries) && WorkerConsistent(state.retrieval) ==> LimitStreamConsistent(SetQueries(state, queries))
  {
    LimitStreamState(state.store, queries, state.retrieval)
  }

  function SetRetrieval(state: LimitStreamState, retrieval: RetrievalWorkerState): LimitStreamState {
    LimitStreamState(state.store, state.queries, retrieval)
  }

  function SetStore(state: LimitStreamState, store: map<DocId, DocState>): LimitStreamState {
    LimitStreamState(store, state.queries, state.retrieval)
  }

  function RegisterIfAllowed(state: LimitStreamState, docId: DocId, queryId: QueryId): LimitStreamState {
    if CanRegister(state.retrieval, docId, queryId)
    then SetRetrieval(state, Register(state.retrieval, docId, queryId))
    else state
  }

  function NotifyRetrievalResolved(state: LimitStreamState, docId: DocId): LimitStreamState
    requires LimitQueriesConsistent(state.queries)
  {
    LimitStreamState(state.store, ResolvePendingForDoc(state.queries, docId), ResolveDoc(state.retrieval, docId).state)
  }

  function RegisterDocsForQuery(state: LimitStreamState, docs: seq<DocId>, queryId: QueryId): LimitStreamState
    decreases |docs|
  {
    if |docs| == 0 then state
    else RegisterDocsForQuery(RegisterIfAllowed(state, docs[0], queryId), docs[1..], queryId)
  }

  function SeedDocsStore(store: map<DocId, DocState>, docs: seq<SeedDoc>): map<DocId, DocState>
    decreases |docs|
  {
    if |docs| == 0 then store
    else SeedDocsStore(store[docs[0].id := docs[0].state], docs[1..])
  }

  function SeedDocsQueries(queries: LimitQueriesState, docs: seq<SeedDoc>): LimitQueriesState
    requires LimitQueriesConsistent(queries)
    ensures LimitQueriesConsistent(SeedDocsQueries(queries, docs))
    decreases |docs|
  {
    if |docs| == 0 then queries
    else 
    var newState := LimitQueriesState(AddDoc(queries.docs, GetScore(docs[0].state), docs[0].id), queries.queries, queries.nextId, queries.infos, queries.baseScores, queries.pendingByQuery, queries.pendingByDoc);
    SeedDocsQueries(newState, docs[1..])
  }

  function FilterMissing(ids: seq<QueryId>, keep: seq<QueryId>): seq<QueryId>
    decreases |ids|
  {
    if |ids| == 0 then []
    else if ContainsQueryId(keep, ids[0]) then FilterMissing(ids[1..], keep)
    else [ids[0]] + FilterMissing(ids[1..], keep)
  }

  function HandleLostQueries(state: LimitStreamState, queries: seq<QueryId>): LimitStreamState
    requires LimitQueriesConsistent(state.queries)
    ensures LimitQueriesConsistent(HandleLostQueries(state, queries).queries)
    decreases |queries|
  {
    if |queries| == 0 then state
    else
      var gap := FillGap(state.queries, queries[0]);
      var nextState := SetQueries(state, gap.state);
      var registered :=
        match gap.doc
        case NoDoc => nextState
        case SomeDoc(docId) => RegisterIfAllowed(nextState, docId, queries[0]);
      HandleLostQueries(registered, queries[1..])
  }

  function HandleOverflowQueries(state: LimitStreamState, queries: seq<QueryId>): OverflowResult
    requires LimitQueriesConsistent(state.queries)
    ensures LimitQueriesConsistent(HandleOverflowQueries(state, queries).state.queries)
    decreases |queries|
  {
    if |queries| == 0 then OverflowResult(state, [])
    else
      var queryId := queries[0];
      var overflowDoc := PickOverflowDoc(state.queries, queryId);
      match overflowDoc
      case NoDoc => HandleOverflowQueries(state, queries[1..])
      case SomeDoc(docId) =>
        var cancelledPending := CancelPendingForQuery(state.queries, docId, queryId);
        var retrievalCancelled := Cancel(state.retrieval, docId, queryId);
        var state1 := LimitStreamState(state.store, cancelledPending.state, retrievalCancelled.state);
        var state2 :=
          if cancelledPending.changed then
            var gap := FillGap(state1.queries, queryId);
            var gapState := SetQueries(state1, gap.state);
            match gap.doc
            case NoDoc => gapState
            case SomeDoc(replacement) => RegisterIfAllowed(gapState, replacement, queryId)
          else state1;
        var rest := HandleOverflowQueries(state2, queries[1..]);
        OverflowResult(rest.state, [Eviction(queryId, docId)] + rest.evictions)
  }

  function MatchEventIfAny(docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, matchesOld: seq<QueryId>, matchesNew: seq<QueryId>, evictions: seq<Eviction>): seq<DownstreamEvent> {
    if |matchesOld| == 0 && |matchesNew| == 0 && |evictions| == 0 then []
    else [MatchEvent(MatchPayload(docId, oldState, newState, matchesOld, matchesNew, evictions))]
  }

  function HandleDocChange(state: LimitStreamState, docId: DocId, oldState: MaybeDocState, newState: MaybeDocState): StreamStep
    requires LimitStreamConsistent(state)
  {
    match oldState
    case NoState =>
      HandleDocChangeNoOld(state, docId, newState)
    case HasState(oldDocState) =>
      match newState
      case HasState(nextDocState) =>
        if GetScore(oldDocState) == GetScore(nextDocState) then
          var covering := GetQueriesCovering(state.queries, GetScore(oldDocState), SomeDoc(docId));
          StreamStep(NotifyRetrievalResolved(state, docId), [MatchEvent(MatchPayload(docId, oldState, newState, covering, covering, []))])
        else
          HandleDocChangeGeneral(state, docId, oldState, newState, GetScore(oldDocState), HasState(nextDocState))
      case NoState =>
        HandleDocChangeGeneral(state, docId, oldState, newState, GetScore(oldDocState), NoState)
  }

  function HandleDocChangeNoOld(state: LimitStreamState, docId: DocId, newState: MaybeDocState): StreamStep
    requires LimitStreamConsistent(state)
  {
    match newState
    case NoState => StreamStep(NotifyRetrievalResolved(state, docId), [])
    case HasState(nextDocState) =>
      var added := AddDocument(state.queries, GetScore(nextDocState), docId);
      var state1 := SetQueries(state, added.state);
      var overflow := HandleOverflowQueries(state1, FilterMissing(added.blocked, []));
      var state2 := NotifyRetrievalResolved(overflow.state, docId);
      StreamStep(state2, MatchEventIfAny(docId, NoState, newState, [], added.matched, overflow.evictions))
  }

  function HandleDocChangeGeneral(state: LimitStreamState, docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, oldScore: Score, nextDocState: MaybeDocState): StreamStep
    requires LimitStreamConsistent(state)
  {
    var removed := RemoveDocument(state.queries, oldScore, docId);
    var state1 := SetQueries(state, removed.state);
    var added :=
      match nextDocState
      case NoState => AddDocumentResult(state1.queries, [], [])
      case HasState(nextState) => AddDocument(state1.queries, GetScore(nextState), docId);
    var state2 := SetQueries(state1, added.state);
    var lostQueries := FilterMissing(removed.removed, added.matched);
    var state3 := HandleLostQueries(state2, lostQueries);
    var overflowQueries := FilterMissing(added.blocked, removed.removed);
    var overflow := HandleOverflowQueries(state3, overflowQueries);
    var state4 := NotifyRetrievalResolved(overflow.state, docId);
    StreamStep(state4, MatchEventIfAny(docId, oldState, newState, removed.removed, added.matched, overflow.evictions))
  }

  function HandleQueryAdd(state: LimitStreamState, spec: QuerySpec): StreamStep
    requires LimitStreamConsistent(state)
  {
    var added := TsLimitQueriesRuntime.AddQuery(state.queries, spec.minScore, spec.limit, spec.maxScore);
    var state1 := SetQueries(state, added.state);
    var seedDocs := CollectRangeDocs(state.queries.docs, spec.minScore, spec.maxScore, spec.limit);
    StreamStep(RegisterDocsForQuery(state1, seedDocs, added.queryId), [])
  }

  function HandleQueryRemove(state: LimitStreamState, queryId: QueryId): StreamStep
    requires LimitStreamConsistent(state)
  {
    var removed := TsLimitQueriesRuntime.RemoveQuery(state.queries, queryId);
    StreamStep(SetQueries(state, removed.state), [])
  }

  function HandleSeedDocs(state: LimitStreamState, docs: seq<SeedDoc>): StreamStep
    requires LimitStreamConsistent(state)
  {
    StreamStep(LimitStreamState(SeedDocsStore(state.store, docs), SeedDocsQueries(state.queries, docs), state.retrieval), [])
  }

  function HandleItem(state: LimitStreamState, item: StreamItem): StreamStep
    requires LimitStreamConsistent(state)
  {
    match item
    case QueryAddItem(spec) => HandleQueryAdd(state, spec)
    case QueryRemoveItem(id) => HandleQueryRemove(state, id)
    case SeedDocsItem(docs) => HandleSeedDocs(state, docs)
    case DocChangeItem(id, oldState, newState) =>
      var nextStore :=
        match newState
        case NoState => RemoveStoredDoc(state.store, id)
        case HasState(docState) => PutStoredDoc(state.store, id, docState);
      HandleDocChange(SetStore(state, nextStore), id, oldState, newState)
  }

  function ResolveDeliveredDocs(queries: LimitQueriesState, docs: seq<RetrievalDoc>): LimitQueriesState
    requires LimitQueriesConsistent(queries)
    ensures LimitQueriesConsistent(ResolveDeliveredDocs(queries, docs))
    decreases |docs|
  {
    if |docs| == 0 then queries
    else ResolveDeliveredDocs(ResolvePendingForDoc(queries, docs[0].docId), docs[1..])
  }

  function DrainRetrievalCycle(state: LimitStreamState): StreamStep
    requires LimitStreamConsistent(state)
  {
    if !HasPendingWork(state.retrieval) then StreamStep(state, [])
    else
      var processing := BeginCycle(state.retrieval);
      var payload := BuildPayload(processing, state.store);
      var finished := FinishCycle(processing);
      var nextQueries := ResolveDeliveredDocs(state.queries, payload);
      var nextState := LimitStreamState(state.store, nextQueries, finished);
      if |payload| == 0 then StreamStep(nextState, [])
      else StreamStep(nextState, [RetrievalEvent(payload)])
  }

  function Stop(state: LimitStreamState): LimitStreamState {
    SetRetrieval(state, TsRetrievalRuntime.Stop(state.retrieval))
  }
}