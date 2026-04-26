// Dafny program TsLimitStreamSmoke.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.11.0.0
// Command-line arguments: run specs/dafny-ts/TsLimitStreamSmoke.dfy --no-verify --allow-warnings
// TsLimitStreamSmoke.dfy


module TsLimitStreamSmoke {
  method Main(_noArgsParameter: seq<seq<char>>)
  {
    var state := EmptyLimitStreamState();
    expect LimitStreamConsistent(state), ""expectation violation"";
    var seeded := HandleItem(state, SeedDocsItem([SeedDoc(1, DocState(10)), SeedDoc(2, DocState(20)), SeedDoc(3, DocState(30))]));
    state := seeded.state;
    expect seeded.events == [], ""expectation violation"";
    expect state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)], ""expectation violation"";
    expect state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)], ""expectation violation"";
    var added := HandleItem(state, QueryAddItem(QuerySpec(0, 100, 2)));
    state := added.state;
    expect added.events == [], ""expectation violation"";
    expect 1 in state.queries.infos, ""expectation violation"";
    expect state.queries.infos[1].currentMatches == 2, ""expectation violation"";
    expect state.retrieval.pendingOrder == [1, 2], ""expectation violation"";
    var retrieval := DrainRetrievalCycle(state);
    state := retrieval.state;
    expect retrieval.events == [RetrievalEvent([RetrievalDoc(1, DocState(10), [1]), RetrievalDoc(2, DocState(20), [1])])], ""expectation violation"";
    expect state.retrieval.pendingOrder == [], ""expectation violation"";
    var removed := HandleItem(state, DocChangeItem(1, HasState(DocState(10)), NoState));
    state := removed.state;
    expect removed.events == [MatchEvent(MatchPayload(1, HasState(DocState(10)), NoState, [1], [], []))], ""expectation violation"";
    expect state.queries.infos[1].currentMatches == 2, ""expectation violation"";
    expect state.queries.pendingByQuery[1] == [3], ""expectation violation"";
    expect state.retrieval.pendingOrder == [3], ""expectation violation"";
    retrieval := DrainRetrievalCycle(state);
    state := retrieval.state;
    expect retrieval.events == [RetrievalEvent([RetrievalDoc(3, DocState(30), [1])])], ""expectation violation"";
    expect !(1 in state.queries.pendingByQuery), ""expectation violation"";
    var changed := HandleItem(state, DocChangeItem(0, NoState, HasState(DocState(5))));
    state := changed.state;
    expect changed.events == [MatchEvent(MatchPayload(0, NoState, HasState(DocState(5)), [], [1], [Eviction(1, 3)]))], ""expectation violation"";
    expect state.retrieval.pendingOrder == [], ""expectation violation"";
    expect !(1 in state.queries.pendingByQuery), ""expectation violation"";
    var removedQuery := HandleItem(state, QueryRemoveItem(1));
    state := removedQuery.state;
    expect removedQuery.events == [], ""expectation violation"";
    expect !(1 in state.queries.infos), ""expectation violation"";
    print ""ts-limit-stream-smoke passed\n"";
  }

  import opened DocsIndexModel

  import opened ThunderDbStack

  import opened TsLimitStreamRuntime
}

module TsLimitStreamLemmas {
  lemma EmptyStreamIsConsistent()
    ensures LimitStreamConsistent(EmptyLimitStreamState())
  {
  }

  lemma DrainWithoutPendingIsStable(state: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires !HasPendingWork(state.retrieval)
    ensures DrainRetrievalCycle(state) == StreamStep(state, [])
    decreases state
  {
  }

  import opened DocsIndexModel

  import opened ThunderDbStack

  import opened TsLimitStreamRuntime

  import opened TsRetrievalRuntime
}

module TsLimitStreamRuntime {
  function EmptyLimitStreamState(): LimitStreamState
  {
    LimitStreamState(map[], EmptyLimitQueriesState(), EmptyWorkerState())
  }

  predicate LimitStreamConsistent(state: LimitStreamState)
    decreases state
  {
    LimitQueriesConsistent(state.queries) &&
    WorkerConsistent(state.retrieval)
  }

  function SetQueries(state: LimitStreamState, queries: LimitQueriesState): LimitStreamState
    ensures LimitQueriesConsistent(queries) && WorkerConsistent(state.retrieval) ==> LimitStreamConsistent(SetQueries(state, queries))
    decreases state, queries
  {
    LimitStreamState(state.store, queries, state.retrieval)
  }

  function SetRetrieval(state: LimitStreamState, retrieval: RetrievalWorkerState): LimitStreamState
    decreases state, retrieval
  {
    LimitStreamState(state.store, state.queries, retrieval)
  }

  function SetStore(state: LimitStreamState, store: map<DocId, DocState>): LimitStreamState
    decreases state, store
  {
    LimitStreamState(store, state.queries, state.retrieval)
  }

  function RegisterIfAllowed(state: LimitStreamState, docId: DocId, queryId: QueryId): LimitStreamState
    decreases state, docId, queryId
  {
    if CanRegister(state.retrieval, docId, queryId) then
      SetRetrieval(state, Register(state.retrieval, docId, queryId))
    else
      state
  }

  function NotifyRetrievalResolved(state: LimitStreamState, docId: DocId): LimitStreamState
    requires LimitQueriesConsistent(state.queries)
    decreases state, docId
  {
    LimitStreamState(state.store, ResolvePendingForDoc(state.queries, docId), ResolveDoc(state.retrieval, docId).state)
  }

  function RegisterDocsForQuery(state: LimitStreamState, docs: seq<DocId>, queryId: QueryId): LimitStreamState
    decreases |docs|
  {
    if |docs| == 0 then
      state
    else
      RegisterDocsForQuery(RegisterIfAllowed(state, docs[0], queryId), docs[1..], queryId)
  }

  function SeedDocsStore(store: map<DocId, DocState>, docs: seq<SeedDoc>): map<DocId, DocState>
    decreases |docs|
  {
    if |docs| == 0 then
      store
    else
      SeedDocsStore(store[docs[0].id := docs[0].state], docs[1..])
  }

  function SeedDocsQueries(queries: LimitQueriesState, docs: seq<SeedDoc>): LimitQueriesState
    requires LimitQueriesConsistent(queries)
    ensures LimitQueriesConsistent(SeedDocsQueries(queries, docs))
    decreases |docs|
  {
    if |docs| == 0 then
      queries
    else
      var newState: LimitQueriesState := LimitQueriesState(AddDoc(queries.docs, GetScore(docs[0].state), docs[0].id), queries.queries, queries.nextId, queries.infos, queries.baseScores, queries.pendingByQuery, queries.pendingByDoc); SeedDocsQueries(newState, docs[1..])
  }

  function FilterMissing(ids: seq<QueryId>, keep: seq<QueryId>): seq<QueryId>
    decreases |ids|
  {
    if |ids| == 0 then
      []
    else if ContainsQueryId(keep, ids[0]) then
      FilterMissing(ids[1..], keep)
    else
      [ids[0]] + FilterMissing(ids[1..], keep)
  }

  function HandleLostQueries(state: LimitStreamState, queries: seq<QueryId>): LimitStreamState
    requires LimitQueriesConsistent(state.queries)
    ensures LimitQueriesConsistent(HandleLostQueries(state, queries).queries)
    decreases |queries|
  {
    if |queries| == 0 then
      state
    else
      var gap: GapFillResult := FillGap(state.queries, queries[0]); var nextState: LimitStreamState := SetQueries(state, gap.state); var registered: LimitStreamState := match gap.doc case NoDoc() => nextState case SomeDoc(docId) => RegisterIfAllowed(nextState, docId, queries[0]); HandleLostQueries(registered, queries[1..])
  }

  function HandleOverflowQueries(state: LimitStreamState, queries: seq<QueryId>): OverflowResult
    requires LimitQueriesConsistent(state.queries)
    ensures LimitQueriesConsistent(HandleOverflowQueries(state, queries).state.queries)
    decreases |queries|
  {
    if |queries| == 0 then
      OverflowResult(state, [])
    else
      var queryId: int := queries[0]; var overflowDoc: MaybeDocId := PickOverflowDoc(state.queries, queryId); match overflowDoc case NoDoc() => HandleOverflowQueries(state, queries[1..]) case SomeDoc(docId) => var cancelledPending: StateChange := CancelPendingForQuery(state.queries, docId, queryId); var retrievalCancelled: StateChange := Cancel(state.retrieval, docId, queryId); var state1: LimitStreamState := LimitStreamState(state.store, cancelledPending.state, retrievalCancelled.state); var state2: LimitStreamState := if cancelledPending.changed then var gap: GapFillResult := FillGap(state1.queries, queryId); var gapState: LimitStreamState := SetQueries(state1, gap.state); match gap.doc case NoDoc() => gapState case SomeDoc(replacement) => RegisterIfAllowed(gapState, replacement, queryId) else state1; var rest: OverflowResult := HandleOverflowQueries(state2, queries[1..]); OverflowResult(rest.state, [Eviction(queryId, docId)] + rest.evictions)
  }

  function MatchEventIfAny(docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, matchesOld: seq<QueryId>, matchesNew: seq<QueryId>, evictions: seq<Eviction>): seq<DownstreamEvent>
    decreases docId, oldState, newState, matchesOld, matchesNew, evictions
  {
    if |matchesOld| == 0 && |matchesNew| == 0 && |evictions| == 0 then
      []
    else
      [MatchEvent(MatchPayload(docId, oldState, newState, matchesOld, matchesNew, evictions))]
  }

  function HandleDocChange(state: LimitStreamState, docId: DocId, oldState: MaybeDocState, newState: MaybeDocState): StreamStep
    requires LimitStreamConsistent(state)
    decreases state, docId, oldState, newState
  {
    match oldState
    case NoState() =>
      HandleDocChangeNoOld(state, docId, newState)
    case HasState(oldDocState) =>
      match newState
      case HasState(nextDocState) =>
        if GetScore(oldDocState) == GetScore(nextDocState) then
          var covering: seq<QueryId> := GetQueriesCovering(state.queries, GetScore(oldDocState), SomeDoc(docId));
          StreamStep(NotifyRetrievalResolved(state, docId), [MatchEvent(MatchPayload(docId, oldState, newState, covering, covering, []))])
        else
          HandleDocChangeGeneral(state, docId, oldState, newState, GetScore(oldDocState), HasState(nextDocState))
      case NoState() =>
        HandleDocChangeGeneral(state, docId, oldState, newState, GetScore(oldDocState), NoState)
  }

  function HandleDocChangeNoOld(state: LimitStreamState, docId: DocId, newState: MaybeDocState): StreamStep
    requires LimitStreamConsistent(state)
    decreases state, docId, newState
  {
    match newState
    case NoState() =>
      StreamStep(NotifyRetrievalResolved(state, docId), [])
    case HasState(nextDocState) =>
      var added: AddDocumentResult := AddDocument(state.queries, GetScore(nextDocState), docId);
      var state1: LimitStreamState := SetQueries(state, added.state);
      var overflow: OverflowResult := HandleOverflowQueries(state1, FilterMissing(added.blocked, []));
      var state2: LimitStreamState := NotifyRetrievalResolved(overflow.state, docId);
      StreamStep(state2, MatchEventIfAny(docId, NoState, newState, [], added.matched, overflow.evictions))
  }

  function HandleDocChangeGeneral(state: LimitStreamState, docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, oldScore: Score, nextDocState: MaybeDocState): StreamStep
    requires LimitStreamConsistent(state)
    decreases state, docId, oldState, newState, oldScore, nextDocState
  {
    var removed: RemoveDocumentResult := RemoveDocument(state.queries, oldScore, docId);
    var state1: LimitStreamState := SetQueries(state, removed.state);
    var added: AddDocumentResult := match nextDocState case NoState() => AddDocumentResult(state1.queries, [], []) case HasState(nextState) => AddDocument(state1.queries, GetScore(nextState), docId);
    var state2: LimitStreamState := SetQueries(state1, added.state);
    var lostQueries: seq<QueryId> := FilterMissing(removed.removed, added.matched);
    var state3: LimitStreamState := HandleLostQueries(state2, lostQueries);
    var overflowQueries: seq<QueryId> := FilterMissing(added.blocked, removed.removed);
    var overflow: OverflowResult := HandleOverflowQueries(state3, overflowQueries);
    var state4: LimitStreamState := NotifyRetrievalResolved(overflow.state, docId);
    StreamStep(state4, MatchEventIfAny(docId, oldState, newState, removed.removed, added.matched, overflow.evictions))
  }

  function HandleQueryAdd(state: LimitStreamState, spec: QuerySpec): StreamStep
    requires LimitStreamConsistent(state)
    decreases state, spec
  {
    var added: QueryAddResult := TsLimitQueriesRuntime.AddQuery(state.queries, spec.minScore, spec.limit, spec.maxScore);
    var state1: LimitStreamState := SetQueries(state, added.state);
    var seedDocs: seq<DocId> := CollectRangeDocs(state.queries.docs, spec.minScore, spec.maxScore, spec.limit);
    StreamStep(RegisterDocsForQuery(state1, seedDocs, added.queryId), [])
  }

  function HandleQueryRemove(state: LimitStreamState, queryId: QueryId): StreamStep
    requires LimitStreamConsistent(state)
    decreases state, queryId
  {
    var removed: StateChange := TsLimitQueriesRuntime.RemoveQuery(state.queries, queryId);
    StreamStep(SetQueries(state, removed.state), [])
  }

  function HandleSeedDocs(state: LimitStreamState, docs: seq<SeedDoc>): StreamStep
    requires LimitStreamConsistent(state)
    decreases state, docs
  {
    StreamStep(LimitStreamState(SeedDocsStore(state.store, docs), SeedDocsQueries(state.queries, docs), state.retrieval), [])
  }

  function HandleItem(state: LimitStreamState, item: StreamItem): StreamStep
    requires LimitStreamConsistent(state)
    decreases state, item
  {
    match item
    case QueryAddItem(spec) =>
      HandleQueryAdd(state, spec)
    case QueryRemoveItem(id) =>
      HandleQueryRemove(state, id)
    case SeedDocsItem(docs) =>
      HandleSeedDocs(state, docs)
    case DocChangeItem(id, oldState, newState) =>
      var nextStore: map<DocId, DocState> := match newState case NoState() => RemoveStoredDoc(state.store, id) case HasState(docState) => PutStoredDoc(state.store, id, docState);
      HandleDocChange(SetStore(state, nextStore), id, oldState, newState)
  }

  function ResolveDeliveredDocs(queries: LimitQueriesState, docs: seq<RetrievalDoc>): LimitQueriesState
    requires LimitQueriesConsistent(queries)
    ensures LimitQueriesConsistent(ResolveDeliveredDocs(queries, docs))
    decreases |docs|
  {
    if |docs| == 0 then
      queries
    else
      ResolveDeliveredDocs(ResolvePendingForDoc(queries, docs[0].docId), docs[1..])
  }

  function DrainRetrievalCycle(state: LimitStreamState): StreamStep
    requires LimitStreamConsistent(state)
    decreases state
  {
    if !HasPendingWork(state.retrieval) then
      StreamStep(state, [])
    else
      var processing: RetrievalWorkerState := BeginCycle(state.retrieval); var payload: seq<RetrievalDoc> := BuildPayload(processing, state.store); var finished: RetrievalWorkerState := FinishCycle(processing); var nextQueries: LimitQueriesState := ResolveDeliveredDocs(state.queries, payload); var nextState: LimitStreamState := LimitStreamState(state.store, nextQueries, finished); if |payload| == 0 then StreamStep(nextState, []) else StreamStep(nextState, [RetrievalEvent(payload)])
  }

  function Stop(state: LimitStreamState): LimitStreamState
    decreases state
  {
    SetRetrieval(state, TsRetrievalRuntime.Stop(state.retrieval))
  }

  import opened DocsIndexModel

  import opened ThunderDbStack

  import opened TsDocsRuntime

  import opened TsLimitQueriesRuntime

  import opened TsRetrievalRuntime

  datatype LimitStreamState = LimitStreamState(store: map<DocId, DocState>, queries: LimitQueriesState, retrieval: RetrievalWorkerState)

  datatype StreamStep = StreamStep(state: LimitStreamState, events: seq<DownstreamEvent>)

  datatype OverflowResult = OverflowResult(state: LimitStreamState, evictions: seq<Eviction>)
}

module TsRetrievalRuntime {
  function EmptyWorkerState(): RetrievalWorkerState
  {
    RetrievalWorkerState(map[], [], map[], [], false)
  }

  function RemoveQueryId(ids: seq<QueryId>, id: QueryId): seq<QueryId>
    decreases ids, id
  {
    if |ids| == 0 then
      []
    else if ids[0] == id then
      ids[1..]
    else
      [ids[0]] + RemoveQueryId(ids[1..], id)
  }

  function UniqueQueryIds(ids: seq<QueryId>): bool
    decreases ids
  {
    if |ids| == 0 then
      true
    else
      !ContainsQueryId(ids[1..], ids[0]) && UniqueQueryIds(ids[1..])
  }

  predicate RegistryConsistent(batch: map<DocId, seq<QueryId>>, order: seq<DocId>)
    decreases batch, order
  {
    UniqueDocIds(order) &&
    (forall docId: int {:trigger ContainsId(order, docId)} {:trigger docId in batch} :: 
      docId in batch ==>
        ContainsId(order, docId)) &&
    forall docId: int {:trigger batch[docId]} {:trigger docId in batch} :: 
      docId in batch ==>
        UniqueQueryIds(batch[docId])
  }

  predicate WorkerConsistent(state: RetrievalWorkerState)
    decreases state
  {
    RegistryConsistent(state.pendingBatch, state.pendingOrder) &&
    RegistryConsistent(state.processingBatch, state.processingOrder)
  }

  function CanRegister(state: RetrievalWorkerState, docId: DocId, queryId: QueryId): bool
    decreases state, docId, queryId
  {
    !(docId in state.processingBatch && ContainsQueryId(state.processingBatch[docId], queryId))
  }

  function Register(state: RetrievalWorkerState, docId: DocId, queryId: QueryId): RetrievalWorkerState
    requires CanRegister(state, docId, queryId)
    decreases state, docId, queryId
  {
    var nextQueries: seq<QueryId> := if docId in state.pendingBatch then AppendQueryIdUnique(state.pendingBatch[docId], queryId) else [queryId];
    var nextOrder: seq<DocId> := if docId in state.pendingBatch then state.pendingOrder else AppendDocIdIfMissing(state.pendingOrder, docId);
    RetrievalWorkerState(state.pendingBatch[docId := nextQueries], nextOrder, state.processingBatch, state.processingOrder, state.stopped)
  }

  function Cancel(state: RetrievalWorkerState, docId: DocId, queryId: QueryId): StateChange
    decreases state, docId, queryId
  {
    if docId in state.pendingBatch then
      var removed: bool := ContainsQueryId(state.pendingBatch[docId], queryId);
      var nextQueries: seq<QueryId> := RemoveQueryId(state.pendingBatch[docId], queryId);
      var nextBatch: map<int, seq<QueryId>> := if removed && |nextQueries| == 0 then map key: int {:trigger state.pendingBatch[key]} {:trigger key in state.pendingBatch} | key in state.pendingBatch && key != docId :: state.pendingBatch[key] else if removed then state.pendingBatch[docId := nextQueries] else state.pendingBatch;
      var nextOrder: seq<DocId> := if removed && !(docId in nextBatch) then RemoveDocId(state.pendingOrder, docId) else state.pendingOrder;
      StateChange(RetrievalWorkerState(nextBatch, nextOrder, state.processingBatch, state.processingOrder, state.stopped), removed)
    else if docId in state.processingBatch then
      var removed: bool := ContainsQueryId(state.processingBatch[docId], queryId);
      var nextQueries: seq<QueryId> := RemoveQueryId(state.processingBatch[docId], queryId);
      var nextBatch: map<int, seq<QueryId>> := if removed && |nextQueries| == 0 then map key: int {:trigger state.processingBatch[key]} {:trigger key in state.processingBatch} | key in state.processingBatch && key != docId :: state.processingBatch[key] else if removed then state.processingBatch[docId := nextQueries] else state.processingBatch;
      var nextOrder: seq<DocId> := if removed && !(docId in nextBatch) then RemoveDocId(state.processingOrder, docId) else state.processingOrder;
      StateChange(RetrievalWorkerState(state.pendingBatch, state.pendingOrder, nextBatch, nextOrder, state.stopped), removed)
    else
      StateChange(state, false)
  }

  function ResolveDoc(state: RetrievalWorkerState, docId: DocId): StateChange
    decreases state, docId
  {
    var removedPending: bool := docId in state.pendingBatch;
    var removedProcessing: bool := docId in state.processingBatch;
    var nextPending: map<int, seq<QueryId>> := map key: int {:trigger state.pendingBatch[key]} {:trigger key in state.pendingBatch} | key in state.pendingBatch && key != docId :: state.pendingBatch[key];
    var nextProcessing: map<int, seq<QueryId>> := map key: int {:trigger state.processingBatch[key]} {:trigger key in state.processingBatch} | key in state.processingBatch && key != docId :: state.processingBatch[key];
    StateChange(RetrievalWorkerState(nextPending, RemoveDocId(state.pendingOrder, docId), nextProcessing, RemoveDocId(state.processingOrder, docId), state.stopped), removedPending || removedProcessing)
  }

  function BeginCycle(state: RetrievalWorkerState): RetrievalWorkerState
    decreases state
  {
    RetrievalWorkerState(map[], [], state.pendingBatch, state.pendingOrder, state.stopped)
  }

  function FinishCycle(state: RetrievalWorkerState): RetrievalWorkerState
    decreases state
  {
    RetrievalWorkerState(state.pendingBatch, state.pendingOrder, map[], [], state.stopped)
  }

  function Stop(state: RetrievalWorkerState): RetrievalWorkerState
    decreases state
  {
    RetrievalWorkerState(state.pendingBatch, state.pendingOrder, state.processingBatch, state.processingOrder, true)
  }

  function HasPendingWork(state: RetrievalWorkerState): bool
    decreases state
  {
    |state.pendingOrder| > 0
  }

  function ShouldExit(state: RetrievalWorkerState): bool
    decreases state
  {
    state.stopped &&
    !HasPendingWork(state)
  }

  function BuildPayload(state: RetrievalWorkerState, store: map<DocId, DocState>): seq<RetrievalDoc>
    decreases |state.processingOrder|
  {
    BuildPayloadFrom(state.processingOrder, state.processingBatch, store)
  }

  function BuildPayloadFrom(order: seq<DocId>, batch: map<DocId, seq<QueryId>>, store: map<DocId, DocState>): seq<RetrievalDoc>
    decreases |order|
  {
    if |order| == 0 then
      []
    else if !(order[0] in batch) then
      BuildPayloadFrom(order[1..], batch, store)
    else
      match LookupState(store, order[0]) case NoState() => BuildPayloadFrom(order[1..], batch, store) case HasState(state) => [RetrievalDoc(order[0], state, batch[order[0]])] + BuildPayloadFrom(order[1..], batch, store)
  }

  import opened DocsIndexModel

  import opened ThunderDbStack

  datatype RetrievalWorkerState = RetrievalWorkerState(pendingBatch: map<DocId, seq<QueryId>>, pendingOrder: seq<DocId>, processingBatch: map<DocId, seq<QueryId>>, processingOrder: seq<DocId>, stopped: bool)

  datatype StateChange = StateChange(state: RetrievalWorkerState, changed: bool)
}

module ThunderDbStack {
  function GetScore(state: DocState): Score
    decreases state
  {
    state.scoreValue
  }

  function LookupState(store: map<DocId, DocState>, id: DocId): MaybeDocState
    decreases store, id
  {
    if id in store then
      HasState(store[id])
    else
      NoState
  }

  function PutStoredDoc(store: map<DocId, DocState>, id: DocId, state: DocState): map<DocId, DocState>
    decreases store, id, state
  {
    store[id := state]
  }

  function RemoveStoredDoc(store: map<DocId, DocState>, id: DocId): map<DocId, DocState>
    decreases store, id
  {
    map key: int {:trigger store[key]} {:trigger key in store} | key in store && key != id :: store[key]
  }

  function ContainsId(ids: seq<DocId>, id: DocId): bool
    decreases ids, id
  {
    if |ids| == 0 then
      false
    else
      ids[0] == id || ContainsId(ids[1..], id)
  }

  function ContainsQueryId(ids: seq<QueryId>, id: QueryId): bool
    decreases ids, id
  {
    if |ids| == 0 then
      false
    else
      ids[0] == id || ContainsQueryId(ids[1..], id)
  }

  function AppendQueryIdUnique(ids: seq<QueryId>, id: QueryId): seq<QueryId>
    decreases ids, id
  {
    if ContainsQueryId(ids, id) then
      ids
    else
      ids + [id]
  }

  function UniqueDocIds(ids: seq<DocId>): bool
    decreases ids
  {
    if |ids| == 0 then
      true
    else
      !ContainsId(ids[1..], ids[0]) && UniqueDocIds(ids[1..])
  }

  function AppendDocIdIfMissing(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if ContainsId(ids, id) then
      ids
    else
      ids + [id]
  }

  function RemoveDocId(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if |ids| == 0 then
      []
    else if ids[0] == id then
      ids[1..]
    else
      [ids[0]] + RemoveDocId(ids[1..], id)
  }

  import opened DocsIndexModel

  type QueryId = int

  datatype DocState = DocState(scoreValue: Score)

  datatype MaybeDocState = NoState | HasState(state: DocState)

  datatype SeedDoc = SeedDoc(id: DocId, state: DocState)

  datatype QuerySpec = QuerySpec(minScore: Score, maxScore: Score, limit: nat)

  datatype Eviction = Eviction(queryId: QueryId, docId: DocId)

  datatype MatchPayload = MatchPayload(docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, matchesOld: seq<QueryId>, matchesNew: seq<QueryId>, evictions: seq<Eviction>)

  datatype RetrievalDoc = RetrievalDoc(docId: DocId, state: DocState, queries: seq<QueryId>)

  datatype DownstreamEvent = MatchEvent(payload: MatchPayload) | RetrievalEvent(docs: seq<RetrievalDoc>)

  datatype StreamItem = DocChangeItem(id: DocId, oldState: MaybeDocState, newState: MaybeDocState) | QueryAddItem(spec: QuerySpec) | QueryRemoveItem(id: QueryId) | SeedDocsItem(docs: seq<SeedDoc>)
}

module DocsIndexModel {
  function LexLt(a: Entry, b: Entry): bool
    decreases a, b
  {
    a.score < b.score || (a.score == b.score && a.id < b.id)
  }

  predicate SortedEntries(es: seq<Entry>)
    decreases es
  {
    if |es| < 2 then
      true
    else
      LexLt(es[0], es[1]) && SortedEntries(es[1..])
  }

  function CountStrictLessScore(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score < score then 1 else 0) + CountStrictLessScore(es[1..], score)
  }

  function CountAtMost(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score <= score then 1 else 0) + CountAtMost(es[1..], score)
  }

  function RankWithId(es: seq<Entry>, score: Score, id: DocId): nat
    decreases es, score, id
  {
    if |es| == 0 then
      0
    else if es[0].score < score || (es[0].score == score && es[0].id < id) then
      1 + RankWithId(es[1..], score, id)
    else
      0
  }

  function Rank(es: seq<Entry>, score: Score, id: MaybeDocId): nat
    decreases es, score, id
  {
    match id
    case NoDoc() =>
      CountStrictLessScore(es, score)
    case SomeDoc(doc) =>
      RankWithId(es, score, doc)
  }

  function InsertUnique(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    ensures SortedEntries(InsertUnique(es, score, id))
    decreases es, score, id
  {
    if |es| == 0 then
      [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then
      es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      [Entry(score, id)] + es
    else
      [es[0]] + InsertUnique(es[1..], score, id)
  }

  function RemoveOne(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    ensures SortedEntries(RemoveOne(es, score, id))
    decreases es, score, id
  {
    if |es| == 0 then
      es
    else if es[0].score == score && es[0].id == id then
      es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      es
    else
      [es[0]] + RemoveOne(es[1..], score, id)
  }

  function PositionAt(es: seq<Entry>, idx: nat): nat
    requires SortedEntries(es)
    requires idx < |es|
    decreases es, idx
  {
    if idx == 0 then
      0
    else if es[idx - 1].score == es[idx].score then
      1 + PositionAt(es, idx - 1)
    else
      0
  }

  function GetAtRank(es: seq<Entry>, rank: nat): AtRank
    requires SortedEntries(es)
    decreases es, rank
  {
    if rank >= |es| then
      Missing
    else
      Found(es[rank].score, es[rank].id, PositionAt(es, rank))
  }

  function CollectRange(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SortedEntries(es)
    decreases es, minScore, maxScore, limit
  {
    if |es| == 0 || limit == 0 then
      []
    else if es[0].score < minScore then
      CollectRange(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then
      []
    else
      [es[0].id] + CollectRange(es[1..], minScore, maxScore, limit - 1)
  }

  type Score = int

  type DocId = int

  datatype MaybeDocId = NoDoc | SomeDoc(doc: DocId)

  datatype AtRank = Missing | Found(score: Score, id: DocId, position: nat)

  datatype Entry = Entry(score: Score, id: DocId)
}

module TsLimitQueriesRuntime {
  function EmptyLimitQueriesState(): LimitQueriesState
  {
    LimitQueriesState(EmptyDocsState(), EmptyQueriesState(), 1, map[], map[], map[], map[])
  }

  predicate LimitQueriesConsistent(state: LimitQueriesState)
    decreases state
  {
    DocsConsistent(state.docs) &&
    QueriesConsistent(state.queries) &&
    1 <= state.nextId &&
    EntryIdsBelow(state.queries.entries, state.nextId) &&
    forall id: int {:trigger state.infos[id]} {:trigger id in state.baseScores} {:trigger id in state.infos} :: 
      (id in state.infos ==>
        id in state.baseScores) &&
      (id in state.infos ==>
        state.infos[id].id == id)
  }

  function NatMin(a: nat, b: nat): nat
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function RemoveQueryId(ids: seq<QueryId>, id: QueryId): seq<QueryId>
    decreases ids, id
  {
    if |ids| == 0 then
      []
    else if ids[0] == id then
      ids[1..]
    else
      [ids[0]] + RemoveQueryId(ids[1..], id)
  }

  function SetCurrentMatches(state: LimitQueriesState, queryId: QueryId, currentMatches: nat): LimitQueriesState
    requires queryId in state.infos
    ensures LimitQueriesConsistent(state) ==> LimitQueriesConsistent(SetCurrentMatches(state, queryId, currentMatches))
    decreases state, queryId, currentMatches
  {
    var info: QueryInfo := state.infos[queryId];
    LimitQueriesState(state.docs, state.queries, state.nextId, state.infos[queryId := QueryInfo(info.id, info.a, info.k, info.max, currentMatches)], state.baseScores, state.pendingByQuery, state.pendingByDoc)
  }

  function AddPendingPair(state: LimitQueriesState, queryId: QueryId, docId: DocId): LimitQueriesState
    ensures LimitQueriesConsistent(state) ==> LimitQueriesConsistent(AddPendingPair(state, queryId, docId))
    decreases state, queryId, docId
  {
    var docsForQuery: seq<DocId> := if queryId in state.pendingByQuery then AppendDocIdIfMissing(state.pendingByQuery[queryId], docId) else [docId];
    var queriesForDoc: seq<QueryId> := if docId in state.pendingByDoc then AppendQueryIdUnique(state.pendingByDoc[docId], queryId) else [queryId];
    LimitQueriesState(state.docs, state.queries, state.nextId, state.infos, state.baseScores, state.pendingByQuery[queryId := docsForQuery], state.pendingByDoc[docId := queriesForDoc])
  }

  function RemovePendingPair(state: LimitQueriesState, queryId: QueryId, docId: DocId): LimitQueriesState
    ensures LimitQueriesConsistent(state) ==> LimitQueriesConsistent(RemovePendingPair(state, queryId, docId))
    decreases state, queryId, docId
  {
    var nextPendingByQuery: map<int, seq<DocId>> := if queryId in state.pendingByQuery && ContainsId(state.pendingByQuery[queryId], docId) then var nextDocs: seq<DocId> := RemoveDocId(state.pendingByQuery[queryId], docId); if |nextDocs| == 0 then map key: int {:trigger state.pendingByQuery[key]} {:trigger key in state.pendingByQuery} | key in state.pendingByQuery && key != queryId :: state.pendingByQuery[key] else state.pendingByQuery[queryId := nextDocs] else state.pendingByQuery;
    var nextPendingByDoc: map<int, seq<QueryId>> := if docId in state.pendingByDoc && ContainsQueryId(state.pendingByDoc[docId], queryId) then var nextQueries: seq<QueryId> := RemoveQueryId(state.pendingByDoc[docId], queryId); if |nextQueries| == 0 then map key: int {:trigger state.pendingByDoc[key]} {:trigger key in state.pendingByDoc} | key in state.pendingByDoc && key != docId :: state.pendingByDoc[key] else state.pendingByDoc[docId := nextQueries] else state.pendingByDoc;
    LimitQueriesState(state.docs, state.queries, state.nextId, state.infos, state.baseScores, nextPendingByQuery, nextPendingByDoc)
  }

  function CountDocsInRange(state: LimitQueriesState, minScore: Score, maxScore: Score): nat
    requires LimitQueriesConsistent(state)
    decreases state, minScore, maxScore
  {
    var upper: nat := CountAtMostDoc(state.docs, maxScore);
    var lower: nat := RankDoc(state.docs, minScore, NoDoc);
    if lower <= upper then
      upper - lower
    else
      0
  }

  function AddQuery(state: LimitQueriesState, a: Score, k: nat, max: Score): QueryAddResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(AddQuery(state, a, k, max).state)
    decreases state, a, k, max
  {
    var queryId: QueryId := state.nextId;
    var effectiveScore: int := RankDoc(state.docs, a, NoDoc) + k;
    var nextQueries: QueriesState := Insert(state.queries, a, state.nextId, effectiveScore, max);
    var baseScore: int := effectiveScore - AccumulatedAddAtKey(state.queries, a);
    var currentMatches: nat := NatMin(CountDocsInRange(state, a, max), k);
    QueryAddResult(LimitQueriesState(state.docs, nextQueries, queryId + 1, state.infos[queryId := QueryInfo(queryId, a, k, max, currentMatches)], state.baseScores[queryId := baseScore], state.pendingByQuery, state.pendingByDoc), queryId)
  }

  function RemovePendingDocsForQuery(state: LimitQueriesState, docs: seq<DocId>, queryId: QueryId): LimitQueriesState
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(RemovePendingDocsForQuery(state, docs, queryId))
    decreases |docs|
  {
    if |docs| == 0 then
      state
    else
      RemovePendingDocsForQuery(RemovePendingPair(state, queryId, docs[0]), docs[1..], queryId)
  }

  function RemoveQuery(state: LimitQueriesState, queryId: QueryId): StateChange
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(RemoveQuery(state, queryId).state)
    decreases state, queryId
  {
    if !(queryId in state.infos) || !(queryId in state.baseScores) then
      StateChange(state, false)
    else
      var info: QueryInfo := state.infos[queryId]; var baseScore: int := state.baseScores[queryId]; var state1: LimitQueriesState := LimitQueriesState(state.docs, Remove(state.queries, info.a, queryId, baseScore, info.max), state.nextId, map key: int {:trigger state.infos[key]} {:trigger key in state.infos} | key in state.infos && key != queryId :: state.infos[key], map key: int {:trigger state.baseScores[key]} {:trigger key in state.baseScores} | key in state.baseScores && key != queryId :: state.baseScores[key], state.pendingByQuery, state.pendingByDoc); var state2: LimitQueriesState := if queryId in state1.pendingByQuery then RemovePendingDocsForQuery(state1, state1.pendingByQuery[queryId], queryId) else state1; StateChange(LimitQueriesState(state2.docs, state2.queries, state2.nextId, state2.infos, state2.baseScores, map key: int {:trigger state2.pendingByQuery[key]} {:trigger key in state2.pendingByQuery} | key in state2.pendingByQuery && key != queryId :: state2.pendingByQuery[key], state2.pendingByDoc), true)
  }

  function GetQueriesCovering(state: LimitQueriesState, value: Score, docId: MaybeDocId): seq<QueryId>
    requires LimitQueriesConsistent(state)
    decreases state, value, docId
  {
    CollectForValue(state.queries, value, RankDoc(state.docs, value, docId))
  }

  function GetDocsForQuery(state: LimitQueriesState, queryId: QueryId): seq<DocId>
    requires LimitQueriesConsistent(state)
    decreases state, queryId
  {
    if !(queryId in state.infos) then
      []
    else
      var info: QueryInfo := state.infos[queryId]; CollectRangeDocs(state.docs, info.a, info.max, info.k)
  }

  function DecrementCurrentMatchesFor(state: LimitQueriesState, affected: seq<QueryId>): LimitQueriesState
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(DecrementCurrentMatchesFor(state, affected))
    decreases |affected|
  {
    if |affected| == 0 then
      state
    else if !(affected[0] in state.infos) then
      DecrementCurrentMatchesFor(state, affected[1..])
    else
      var info: QueryInfo := state.infos[affected[0]]; var nextState: LimitQueriesState := if info.currentMatches == 0 then state else SetCurrentMatches(state, affected[0], info.currentMatches - 1); DecrementCurrentMatchesFor(nextState, affected[1..])
  }

  function RemoveDocument(state: LimitQueriesState, score: Score, docId: DocId): RemoveDocumentResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(RemoveDocument(state, score, docId).state)
    decreases state, score, docId
  {
    var affected: seq<QueryId> := GetQueriesCovering(state, score, SomeDoc(docId));
    var nextDocs: DocsState := RemoveDoc(state.docs, score, docId);
    var nextQueries: QueriesState := RangeAddKeysGreaterThan(state.queries, score, -1);
    var nextState: LimitQueriesState := LimitQueriesState(nextDocs, nextQueries, state.nextId, state.infos, state.baseScores, state.pendingByQuery, state.pendingByDoc);
    RemoveDocumentResult(DecrementCurrentMatchesFor(nextState, affected), affected)
  }

  function ProcessAddedQueries(state: LimitQueriesState, affected: seq<QueryId>, docId: DocId): AddDocumentResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(ProcessAddedQueries(state, affected, docId).state)
    decreases |affected|
  {
    if |affected| == 0 then
      AddDocumentResult(state, [], [])
    else
      var queryId: int := affected[0]; var rest: seq<int> := affected[1..]; if !(queryId in state.infos) then var next: AddDocumentResult := ProcessAddedQueries(state, rest, docId); AddDocumentResult(next.state, [queryId] + next.matched, next.blocked) else if docId in state.pendingByDoc && ContainsQueryId(state.pendingByDoc[docId], queryId) then var next: AddDocumentResult := ProcessAddedQueries(RemovePendingPair(state, queryId, docId), rest, docId); AddDocumentResult(next.state, [queryId] + next.matched, next.blocked) else var info: QueryInfo := state.infos[queryId]; if info.currentMatches < info.k then var next: AddDocumentResult := ProcessAddedQueries(SetCurrentMatches(state, queryId, info.currentMatches + 1), rest, docId); AddDocumentResult(next.state, [queryId] + next.matched, next.blocked) else var next: AddDocumentResult := ProcessAddedQueries(state, rest, docId); AddDocumentResult(next.state, [queryId] + next.matched, [queryId] + next.blocked)
  }

  function AddDocument(state: LimitQueriesState, score: Score, docId: DocId): AddDocumentResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(AddDocument(state, score, docId).state)
    decreases state, score, docId
  {
    var affected: seq<QueryId> := GetQueriesCovering(state, score, SomeDoc(docId));
    var nextDocs: DocsState := AddDoc(state.docs, score, docId);
    var nextQueries: QueriesState := RangeAddKeysGreaterThan(state.queries, score, 1);
    ProcessAddedQueries(LimitQueriesState(nextDocs, nextQueries, state.nextId, state.infos, state.baseScores, state.pendingByQuery, state.pendingByDoc), affected, docId)
  }

  function DocForQueryAt(state: LimitQueriesState, info: QueryInfo, offset: nat): MaybeDocId
    requires LimitQueriesConsistent(state)
    decreases state, info, offset
  {
    var startRank: nat := RankDoc(state.docs, info.a, NoDoc);
    match GetAtRankDoc(state.docs, startRank + offset)
    case Missing() =>
      NoDoc
    case Found(score, id, pos) =>
      if score <= info.max then
        SomeDoc(id)
      else
        NoDoc
  }

  function PickOverflowDoc(state: LimitQueriesState, queryId: QueryId): MaybeDocId
    requires LimitQueriesConsistent(state)
    decreases state, queryId
  {
    if !(queryId in state.infos) then
      NoDoc
    else
      var info: QueryInfo := state.infos[queryId]; if info.currentMatches < info.k then NoDoc else DocForQueryAt(state, info, info.k)
  }

  function FillGapFrom(state: LimitQueriesState, queryId: QueryId, offset: nat): GapFillResult
    requires LimitQueriesConsistent(state)
    requires queryId in state.infos
    ensures LimitQueriesConsistent(FillGapFrom(state, queryId, offset).state)
    decreases |state.docs.entries| + 1, |state.docs.entries| - offset
  {
    var candidate: MaybeDocId := DocForQueryAt(state, state.infos[queryId], offset);
    match candidate
    case NoDoc() =>
      GapFillResult(state, NoDoc)
    case SomeDoc(docId) =>
      if queryId in state.pendingByQuery && ContainsId(state.pendingByQuery[queryId], docId) then
        FillGapFrom(state, queryId, offset + 1)
      else
        var info: QueryInfo := state.infos[queryId]; var state1: LimitQueriesState := SetCurrentMatches(state, queryId, info.currentMatches + 1); GapFillResult(AddPendingPair(state1, queryId, docId), SomeDoc(docId))
  }

  function FillGap(state: LimitQueriesState, queryId: QueryId): GapFillResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(FillGap(state, queryId).state)
    decreases state, queryId
  {
    if !(queryId in state.infos) then
      GapFillResult(state, NoDoc)
    else
      var info: QueryInfo := state.infos[queryId]; if info.currentMatches >= info.k then GapFillResult(state, NoDoc) else FillGapFrom(state, queryId, info.currentMatches)
  }

  function CancelPendingForQuery(state: LimitQueriesState, docId: DocId, queryId: QueryId): StateChange
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(CancelPendingForQuery(state, docId, queryId).state)
    decreases state, docId, queryId
  {
    if !(queryId in state.pendingByQuery) || !ContainsId(state.pendingByQuery[queryId], docId) then
      StateChange(state, false)
    else
      var state1: LimitQueriesState := RemovePendingPair(state, queryId, docId); var state2: LimitQueriesState := if queryId in state1.infos && state1.infos[queryId].currentMatches > 0 then SetCurrentMatches(state1, queryId, state1.infos[queryId].currentMatches - 1) else state1; StateChange(state2, true)
  }

  function ResolvePendingDocQueries(state: LimitQueriesState, queryIds: seq<QueryId>, docId: DocId): LimitQueriesState
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(ResolvePendingDocQueries(state, queryIds, docId))
    decreases |queryIds|
  {
    if |queryIds| == 0 then
      state
    else
      ResolvePendingDocQueries(RemovePendingPair(state, queryIds[0], docId), queryIds[1..], docId)
  }

  function ResolvePendingForDoc(state: LimitQueriesState, docId: DocId): LimitQueriesState
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(ResolvePendingForDoc(state, docId))
    decreases state, docId
  {
    if !(docId in state.pendingByDoc) then
      state
    else
      ResolvePendingDocQueries(state, state.pendingByDoc[docId], docId)
  }

  import opened DocsIndexModel

  import opened ThunderDbStack

  import opened TsDocsRuntime

  import opened TsQueriesRuntime

  datatype QueryInfo = QueryInfo(id: QueryId, a: Score, k: nat, max: Score, currentMatches: nat)

  datatype LimitQueriesState = LimitQueriesState(docs: DocsState, queries: QueriesState, nextId: QueryId, infos: map<QueryId, QueryInfo>, baseScores: map<QueryId, int>, pendingByQuery: map<QueryId, seq<DocId>>, pendingByDoc: map<DocId, seq<QueryId>>)

  datatype StateChange = StateChange(state: LimitQueriesState, changed: bool)

  datatype QueryAddResult = QueryAddResult(state: LimitQueriesState, queryId: QueryId)

  datatype AddDocumentResult = AddDocumentResult(state: LimitQueriesState, matched: seq<QueryId>, blocked: seq<QueryId>)

  datatype RemoveDocumentResult = RemoveDocumentResult(state: LimitQueriesState, removed: seq<QueryId>)

  datatype GapFillResult = GapFillResult(state: LimitQueriesState, doc: MaybeDocId)
}

module TsQueriesRuntime {
  function EmptyQueriesState(): QueriesState
  {
    QueriesState([], [])
  }

  function UniqueQueryEntries(entries: seq<QueryEntry>): bool
    decreases entries
  {
    if |entries| == 0 then
      true
    else
      !ContainsQueryEntryId(entries[1..], entries[0].id) && UniqueQueryEntries(entries[1..])
  }

  predicate EntryIdsBelow(entries: seq<QueryEntry>, bound: QueryId)
    decreases entries, bound
  {
    if |entries| == 0 then
      true
    else
      entries[0].id < bound && EntryIdsBelow(entries[1..], bound)
  }

  function ContainsQueryEntryId(entries: seq<QueryEntry>, id: QueryId): bool
    decreases entries, id
  {
    if |entries| == 0 then
      false
    else
      entries[0].id == id || ContainsQueryEntryId(entries[1..], id)
  }

  predicate OrderedEntries(entries: seq<QueryEntry>)
    decreases entries
  {
    if |entries| < 2 then
      true
    else
      CompareEntries(entries[0], entries[1]) && OrderedEntries(entries[1..])
  }

  predicate QueriesConsistent(state: QueriesState)
    decreases state
  {
    UniqueQueryEntries(state.entries) &&
    OrderedEntries(state.entries)
  }

  function SumRangeAddsAtKey(ops: seq<RangeAddOp>, key: Score): int
    decreases |ops|
  {
    if |ops| == 0 then
      0
    else
      (if ops[0].threshold < key then ops[0].delta else 0) + SumRangeAddsAtKey(ops[1..], key)
  }

  function AccumulatedAddAtKey(state: QueriesState, key: Score): int
    decreases state, key
  {
    SumRangeAddsAtKey(state.rangeAdds, key)
  }

  function EffectiveScore(state: QueriesState, entry: QueryEntry): int
    decreases state, entry
  {
    entry.baseScore + AccumulatedAddAtKey(state, entry.key)
  }

  function RangeAddKeysGreaterThan(state: QueriesState, threshold: Score, delta: int): QueriesState
    requires QueriesConsistent(state)
    ensures QueriesConsistent(state) ==> QueriesConsistent(RangeAddKeysGreaterThan(state, threshold, delta))
    decreases state, threshold, delta
  {
    QueriesState(state.entries, state.rangeAdds + [RangeAddOp(threshold, delta)])
  }

  function CompareEntries(left: QueryEntry, right: QueryEntry): bool
    decreases left, right
  {
    left.key < right.key || (left.key == right.key && (left.baseScore < right.baseScore || (left.baseScore == right.baseScore && left.id < right.id)))
  }

  lemma /*{:_inductionTrigger ContainsQueryEntryId(entries, bound)}*/ /*{:_inductionTrigger EntryIdsBelow(entries, bound)}*/ /*{:_induction entries, bound}*/ EntryIdsBelowEntailsNotContained(entries: seq<QueryEntry>, bound: QueryId)
    requires EntryIdsBelow(entries, bound)
    ensures !ContainsQueryEntryId(entries, bound)
    decreases |entries|
  {
  }

  lemma BelowBoundImpliesBelowPlusOne(entries: seq<QueryEntry>, bound: QueryId)
    requires EntryIdsBelow(entries, bound)
    ensures EntryIdsBelow(entries, bound + 1)
    decreases |entries|
  {
    if |entries| > 0 {
      BelowBoundImpliesBelowPlusOne(entries[1..], bound);
    }
  }

  function InsertEntrySorted(entries: seq<QueryEntry>, entry: QueryEntry): seq<QueryEntry>
    requires OrderedEntries(entries)
    requires UniqueQueryEntries(entries)
    requires EntryIdsBelow(entries, entry.id)
    ensures OrderedEntries(InsertEntrySorted(entries, entry))
    ensures UniqueQueryEntries(InsertEntrySorted(entries, entry))
    ensures forall id: int {:trigger ContainsQueryEntryId(entries, id)} {:trigger ContainsQueryEntryId(InsertEntrySorted(entries, entry), id)} :: ContainsQueryEntryId(InsertEntrySorted(entries, entry), id) ==> id == entry.id || ContainsQueryEntryId(entries, id)
    ensures forall bound: int {:trigger EntryIdsBelow(InsertEntrySorted(entries, entry), bound)} {:trigger EntryIdsBelow(entries, bound)} :: EntryIdsBelow(entries, bound) && entry.id < bound ==> EntryIdsBelow(InsertEntrySorted(entries, entry), bound)
    ensures EntryIdsBelow(InsertEntrySorted(entries, entry), entry.id + 1)
    decreases |entries|
  {
    if |entries| == 0 then
      [entry]
    else if CompareEntries(entry, entries[0]) then
      EntryIdsBelowEntailsNotContained(entries, entry.id);
      BelowBoundImpliesBelowPlusOne(entries, entry.id);
      [entry] + entries
    else
      [entries[0]] + InsertEntrySorted(entries[1..], entry)
  }

  function Insert(state: QueriesState, key: Score, id: QueryId, effectiveScore: int, maxCap: Score): QueriesState
    requires QueriesConsistent(state)
    requires EntryIdsBelow(state.entries, id)
    ensures QueriesConsistent(Insert(state, key, id, effectiveScore, maxCap))
    ensures forall bound: int {:trigger EntryIdsBelow(Insert(state, key, id, effectiveScore, maxCap).entries, bound)} {:trigger EntryIdsBelow(state.entries, bound)} :: EntryIdsBelow(state.entries, bound) && id < bound ==> EntryIdsBelow(Insert(state, key, id, effectiveScore, maxCap).entries, bound)
    ensures EntryIdsBelow(Insert(state, key, id, effectiveScore, maxCap).entries, id + 1)
    decreases state, key, id, effectiveScore, maxCap
  {
    var baseScore: int := effectiveScore - AccumulatedAddAtKey(state, key);
    var entries: seq<QueryEntry> := InsertEntrySorted(state.entries, QueryEntry(id, key, baseScore, maxCap));
    assert OrderedEntries(entries);
    assert UniqueQueryEntries(entries);
    assert EntryIdsBelow(entries, id + 1);
    QueriesState(entries, state.rangeAdds)
  }

  function RemoveEntries(entries: seq<QueryEntry>, key: Score, id: QueryId, baseScore: int, maxCap: Score): seq<QueryEntry>
    requires OrderedEntries(entries)
    requires UniqueQueryEntries(entries)
    ensures OrderedEntries(entries) ==> OrderedEntries(RemoveEntries(entries, key, id, baseScore, maxCap))
    ensures UniqueQueryEntries(entries) ==> UniqueQueryEntries(RemoveEntries(entries, key, id, baseScore, maxCap))
    ensures forall id2: QueryId {:trigger ContainsQueryEntryId(entries, id2)} {:trigger ContainsQueryEntryId(RemoveEntries(entries, key, id, baseScore, maxCap), id2)} :: ContainsQueryEntryId(RemoveEntries(entries, key, id, baseScore, maxCap), id2) ==> ContainsQueryEntryId(entries, id2)
    ensures forall bound: QueryId {:trigger EntryIdsBelow(RemoveEntries(entries, key, id, baseScore, maxCap), bound)} {:trigger EntryIdsBelow(entries, bound)} :: EntryIdsBelow(entries, bound) ==> EntryIdsBelow(RemoveEntries(entries, key, id, baseScore, maxCap), bound)
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else if entries[0] == QueryEntry(id, key, baseScore, maxCap) then
      entries[1..]
    else
      [entries[0]] + RemoveEntries(entries[1..], key, id, baseScore, maxCap)
  }

  function Remove(state: QueriesState, key: Score, id: QueryId, baseScore: int, maxCap: Score): QueriesState
    requires QueriesConsistent(state)
    ensures QueriesConsistent(state) ==> QueriesConsistent(Remove(state, key, id, baseScore, maxCap))
    ensures forall bound: QueryId {:trigger EntryIdsBelow(Remove(state, key, id, baseScore, maxCap).entries, bound)} {:trigger EntryIdsBelow(state.entries, bound)} :: EntryIdsBelow(state.entries, bound) ==> EntryIdsBelow(Remove(state, key, id, baseScore, maxCap).entries, bound)
    decreases state, key, id, baseScore, maxCap
  {
    QueriesState(RemoveEntries(state.entries, key, id, baseScore, maxCap), state.rangeAdds)
  }

  function CollectForValue(state: QueriesState, value: Score, cutoff: int): seq<QueryId>
    decreases |state.entries|
  {
    CollectMatchingEntries(state, state.entries, value, cutoff)
  }

  function CollectMatchingEntries(state: QueriesState, entries: seq<QueryEntry>, value: Score, cutoff: int): seq<QueryId>
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else if entries[0].key <= value && value <= entries[0].maxCap && cutoff < EffectiveScore(state, entries[0]) then
      [entries[0].id] + CollectMatchingEntries(state, entries[1..], value, cutoff)
    else
      CollectMatchingEntries(state, entries[1..], value, cutoff)
  }

  import opened DocsIndexModel

  import opened ThunderDbStack

  datatype RangeAddOp = RangeAddOp(threshold: Score, delta: int)

  datatype QueryEntry = QueryEntry(id: QueryId, key: Score, baseScore: int, maxCap: Score)

  datatype QueriesState = QueriesState(entries: seq<QueryEntry>, rangeAdds: seq<RangeAddOp>)
}

module TsDocsRuntime {
  function EmptyDocsState(): DocsState
  {
    DocsState([])
  }

  predicate DocsConsistent(state: DocsState)
    decreases state
  {
    SortedEntries(state.entries)
  }

  function AddDoc(state: DocsState, score: Score, id: DocId): DocsState
    requires DocsConsistent(state)
    ensures DocsConsistent(AddDoc(state, score, id))
    decreases state, score, id
  {
    DocsState(InsertUnique(state.entries, score, id))
  }

  function RemoveDoc(state: DocsState, score: Score, id: DocId): DocsState
    requires DocsConsistent(state)
    ensures DocsConsistent(RemoveDoc(state, score, id))
    decreases state, score, id
  {
    DocsState(RemoveOne(state.entries, score, id))
  }

  function RankDoc(state: DocsState, score: Score, id: MaybeDocId): nat
    requires DocsConsistent(state)
    decreases state, score, id
  {
    Rank(state.entries, score, id)
  }

  function CountAtMostDoc(state: DocsState, score: Score): nat
    requires DocsConsistent(state)
    decreases state, score
  {
    CountAtMost(state.entries, score)
  }

  function GetAtRankDoc(state: DocsState, rank: nat): AtRank
    requires DocsConsistent(state)
    decreases state, rank
  {
    GetAtRank(state.entries, rank)
  }

  function CollectRangeDocs(state: DocsState, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires DocsConsistent(state)
    decreases state, minScore, maxScore, limit
  {
    CollectRange(state.entries, minScore, maxScore, limit)
  }

  import opened DocsIndexModel

  datatype DocsState = DocsState(entries: seq<Entry>)
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      // Be sure to use ElementCount to avoid casting into 32 bits
      // integers that could lead to overflows (see https://github.com/dafny-lang/dafny/issues/5554)
      return th.ElementCount < other.ElementCount && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    internal volatile ISequence<T> left, right;
    internal ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    internal ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
// end of class FuncExtensions
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
}
// end of class FuncExtensions
namespace DocsIndexModel {

  public partial class __default {
    public static bool LexLt(DocsIndexModel._IEntry a, DocsIndexModel._IEntry b)
    {
      return (((a).dtor_score) < ((b).dtor_score)) || ((((a).dtor_score) == ((b).dtor_score)) && (((a).dtor_id) < ((b).dtor_id)));
    }
    public static bool SortedEntries(Dafny.ISequence<DocsIndexModel._IEntry> es) {
      if ((new BigInteger((es).Count)) < (new BigInteger(2))) {
        return true;
      } else {
        return (DocsIndexModel.__default.LexLt((es).Select(BigInteger.Zero), (es).Select(BigInteger.One))) && (DocsIndexModel.__default.SortedEntries((es).Drop(BigInteger.One)));
      }
    }
    public static BigInteger CountStrictLessScore(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) < (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger CountAtMost(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) <= (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger RankWithId(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) < (score)) || (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) < (id)))) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static BigInteger Rank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, DocsIndexModel._IMaybeDocId id)
    {
      DocsIndexModel._IMaybeDocId _source0 = id;
      {
        if (_source0.is_NoDoc) {
          return DocsIndexModel.__default.CountStrictLessScore(es, score);
        }
      }
      {
        BigInteger _0_doc = _source0.dtor_doc;
        return DocsIndexModel.__default.RankWithId(es, score, _0_doc);
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> InsertUnique(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)));
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.Concat(Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)), es));
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> RemoveOne(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, (es).Drop(BigInteger.One));
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger PositionAt(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger idx)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((idx).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if ((((es).Select((idx) - (BigInteger.One))).dtor_score) == (((es).Select(idx)).dtor_score)) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = es;
        BigInteger _in1 = (idx) - (BigInteger.One);
        es = _in0;
        idx = _in1;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static DocsIndexModel._IAtRank GetAtRank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger rank)
    {
      if ((rank) >= (new BigInteger((es).Count))) {
        return DocsIndexModel.AtRank.create_Missing();
      } else {
        return DocsIndexModel.AtRank.create_Found(((es).Select(rank)).dtor_score, ((es).Select(rank)).dtor_id, DocsIndexModel.__default.PositionAt(es, rank));
      }
    }
    public static Dafny.ISequence<BigInteger> CollectRange(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((es).Count)).Sign == 0) || ((limit).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) < (minScore)) {
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = minScore;
        BigInteger _in2 = maxScore;
        BigInteger _in3 = limit;
        es = _in0;
        minScore = _in1;
        maxScore = _in2;
        limit = _in3;
        goto TAIL_CALL_START;
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) > (maxScore)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((es).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<DocsIndexModel._IEntry> _in4 = (es).Drop(BigInteger.One);
        BigInteger _in5 = minScore;
        BigInteger _in6 = maxScore;
        BigInteger _in7 = (limit) - (BigInteger.One);
        es = _in4;
        minScore = _in5;
        maxScore = _in6;
        limit = _in7;
        goto TAIL_CALL_START;
      }
    }
  }

  public interface _IMaybeDocId {
    bool is_NoDoc { get; }
    bool is_SomeDoc { get; }
    BigInteger dtor_doc { get; }
    _IMaybeDocId DowncastClone();
  }
  public abstract class MaybeDocId : _IMaybeDocId {
    public MaybeDocId() {
    }
    private static readonly DocsIndexModel._IMaybeDocId theDefault = create_NoDoc();
    public static DocsIndexModel._IMaybeDocId Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId>(DocsIndexModel.MaybeDocId.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaybeDocId create_NoDoc() {
      return new MaybeDocId_NoDoc();
    }
    public static _IMaybeDocId create_SomeDoc(BigInteger doc) {
      return new MaybeDocId_SomeDoc(doc);
    }
    public bool is_NoDoc { get { return this is MaybeDocId_NoDoc; } }
    public bool is_SomeDoc { get { return this is MaybeDocId_SomeDoc; } }
    public BigInteger dtor_doc {
      get {
        var d = this;
        return ((MaybeDocId_SomeDoc)d)._doc;
      }
    }
    public abstract _IMaybeDocId DowncastClone();
  }
  public class MaybeDocId_NoDoc : MaybeDocId {
    public MaybeDocId_NoDoc() : base() {
    }
    public override _IMaybeDocId DowncastClone() {
      if (this is _IMaybeDocId dt) { return dt; }
      return new MaybeDocId_NoDoc();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.MaybeDocId_NoDoc;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.MaybeDocId.NoDoc";
      return s;
    }
  }
  public class MaybeDocId_SomeDoc : MaybeDocId {
    public readonly BigInteger _doc;
    public MaybeDocId_SomeDoc(BigInteger doc) : base() {
      this._doc = doc;
    }
    public override _IMaybeDocId DowncastClone() {
      if (this is _IMaybeDocId dt) { return dt; }
      return new MaybeDocId_SomeDoc(_doc);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.MaybeDocId_SomeDoc;
      return oth != null && this._doc == oth._doc;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._doc));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.MaybeDocId.SomeDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._doc);
      s += ")";
      return s;
    }
  }

  public interface _IAtRank {
    bool is_Missing { get; }
    bool is_Found { get; }
    BigInteger dtor_score { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_position { get; }
    _IAtRank DowncastClone();
  }
  public abstract class AtRank : _IAtRank {
    public AtRank() {
    }
    private static readonly DocsIndexModel._IAtRank theDefault = create_Missing();
    public static DocsIndexModel._IAtRank Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IAtRank> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IAtRank>(DocsIndexModel.AtRank.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IAtRank> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAtRank create_Missing() {
      return new AtRank_Missing();
    }
    public static _IAtRank create_Found(BigInteger score, BigInteger id, BigInteger position) {
      return new AtRank_Found(score, id, position);
    }
    public bool is_Missing { get { return this is AtRank_Missing; } }
    public bool is_Found { get { return this is AtRank_Found; } }
    public BigInteger dtor_score {
      get {
        var d = this;
        return ((AtRank_Found)d)._score;
      }
    }
    public BigInteger dtor_id {
      get {
        var d = this;
        return ((AtRank_Found)d)._id;
      }
    }
    public BigInteger dtor_position {
      get {
        var d = this;
        return ((AtRank_Found)d)._position;
      }
    }
    public abstract _IAtRank DowncastClone();
  }
  public class AtRank_Missing : AtRank {
    public AtRank_Missing() : base() {
    }
    public override _IAtRank DowncastClone() {
      if (this is _IAtRank dt) { return dt; }
      return new AtRank_Missing();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.AtRank_Missing;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.AtRank.Missing";
      return s;
    }
  }
  public class AtRank_Found : AtRank {
    public readonly BigInteger _score;
    public readonly BigInteger _id;
    public readonly BigInteger _position;
    public AtRank_Found(BigInteger score, BigInteger id, BigInteger position) : base() {
      this._score = score;
      this._id = id;
      this._position = position;
    }
    public override _IAtRank DowncastClone() {
      if (this is _IAtRank dt) { return dt; }
      return new AtRank_Found(_score, _id, _position);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.AtRank_Found;
      return oth != null && this._score == oth._score && this._id == oth._id && this._position == oth._position;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._score));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._position));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.AtRank.Found";
      s += "(";
      s += Dafny.Helpers.ToString(this._score);
      s += ", ";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._position);
      s += ")";
      return s;
    }
  }

  public interface _IEntry {
    bool is_Entry { get; }
    BigInteger dtor_score { get; }
    BigInteger dtor_id { get; }
    _IEntry DowncastClone();
  }
  public class Entry : _IEntry {
    public readonly BigInteger _score;
    public readonly BigInteger _id;
    public Entry(BigInteger score, BigInteger id) {
      this._score = score;
      this._id = id;
    }
    public _IEntry DowncastClone() {
      if (this is _IEntry dt) { return dt; }
      return new Entry(_score, _id);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.Entry;
      return oth != null && this._score == oth._score && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._score));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.Entry.Entry";
      s += "(";
      s += Dafny.Helpers.ToString(this._score);
      s += ", ";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
    private static readonly DocsIndexModel._IEntry theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static DocsIndexModel._IEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IEntry> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IEntry>(DocsIndexModel.Entry.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEntry create(BigInteger score, BigInteger id) {
      return new Entry(score, id);
    }
    public static _IEntry create_Entry(BigInteger score, BigInteger id) {
      return create(score, id);
    }
    public bool is_Entry { get { return true; } }
    public BigInteger dtor_score {
      get {
        return this._score;
      }
    }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
  }
} // end of namespace DocsIndexModel
namespace ThunderDbStack {

  public partial class __default {
    public static BigInteger GetScore(BigInteger state) {
      return (state);
    }
    public static ThunderDbStack._IMaybeDocState LookupState(Dafny.IMap<BigInteger,BigInteger> store, BigInteger id)
    {
      if ((store).Contains(id)) {
        return ThunderDbStack.MaybeDocState.create_HasState(Dafny.Map<BigInteger, BigInteger>.Select(store,id));
      } else {
        return ThunderDbStack.MaybeDocState.create_NoState();
      }
    }
    public static Dafny.IMap<BigInteger,BigInteger> PutStoredDoc(Dafny.IMap<BigInteger,BigInteger> store, BigInteger id, BigInteger state)
    {
      return Dafny.Map<BigInteger, BigInteger>.Update(store, id, state);
    }
    public static Dafny.IMap<BigInteger,BigInteger> RemoveStoredDoc(Dafny.IMap<BigInteger,BigInteger> store, BigInteger id)
    {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,BigInteger>, BigInteger, Dafny.IMap<BigInteger,BigInteger>>>((_0_store, _1_id) => ((System.Func<Dafny.IMap<BigInteger,BigInteger>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,BigInteger>>();
        foreach (BigInteger _compr_0 in (_0_store).Keys.Elements) {
          BigInteger _2_key = (BigInteger)_compr_0;
          if (((_0_store).Contains(_2_key)) && ((_2_key) != (_1_id))) {
            _coll0.Add(new Dafny.Pair<BigInteger,BigInteger>(_2_key, Dafny.Map<BigInteger, BigInteger>.Select(_0_store,_2_key)));
          }
        }
        return Dafny.Map<BigInteger,BigInteger>.FromCollection(_coll0);
      }))())(store, id);
    }
    public static bool ContainsId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return false;
      } else {
        return (((ids).Select(BigInteger.Zero)) == (id)) || (ThunderDbStack.__default.ContainsId((ids).Drop(BigInteger.One), id));
      }
    }
    public static bool ContainsQueryId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return false;
      } else {
        return (((ids).Select(BigInteger.Zero)) == (id)) || (ThunderDbStack.__default.ContainsQueryId((ids).Drop(BigInteger.One), id));
      }
    }
    public static Dafny.ISequence<BigInteger> AppendQueryIdUnique(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if (ThunderDbStack.__default.ContainsQueryId(ids, id)) {
        return ids;
      } else {
        return Dafny.Sequence<BigInteger>.Concat(ids, Dafny.Sequence<BigInteger>.FromElements(id));
      }
    }
    public static bool UniqueDocIds(Dafny.ISequence<BigInteger> ids) {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return true;
      } else {
        return (!(ThunderDbStack.__default.ContainsId((ids).Drop(BigInteger.One), (ids).Select(BigInteger.Zero)))) && (ThunderDbStack.__default.UniqueDocIds((ids).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<BigInteger> AppendDocIdIfMissing(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if (ThunderDbStack.__default.ContainsId(ids, id)) {
        return ids;
      } else {
        return Dafny.Sequence<BigInteger>.Concat(ids, Dafny.Sequence<BigInteger>.FromElements(id));
      }
    }
    public static Dafny.ISequence<BigInteger> RemoveDocId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (((ids).Select(BigInteger.Zero)) == (id)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, (ids).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
  }

  public interface _IDocState {
    bool is_DocState { get; }
    BigInteger dtor_scoreValue { get; }
  }
  public class DocState : _IDocState {
    public readonly BigInteger _scoreValue;
    public DocState(BigInteger scoreValue) {
      this._scoreValue = scoreValue;
    }
    public static BigInteger DowncastClone(BigInteger _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DocState;
      return oth != null && this._scoreValue == oth._scoreValue;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._scoreValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DocState.DocState";
      s += "(";
      s += Dafny.Helpers.ToString(this._scoreValue);
      s += ")";
      return s;
    }
    private static readonly BigInteger theDefault = BigInteger.Zero;
    public static BigInteger Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDocState create(BigInteger scoreValue) {
      return new DocState(scoreValue);
    }
    public static _IDocState create_DocState(BigInteger scoreValue) {
      return create(scoreValue);
    }
    public bool is_DocState { get { return true; } }
    public BigInteger dtor_scoreValue {
      get {
        return this._scoreValue;
      }
    }
  }

  public interface _IMaybeDocState {
    bool is_NoState { get; }
    bool is_HasState { get; }
    BigInteger dtor_state { get; }
    _IMaybeDocState DowncastClone();
  }
  public abstract class MaybeDocState : _IMaybeDocState {
    public MaybeDocState() {
    }
    private static readonly ThunderDbStack._IMaybeDocState theDefault = create_NoState();
    public static ThunderDbStack._IMaybeDocState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState>(ThunderDbStack.MaybeDocState.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaybeDocState create_NoState() {
      return new MaybeDocState_NoState();
    }
    public static _IMaybeDocState create_HasState(BigInteger state) {
      return new MaybeDocState_HasState(state);
    }
    public bool is_NoState { get { return this is MaybeDocState_NoState; } }
    public bool is_HasState { get { return this is MaybeDocState_HasState; } }
    public BigInteger dtor_state {
      get {
        var d = this;
        return ((MaybeDocState_HasState)d)._state;
      }
    }
    public abstract _IMaybeDocState DowncastClone();
  }
  public class MaybeDocState_NoState : MaybeDocState {
    public MaybeDocState_NoState() : base() {
    }
    public override _IMaybeDocState DowncastClone() {
      if (this is _IMaybeDocState dt) { return dt; }
      return new MaybeDocState_NoState();
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MaybeDocState_NoState;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MaybeDocState.NoState";
      return s;
    }
  }
  public class MaybeDocState_HasState : MaybeDocState {
    public readonly BigInteger _state;
    public MaybeDocState_HasState(BigInteger state) : base() {
      this._state = state;
    }
    public override _IMaybeDocState DowncastClone() {
      if (this is _IMaybeDocState dt) { return dt; }
      return new MaybeDocState_HasState(_state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MaybeDocState_HasState;
      return oth != null && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MaybeDocState.HasState";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
  }

  public interface _ISeedDoc {
    bool is_SeedDoc { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_state { get; }
    _ISeedDoc DowncastClone();
  }
  public class SeedDoc : _ISeedDoc {
    public readonly BigInteger _id;
    public readonly BigInteger _state;
    public SeedDoc(BigInteger id, BigInteger state) {
      this._id = id;
      this._state = state;
    }
    public _ISeedDoc DowncastClone() {
      if (this is _ISeedDoc dt) { return dt; }
      return new SeedDoc(_id, _state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.SeedDoc;
      return oth != null && this._id == oth._id && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.SeedDoc.SeedDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._ISeedDoc theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._ISeedDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc>(ThunderDbStack.SeedDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISeedDoc create(BigInteger id, BigInteger state) {
      return new SeedDoc(id, state);
    }
    public static _ISeedDoc create_SeedDoc(BigInteger id, BigInteger state) {
      return create(id, state);
    }
    public bool is_SeedDoc { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
  }

  public interface _IQuerySpec {
    bool is_QuerySpec { get; }
    BigInteger dtor_minScore { get; }
    BigInteger dtor_maxScore { get; }
    BigInteger dtor_limit { get; }
    _IQuerySpec DowncastClone();
  }
  public class QuerySpec : _IQuerySpec {
    public readonly BigInteger _minScore;
    public readonly BigInteger _maxScore;
    public readonly BigInteger _limit;
    public QuerySpec(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      this._minScore = minScore;
      this._maxScore = maxScore;
      this._limit = limit;
    }
    public _IQuerySpec DowncastClone() {
      if (this is _IQuerySpec dt) { return dt; }
      return new QuerySpec(_minScore, _maxScore, _limit);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.QuerySpec;
      return oth != null && this._minScore == oth._minScore && this._maxScore == oth._maxScore && this._limit == oth._limit;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._minScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maxScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._limit));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.QuerySpec.QuerySpec";
      s += "(";
      s += Dafny.Helpers.ToString(this._minScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maxScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._limit);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IQuerySpec theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IQuerySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec>(ThunderDbStack.QuerySpec.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQuerySpec create(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      return new QuerySpec(minScore, maxScore, limit);
    }
    public static _IQuerySpec create_QuerySpec(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      return create(minScore, maxScore, limit);
    }
    public bool is_QuerySpec { get { return true; } }
    public BigInteger dtor_minScore {
      get {
        return this._minScore;
      }
    }
    public BigInteger dtor_maxScore {
      get {
        return this._maxScore;
      }
    }
    public BigInteger dtor_limit {
      get {
        return this._limit;
      }
    }
  }

  public interface _IEviction {
    bool is_Eviction { get; }
    BigInteger dtor_queryId { get; }
    BigInteger dtor_docId { get; }
    _IEviction DowncastClone();
  }
  public class Eviction : _IEviction {
    public readonly BigInteger _queryId;
    public readonly BigInteger _docId;
    public Eviction(BigInteger queryId, BigInteger docId) {
      this._queryId = queryId;
      this._docId = docId;
    }
    public _IEviction DowncastClone() {
      if (this is _IEviction dt) { return dt; }
      return new Eviction(_queryId, _docId);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.Eviction;
      return oth != null && this._queryId == oth._queryId && this._docId == oth._docId;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queryId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.Eviction.Eviction";
      s += "(";
      s += Dafny.Helpers.ToString(this._queryId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._docId);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IEviction theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IEviction Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IEviction> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IEviction>(ThunderDbStack.Eviction.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IEviction> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEviction create(BigInteger queryId, BigInteger docId) {
      return new Eviction(queryId, docId);
    }
    public static _IEviction create_Eviction(BigInteger queryId, BigInteger docId) {
      return create(queryId, docId);
    }
    public bool is_Eviction { get { return true; } }
    public BigInteger dtor_queryId {
      get {
        return this._queryId;
      }
    }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
  }

  public interface _IMatchPayload {
    bool is_MatchPayload { get; }
    BigInteger dtor_docId { get; }
    ThunderDbStack._IMaybeDocState dtor_oldState { get; }
    ThunderDbStack._IMaybeDocState dtor_newState { get; }
    Dafny.ISequence<BigInteger> dtor_matchesOld { get; }
    Dafny.ISequence<BigInteger> dtor_matchesNew { get; }
    Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions { get; }
    _IMatchPayload DowncastClone();
  }
  public class MatchPayload : _IMatchPayload {
    public readonly BigInteger _docId;
    public readonly ThunderDbStack._IMaybeDocState _oldState;
    public readonly ThunderDbStack._IMaybeDocState _newState;
    public readonly Dafny.ISequence<BigInteger> _matchesOld;
    public readonly Dafny.ISequence<BigInteger> _matchesNew;
    public readonly Dafny.ISequence<ThunderDbStack._IEviction> _evictions;
    public MatchPayload(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      this._docId = docId;
      this._oldState = oldState;
      this._newState = newState;
      this._matchesOld = matchesOld;
      this._matchesNew = matchesNew;
      this._evictions = evictions;
    }
    public _IMatchPayload DowncastClone() {
      if (this is _IMatchPayload dt) { return dt; }
      return new MatchPayload(_docId, _oldState, _newState, _matchesOld, _matchesNew, _evictions);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MatchPayload;
      return oth != null && this._docId == oth._docId && object.Equals(this._oldState, oth._oldState) && object.Equals(this._newState, oth._newState) && object.Equals(this._matchesOld, oth._matchesOld) && object.Equals(this._matchesNew, oth._matchesNew) && object.Equals(this._evictions, oth._evictions);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._oldState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._newState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchesOld));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchesNew));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._evictions));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MatchPayload.MatchPayload";
      s += "(";
      s += Dafny.Helpers.ToString(this._docId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._oldState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._newState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._matchesOld);
      s += ", ";
      s += Dafny.Helpers.ToString(this._matchesNew);
      s += ", ";
      s += Dafny.Helpers.ToString(this._evictions);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IMatchPayload theDefault = create(BigInteger.Zero, ThunderDbStack.MaybeDocState.Default(), ThunderDbStack.MaybeDocState.Default(), Dafny.Sequence<BigInteger>.Empty, Dafny.Sequence<BigInteger>.Empty, Dafny.Sequence<ThunderDbStack._IEviction>.Empty);
    public static ThunderDbStack._IMatchPayload Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload>(ThunderDbStack.MatchPayload.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMatchPayload create(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return new MatchPayload(docId, oldState, newState, matchesOld, matchesNew, evictions);
    }
    public static _IMatchPayload create_MatchPayload(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return create(docId, oldState, newState, matchesOld, matchesNew, evictions);
    }
    public bool is_MatchPayload { get { return true; } }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_oldState {
      get {
        return this._oldState;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_newState {
      get {
        return this._newState;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_matchesOld {
      get {
        return this._matchesOld;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_matchesNew {
      get {
        return this._matchesNew;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions {
      get {
        return this._evictions;
      }
    }
  }

  public interface _IRetrievalDoc {
    bool is_RetrievalDoc { get; }
    BigInteger dtor_docId { get; }
    BigInteger dtor_state { get; }
    Dafny.ISequence<BigInteger> dtor_queries { get; }
    _IRetrievalDoc DowncastClone();
  }
  public class RetrievalDoc : _IRetrievalDoc {
    public readonly BigInteger _docId;
    public readonly BigInteger _state;
    public readonly Dafny.ISequence<BigInteger> _queries;
    public RetrievalDoc(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      this._docId = docId;
      this._state = state;
      this._queries = queries;
    }
    public _IRetrievalDoc DowncastClone() {
      if (this is _IRetrievalDoc dt) { return dt; }
      return new RetrievalDoc(_docId, _state, _queries);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.RetrievalDoc;
      return oth != null && this._docId == oth._docId && this._state == oth._state && object.Equals(this._queries, oth._queries);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queries));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.RetrievalDoc.RetrievalDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._docId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queries);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IRetrievalDoc theDefault = create(BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<BigInteger>.Empty);
    public static ThunderDbStack._IRetrievalDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc>(ThunderDbStack.RetrievalDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRetrievalDoc create(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      return new RetrievalDoc(docId, state, queries);
    }
    public static _IRetrievalDoc create_RetrievalDoc(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      return create(docId, state, queries);
    }
    public bool is_RetrievalDoc { get { return true; } }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_queries {
      get {
        return this._queries;
      }
    }
  }

  public interface _IDownstreamEvent {
    bool is_MatchEvent { get; }
    bool is_RetrievalEvent { get; }
    ThunderDbStack._IMatchPayload dtor_payload { get; }
    Dafny.ISequence<ThunderDbStack._IRetrievalDoc> dtor_docs { get; }
    _IDownstreamEvent DowncastClone();
  }
  public abstract class DownstreamEvent : _IDownstreamEvent {
    public DownstreamEvent() {
    }
    private static readonly ThunderDbStack._IDownstreamEvent theDefault = create_MatchEvent(ThunderDbStack.MatchPayload.Default());
    public static ThunderDbStack._IDownstreamEvent Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent>(ThunderDbStack.DownstreamEvent.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDownstreamEvent create_MatchEvent(ThunderDbStack._IMatchPayload payload) {
      return new DownstreamEvent_MatchEvent(payload);
    }
    public static _IDownstreamEvent create_RetrievalEvent(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs) {
      return new DownstreamEvent_RetrievalEvent(docs);
    }
    public bool is_MatchEvent { get { return this is DownstreamEvent_MatchEvent; } }
    public bool is_RetrievalEvent { get { return this is DownstreamEvent_RetrievalEvent; } }
    public ThunderDbStack._IMatchPayload dtor_payload {
      get {
        var d = this;
        return ((DownstreamEvent_MatchEvent)d)._payload;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IRetrievalDoc> dtor_docs {
      get {
        var d = this;
        return ((DownstreamEvent_RetrievalEvent)d)._docs;
      }
    }
    public abstract _IDownstreamEvent DowncastClone();
  }
  public class DownstreamEvent_MatchEvent : DownstreamEvent {
    public readonly ThunderDbStack._IMatchPayload _payload;
    public DownstreamEvent_MatchEvent(ThunderDbStack._IMatchPayload payload) : base() {
      this._payload = payload;
    }
    public override _IDownstreamEvent DowncastClone() {
      if (this is _IDownstreamEvent dt) { return dt; }
      return new DownstreamEvent_MatchEvent(_payload);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DownstreamEvent_MatchEvent;
      return oth != null && object.Equals(this._payload, oth._payload);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._payload));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DownstreamEvent.MatchEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._payload);
      s += ")";
      return s;
    }
  }
  public class DownstreamEvent_RetrievalEvent : DownstreamEvent {
    public readonly Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _docs;
    public DownstreamEvent_RetrievalEvent(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs) : base() {
      this._docs = docs;
    }
    public override _IDownstreamEvent DowncastClone() {
      if (this is _IDownstreamEvent dt) { return dt; }
      return new DownstreamEvent_RetrievalEvent(_docs);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DownstreamEvent_RetrievalEvent;
      return oth != null && object.Equals(this._docs, oth._docs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DownstreamEvent.RetrievalEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._docs);
      s += ")";
      return s;
    }
  }

  public interface _IStreamItem {
    bool is_DocChangeItem { get; }
    bool is_QueryAddItem { get; }
    bool is_QueryRemoveItem { get; }
    bool is_SeedDocsItem { get; }
    BigInteger dtor_id { get; }
    ThunderDbStack._IMaybeDocState dtor_oldState { get; }
    ThunderDbStack._IMaybeDocState dtor_newState { get; }
    ThunderDbStack._IQuerySpec dtor_spec { get; }
    Dafny.ISequence<ThunderDbStack._ISeedDoc> dtor_docs { get; }
    _IStreamItem DowncastClone();
  }
  public abstract class StreamItem : _IStreamItem {
    public StreamItem() {
    }
    private static readonly ThunderDbStack._IStreamItem theDefault = create_DocChangeItem(BigInteger.Zero, ThunderDbStack.MaybeDocState.Default(), ThunderDbStack.MaybeDocState.Default());
    public static ThunderDbStack._IStreamItem Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IStreamItem> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IStreamItem>(ThunderDbStack.StreamItem.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IStreamItem> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStreamItem create_DocChangeItem(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState) {
      return new StreamItem_DocChangeItem(id, oldState, newState);
    }
    public static _IStreamItem create_QueryAddItem(ThunderDbStack._IQuerySpec spec) {
      return new StreamItem_QueryAddItem(spec);
    }
    public static _IStreamItem create_QueryRemoveItem(BigInteger id) {
      return new StreamItem_QueryRemoveItem(id);
    }
    public static _IStreamItem create_SeedDocsItem(Dafny.ISequence<ThunderDbStack._ISeedDoc> docs) {
      return new StreamItem_SeedDocsItem(docs);
    }
    public bool is_DocChangeItem { get { return this is StreamItem_DocChangeItem; } }
    public bool is_QueryAddItem { get { return this is StreamItem_QueryAddItem; } }
    public bool is_QueryRemoveItem { get { return this is StreamItem_QueryRemoveItem; } }
    public bool is_SeedDocsItem { get { return this is StreamItem_SeedDocsItem; } }
    public BigInteger dtor_id {
      get {
        var d = this;
        if (d is StreamItem_DocChangeItem) { return ((StreamItem_DocChangeItem)d)._id; }
        return ((StreamItem_QueryRemoveItem)d)._id;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_oldState {
      get {
        var d = this;
        return ((StreamItem_DocChangeItem)d)._oldState;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_newState {
      get {
        var d = this;
        return ((StreamItem_DocChangeItem)d)._newState;
      }
    }
    public ThunderDbStack._IQuerySpec dtor_spec {
      get {
        var d = this;
        return ((StreamItem_QueryAddItem)d)._spec;
      }
    }
    public Dafny.ISequence<ThunderDbStack._ISeedDoc> dtor_docs {
      get {
        var d = this;
        return ((StreamItem_SeedDocsItem)d)._docs;
      }
    }
    public abstract _IStreamItem DowncastClone();
  }
  public class StreamItem_DocChangeItem : StreamItem {
    public readonly BigInteger _id;
    public readonly ThunderDbStack._IMaybeDocState _oldState;
    public readonly ThunderDbStack._IMaybeDocState _newState;
    public StreamItem_DocChangeItem(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState) : base() {
      this._id = id;
      this._oldState = oldState;
      this._newState = newState;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_DocChangeItem(_id, _oldState, _newState);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_DocChangeItem;
      return oth != null && this._id == oth._id && object.Equals(this._oldState, oth._oldState) && object.Equals(this._newState, oth._newState);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._oldState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._newState));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.DocChangeItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._oldState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._newState);
      s += ")";
      return s;
    }
  }
  public class StreamItem_QueryAddItem : StreamItem {
    public readonly ThunderDbStack._IQuerySpec _spec;
    public StreamItem_QueryAddItem(ThunderDbStack._IQuerySpec spec) : base() {
      this._spec = spec;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_QueryAddItem(_spec);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_QueryAddItem;
      return oth != null && object.Equals(this._spec, oth._spec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._spec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.QueryAddItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._spec);
      s += ")";
      return s;
    }
  }
  public class StreamItem_QueryRemoveItem : StreamItem {
    public readonly BigInteger _id;
    public StreamItem_QueryRemoveItem(BigInteger id) : base() {
      this._id = id;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_QueryRemoveItem(_id);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_QueryRemoveItem;
      return oth != null && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.QueryRemoveItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
  }
  public class StreamItem_SeedDocsItem : StreamItem {
    public readonly Dafny.ISequence<ThunderDbStack._ISeedDoc> _docs;
    public StreamItem_SeedDocsItem(Dafny.ISequence<ThunderDbStack._ISeedDoc> docs) : base() {
      this._docs = docs;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_SeedDocsItem(_docs);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_SeedDocsItem;
      return oth != null && object.Equals(this._docs, oth._docs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.SeedDocsItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._docs);
      s += ")";
      return s;
    }
  }
} // end of namespace ThunderDbStack
namespace TsDocsRuntime {

  public partial class __default {
    public static Dafny.ISequence<DocsIndexModel._IEntry> EmptyDocsState() {
      return Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    }
    public static bool DocsConsistent(Dafny.ISequence<DocsIndexModel._IEntry> state) {
      return DocsIndexModel.__default.SortedEntries((state));
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> AddDoc(Dafny.ISequence<DocsIndexModel._IEntry> state, BigInteger score, BigInteger id)
    {
      return DocsIndexModel.__default.InsertUnique((state), score, id);
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> RemoveDoc(Dafny.ISequence<DocsIndexModel._IEntry> state, BigInteger score, BigInteger id)
    {
      return DocsIndexModel.__default.RemoveOne((state), score, id);
    }
    public static BigInteger RankDoc(Dafny.ISequence<DocsIndexModel._IEntry> state, BigInteger score, DocsIndexModel._IMaybeDocId id)
    {
      return DocsIndexModel.__default.Rank((state), score, id);
    }
    public static BigInteger CountAtMostDoc(Dafny.ISequence<DocsIndexModel._IEntry> state, BigInteger score)
    {
      return DocsIndexModel.__default.CountAtMost((state), score);
    }
    public static DocsIndexModel._IAtRank GetAtRankDoc(Dafny.ISequence<DocsIndexModel._IEntry> state, BigInteger rank)
    {
      return DocsIndexModel.__default.GetAtRank((state), rank);
    }
    public static Dafny.ISequence<BigInteger> CollectRangeDocs(Dafny.ISequence<DocsIndexModel._IEntry> state, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      return DocsIndexModel.__default.CollectRange((state), minScore, maxScore, limit);
    }
  }

  public interface _IDocsState {
    bool is_DocsState { get; }
    Dafny.ISequence<DocsIndexModel._IEntry> dtor_entries { get; }
  }
  public class DocsState : _IDocsState {
    public readonly Dafny.ISequence<DocsIndexModel._IEntry> _entries;
    public DocsState(Dafny.ISequence<DocsIndexModel._IEntry> entries) {
      this._entries = entries;
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> DowncastClone(Dafny.ISequence<DocsIndexModel._IEntry> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as TsDocsRuntime.DocsState;
      return oth != null && object.Equals(this._entries, oth._entries);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._entries));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsDocsRuntime.DocsState.DocsState";
      s += "(";
      s += Dafny.Helpers.ToString(this._entries);
      s += ")";
      return s;
    }
    private static readonly Dafny.ISequence<DocsIndexModel._IEntry> theDefault = Dafny.Sequence<DocsIndexModel._IEntry>.Empty;
    public static Dafny.ISequence<DocsIndexModel._IEntry> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<DocsIndexModel._IEntry>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<DocsIndexModel._IEntry>>(Dafny.Sequence<DocsIndexModel._IEntry>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<DocsIndexModel._IEntry>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDocsState create(Dafny.ISequence<DocsIndexModel._IEntry> entries) {
      return new DocsState(entries);
    }
    public static _IDocsState create_DocsState(Dafny.ISequence<DocsIndexModel._IEntry> entries) {
      return create(entries);
    }
    public bool is_DocsState { get { return true; } }
    public Dafny.ISequence<DocsIndexModel._IEntry> dtor_entries {
      get {
        return this._entries;
      }
    }
  }
} // end of namespace TsDocsRuntime
namespace TsQueriesRuntime {

  public partial class __default {
    public static TsQueriesRuntime._IQueriesState EmptyQueriesState() {
      return TsQueriesRuntime.QueriesState.create(Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements(), Dafny.Sequence<TsQueriesRuntime._IRangeAddOp>.FromElements());
    }
    public static bool UniqueQueryEntries(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries) {
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return true;
      } else {
        return (!(TsQueriesRuntime.__default.ContainsQueryEntryId((entries).Drop(BigInteger.One), ((entries).Select(BigInteger.Zero)).dtor_id))) && (TsQueriesRuntime.__default.UniqueQueryEntries((entries).Drop(BigInteger.One)));
      }
    }
    public static bool EntryIdsBelow(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, BigInteger bound)
    {
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return true;
      } else {
        return ((((entries).Select(BigInteger.Zero)).dtor_id) < (bound)) && (TsQueriesRuntime.__default.EntryIdsBelow((entries).Drop(BigInteger.One), bound));
      }
    }
    public static bool ContainsQueryEntryId(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, BigInteger id)
    {
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return false;
      } else {
        return ((((entries).Select(BigInteger.Zero)).dtor_id) == (id)) || (TsQueriesRuntime.__default.ContainsQueryEntryId((entries).Drop(BigInteger.One), id));
      }
    }
    public static bool OrderedEntries(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries) {
      if ((new BigInteger((entries).Count)) < (new BigInteger(2))) {
        return true;
      } else {
        return (TsQueriesRuntime.__default.CompareEntries((entries).Select(BigInteger.Zero), (entries).Select(BigInteger.One))) && (TsQueriesRuntime.__default.OrderedEntries((entries).Drop(BigInteger.One)));
      }
    }
    public static bool QueriesConsistent(TsQueriesRuntime._IQueriesState state) {
      return (TsQueriesRuntime.__default.UniqueQueryEntries((state).dtor_entries)) && (TsQueriesRuntime.__default.OrderedEntries((state).dtor_entries));
    }
    public static BigInteger SumRangeAddsAtKey(Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> ops, BigInteger key)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((ops).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((ops).Select(BigInteger.Zero)).dtor_threshold) < (key)) ? (((ops).Select(BigInteger.Zero)).dtor_delta) : (BigInteger.Zero)));
        Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> _in0 = (ops).Drop(BigInteger.One);
        BigInteger _in1 = key;
        ops = _in0;
        key = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger AccumulatedAddAtKey(TsQueriesRuntime._IQueriesState state, BigInteger key)
    {
      return TsQueriesRuntime.__default.SumRangeAddsAtKey((state).dtor_rangeAdds, key);
    }
    public static BigInteger EffectiveScore(TsQueriesRuntime._IQueriesState state, TsQueriesRuntime._IQueryEntry entry)
    {
      return ((entry).dtor_baseScore) + (TsQueriesRuntime.__default.AccumulatedAddAtKey(state, (entry).dtor_key));
    }
    public static TsQueriesRuntime._IQueriesState RangeAddKeysGreaterThan(TsQueriesRuntime._IQueriesState state, BigInteger threshold, BigInteger delta)
    {
      return TsQueriesRuntime.QueriesState.create((state).dtor_entries, Dafny.Sequence<TsQueriesRuntime._IRangeAddOp>.Concat((state).dtor_rangeAdds, Dafny.Sequence<TsQueriesRuntime._IRangeAddOp>.FromElements(TsQueriesRuntime.RangeAddOp.create(threshold, delta))));
    }
    public static bool CompareEntries(TsQueriesRuntime._IQueryEntry left, TsQueriesRuntime._IQueryEntry right)
    {
      return (((left).dtor_key) < ((right).dtor_key)) || ((((left).dtor_key) == ((right).dtor_key)) && ((((left).dtor_baseScore) < ((right).dtor_baseScore)) || ((((left).dtor_baseScore) == ((right).dtor_baseScore)) && (((left).dtor_id) < ((right).dtor_id)))));
    }
    public static Dafny.ISequence<TsQueriesRuntime._IQueryEntry> InsertEntrySorted(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, TsQueriesRuntime._IQueryEntry entry)
    {
      Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _0___accumulator = Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Concat(_0___accumulator, Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements(entry));
      } else if (TsQueriesRuntime.__default.CompareEntries(entry, (entries).Select(BigInteger.Zero))) {
        return Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Concat(_0___accumulator, Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Concat(Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements(entry), entries));
      } else {
        _0___accumulator = Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Concat(_0___accumulator, Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements((entries).Select(BigInteger.Zero)));
        Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _in0 = (entries).Drop(BigInteger.One);
        TsQueriesRuntime._IQueryEntry _in1 = entry;
        entries = _in0;
        entry = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static TsQueriesRuntime._IQueriesState Insert(TsQueriesRuntime._IQueriesState state, BigInteger key, BigInteger id, BigInteger effectiveScore, BigInteger maxCap)
    {
      BigInteger _0_baseScore = (effectiveScore) - (TsQueriesRuntime.__default.AccumulatedAddAtKey(state, key));
      Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _1_entries = TsQueriesRuntime.__default.InsertEntrySorted((state).dtor_entries, TsQueriesRuntime.QueryEntry.create(id, key, _0_baseScore, maxCap));
      return TsQueriesRuntime.QueriesState.create(_1_entries, (state).dtor_rangeAdds);
    }
    public static Dafny.ISequence<TsQueriesRuntime._IQueryEntry> RemoveEntries(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, BigInteger key, BigInteger id, BigInteger baseScore, BigInteger maxCap)
    {
      Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _0___accumulator = Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Concat(_0___accumulator, Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements());
      } else if (object.Equals((entries).Select(BigInteger.Zero), TsQueriesRuntime.QueryEntry.create(id, key, baseScore, maxCap))) {
        return Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Concat(_0___accumulator, (entries).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Concat(_0___accumulator, Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.FromElements((entries).Select(BigInteger.Zero)));
        Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _in0 = (entries).Drop(BigInteger.One);
        BigInteger _in1 = key;
        BigInteger _in2 = id;
        BigInteger _in3 = baseScore;
        BigInteger _in4 = maxCap;
        entries = _in0;
        key = _in1;
        id = _in2;
        baseScore = _in3;
        maxCap = _in4;
        goto TAIL_CALL_START;
      }
    }
    public static TsQueriesRuntime._IQueriesState Remove(TsQueriesRuntime._IQueriesState state, BigInteger key, BigInteger id, BigInteger baseScore, BigInteger maxCap)
    {
      return TsQueriesRuntime.QueriesState.create(TsQueriesRuntime.__default.RemoveEntries((state).dtor_entries, key, id, baseScore, maxCap), (state).dtor_rangeAdds);
    }
    public static Dafny.ISequence<BigInteger> CollectForValue(TsQueriesRuntime._IQueriesState state, BigInteger @value, BigInteger cutoff)
    {
      return TsQueriesRuntime.__default.CollectMatchingEntries(state, (state).dtor_entries, @value, cutoff);
    }
    public static Dafny.ISequence<BigInteger> CollectMatchingEntries(TsQueriesRuntime._IQueriesState state, Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, BigInteger @value, BigInteger cutoff)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if ((((((entries).Select(BigInteger.Zero)).dtor_key) <= (@value)) && ((@value) <= (((entries).Select(BigInteger.Zero)).dtor_maxCap))) && ((cutoff) < (TsQueriesRuntime.__default.EffectiveScore(state, (entries).Select(BigInteger.Zero))))) {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((entries).Select(BigInteger.Zero)).dtor_id));
        TsQueriesRuntime._IQueriesState _in0 = state;
        Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _in1 = (entries).Drop(BigInteger.One);
        BigInteger _in2 = @value;
        BigInteger _in3 = cutoff;
        state = _in0;
        entries = _in1;
        @value = _in2;
        cutoff = _in3;
        goto TAIL_CALL_START;
      } else {
        TsQueriesRuntime._IQueriesState _in4 = state;
        Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _in5 = (entries).Drop(BigInteger.One);
        BigInteger _in6 = @value;
        BigInteger _in7 = cutoff;
        state = _in4;
        entries = _in5;
        @value = _in6;
        cutoff = _in7;
        goto TAIL_CALL_START;
      }
    }
  }

  public interface _IRangeAddOp {
    bool is_RangeAddOp { get; }
    BigInteger dtor_threshold { get; }
    BigInteger dtor_delta { get; }
    _IRangeAddOp DowncastClone();
  }
  public class RangeAddOp : _IRangeAddOp {
    public readonly BigInteger _threshold;
    public readonly BigInteger _delta;
    public RangeAddOp(BigInteger threshold, BigInteger delta) {
      this._threshold = threshold;
      this._delta = delta;
    }
    public _IRangeAddOp DowncastClone() {
      if (this is _IRangeAddOp dt) { return dt; }
      return new RangeAddOp(_threshold, _delta);
    }
    public override bool Equals(object other) {
      var oth = other as TsQueriesRuntime.RangeAddOp;
      return oth != null && this._threshold == oth._threshold && this._delta == oth._delta;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._threshold));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._delta));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsQueriesRuntime.RangeAddOp.RangeAddOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._threshold);
      s += ", ";
      s += Dafny.Helpers.ToString(this._delta);
      s += ")";
      return s;
    }
    private static readonly TsQueriesRuntime._IRangeAddOp theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static TsQueriesRuntime._IRangeAddOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsQueriesRuntime._IRangeAddOp> _TYPE = new Dafny.TypeDescriptor<TsQueriesRuntime._IRangeAddOp>(TsQueriesRuntime.RangeAddOp.Default());
    public static Dafny.TypeDescriptor<TsQueriesRuntime._IRangeAddOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRangeAddOp create(BigInteger threshold, BigInteger delta) {
      return new RangeAddOp(threshold, delta);
    }
    public static _IRangeAddOp create_RangeAddOp(BigInteger threshold, BigInteger delta) {
      return create(threshold, delta);
    }
    public bool is_RangeAddOp { get { return true; } }
    public BigInteger dtor_threshold {
      get {
        return this._threshold;
      }
    }
    public BigInteger dtor_delta {
      get {
        return this._delta;
      }
    }
  }

  public interface _IQueryEntry {
    bool is_QueryEntry { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_key { get; }
    BigInteger dtor_baseScore { get; }
    BigInteger dtor_maxCap { get; }
    _IQueryEntry DowncastClone();
  }
  public class QueryEntry : _IQueryEntry {
    public readonly BigInteger _id;
    public readonly BigInteger _key;
    public readonly BigInteger _baseScore;
    public readonly BigInteger _maxCap;
    public QueryEntry(BigInteger id, BigInteger key, BigInteger baseScore, BigInteger maxCap) {
      this._id = id;
      this._key = key;
      this._baseScore = baseScore;
      this._maxCap = maxCap;
    }
    public _IQueryEntry DowncastClone() {
      if (this is _IQueryEntry dt) { return dt; }
      return new QueryEntry(_id, _key, _baseScore, _maxCap);
    }
    public override bool Equals(object other) {
      var oth = other as TsQueriesRuntime.QueryEntry;
      return oth != null && this._id == oth._id && this._key == oth._key && this._baseScore == oth._baseScore && this._maxCap == oth._maxCap;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maxCap));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsQueriesRuntime.QueryEntry.QueryEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._baseScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maxCap);
      s += ")";
      return s;
    }
    private static readonly TsQueriesRuntime._IQueryEntry theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static TsQueriesRuntime._IQueryEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsQueriesRuntime._IQueryEntry> _TYPE = new Dafny.TypeDescriptor<TsQueriesRuntime._IQueryEntry>(TsQueriesRuntime.QueryEntry.Default());
    public static Dafny.TypeDescriptor<TsQueriesRuntime._IQueryEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryEntry create(BigInteger id, BigInteger key, BigInteger baseScore, BigInteger maxCap) {
      return new QueryEntry(id, key, baseScore, maxCap);
    }
    public static _IQueryEntry create_QueryEntry(BigInteger id, BigInteger key, BigInteger baseScore, BigInteger maxCap) {
      return create(id, key, baseScore, maxCap);
    }
    public bool is_QueryEntry { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_key {
      get {
        return this._key;
      }
    }
    public BigInteger dtor_baseScore {
      get {
        return this._baseScore;
      }
    }
    public BigInteger dtor_maxCap {
      get {
        return this._maxCap;
      }
    }
  }

  public interface _IQueriesState {
    bool is_QueriesState { get; }
    Dafny.ISequence<TsQueriesRuntime._IQueryEntry> dtor_entries { get; }
    Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> dtor_rangeAdds { get; }
    _IQueriesState DowncastClone();
  }
  public class QueriesState : _IQueriesState {
    public readonly Dafny.ISequence<TsQueriesRuntime._IQueryEntry> _entries;
    public readonly Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> _rangeAdds;
    public QueriesState(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> rangeAdds) {
      this._entries = entries;
      this._rangeAdds = rangeAdds;
    }
    public _IQueriesState DowncastClone() {
      if (this is _IQueriesState dt) { return dt; }
      return new QueriesState(_entries, _rangeAdds);
    }
    public override bool Equals(object other) {
      var oth = other as TsQueriesRuntime.QueriesState;
      return oth != null && object.Equals(this._entries, oth._entries) && object.Equals(this._rangeAdds, oth._rangeAdds);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._entries));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rangeAdds));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsQueriesRuntime.QueriesState.QueriesState";
      s += "(";
      s += Dafny.Helpers.ToString(this._entries);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rangeAdds);
      s += ")";
      return s;
    }
    private static readonly TsQueriesRuntime._IQueriesState theDefault = create(Dafny.Sequence<TsQueriesRuntime._IQueryEntry>.Empty, Dafny.Sequence<TsQueriesRuntime._IRangeAddOp>.Empty);
    public static TsQueriesRuntime._IQueriesState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsQueriesRuntime._IQueriesState> _TYPE = new Dafny.TypeDescriptor<TsQueriesRuntime._IQueriesState>(TsQueriesRuntime.QueriesState.Default());
    public static Dafny.TypeDescriptor<TsQueriesRuntime._IQueriesState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueriesState create(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> rangeAdds) {
      return new QueriesState(entries, rangeAdds);
    }
    public static _IQueriesState create_QueriesState(Dafny.ISequence<TsQueriesRuntime._IQueryEntry> entries, Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> rangeAdds) {
      return create(entries, rangeAdds);
    }
    public bool is_QueriesState { get { return true; } }
    public Dafny.ISequence<TsQueriesRuntime._IQueryEntry> dtor_entries {
      get {
        return this._entries;
      }
    }
    public Dafny.ISequence<TsQueriesRuntime._IRangeAddOp> dtor_rangeAdds {
      get {
        return this._rangeAdds;
      }
    }
  }
} // end of namespace TsQueriesRuntime
namespace TsLimitQueriesRuntime {

  public partial class __default {
    public static TsLimitQueriesRuntime._ILimitQueriesState EmptyLimitQueriesState() {
      return TsLimitQueriesRuntime.LimitQueriesState.create(TsDocsRuntime.__default.EmptyDocsState(), TsQueriesRuntime.__default.EmptyQueriesState(), BigInteger.One, Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.FromElements(), Dafny.Map<BigInteger, BigInteger>.FromElements(), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements(), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements());
    }
    public static bool LimitQueriesConsistent(TsLimitQueriesRuntime._ILimitQueriesState state) {
      return ((((TsDocsRuntime.__default.DocsConsistent((state).dtor_docs)) && (TsQueriesRuntime.__default.QueriesConsistent((state).dtor_queries))) && ((BigInteger.One) <= ((state).dtor_nextId))) && (TsQueriesRuntime.__default.EntryIdsBelow(((state).dtor_queries).dtor_entries, (state).dtor_nextId))) && (Dafny.Helpers.Id<Func<TsLimitQueriesRuntime._ILimitQueriesState, bool>>((_0_state) => Dafny.Helpers.Quantifier<BigInteger>(((_0_state).dtor_infos).Keys.Elements, true, (((_forall_var_0) => {
        BigInteger _1_id = (BigInteger)_forall_var_0;
        return !(((_0_state).dtor_infos).Contains(_1_id)) || ((((_0_state).dtor_baseScores).Contains(_1_id)) && (((Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((_0_state).dtor_infos,_1_id)).dtor_id) == (_1_id)));
      }))))(state));
    }
    public static BigInteger NatMin(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static Dafny.ISequence<BigInteger> RemoveQueryId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (((ids).Select(BigInteger.Zero)) == (id)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, (ids).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState SetCurrentMatches(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId, BigInteger currentMatches)
    {
      TsLimitQueriesRuntime._IQueryInfo _0_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,queryId);
      return TsLimitQueriesRuntime.LimitQueriesState.create((state).dtor_docs, (state).dtor_queries, (state).dtor_nextId, Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Update((state).dtor_infos, queryId, TsLimitQueriesRuntime.QueryInfo.create((_0_info).dtor_id, (_0_info).dtor_a, (_0_info).dtor_k, (_0_info).dtor_max, currentMatches)), (state).dtor_baseScores, (state).dtor_pendingByQuery, (state).dtor_pendingByDoc);
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState AddPendingPair(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId, BigInteger docId)
    {
      Dafny.ISequence<BigInteger> _0_docsForQuery = ((((state).dtor_pendingByQuery).Contains(queryId)) ? (ThunderDbStack.__default.AppendDocIdIfMissing(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByQuery,queryId), docId)) : (Dafny.Sequence<BigInteger>.FromElements(docId)));
      Dafny.ISequence<BigInteger> _1_queriesForDoc = ((((state).dtor_pendingByDoc).Contains(docId)) ? (ThunderDbStack.__default.AppendQueryIdUnique(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByDoc,docId), queryId)) : (Dafny.Sequence<BigInteger>.FromElements(queryId)));
      return TsLimitQueriesRuntime.LimitQueriesState.create((state).dtor_docs, (state).dtor_queries, (state).dtor_nextId, (state).dtor_infos, (state).dtor_baseScores, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update((state).dtor_pendingByQuery, queryId, _0_docsForQuery), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update((state).dtor_pendingByDoc, docId, _1_queriesForDoc));
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState RemovePendingPair(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId, BigInteger docId)
    {
      var _pat_let_tv0 = state;
      var _pat_let_tv1 = queryId;
      var _pat_let_tv2 = state;
      var _pat_let_tv3 = queryId;
      var _pat_let_tv4 = state;
      var _pat_let_tv5 = docId;
      var _pat_let_tv6 = state;
      var _pat_let_tv7 = docId;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _0_nextPendingByQuery = (((((state).dtor_pendingByQuery).Contains(queryId)) && (ThunderDbStack.__default.ContainsId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByQuery,queryId), docId))) ? (Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>(ThunderDbStack.__default.RemoveDocId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByQuery,queryId), docId), _pat_let0_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>(_pat_let0_0, _1_nextDocs => (((new BigInteger((_1_nextDocs).Count)).Sign == 0) ? (Dafny.Helpers.Id<Func<TsLimitQueriesRuntime._ILimitQueriesState, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_2_state, _3_queryId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
        foreach (BigInteger _compr_0 in ((_2_state).dtor_pendingByQuery).Keys.Elements) {
          BigInteger _4_key = (BigInteger)_compr_0;
          if ((((_2_state).dtor_pendingByQuery).Contains(_4_key)) && ((_4_key) != (_3_queryId))) {
            _coll0.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_4_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_2_state).dtor_pendingByQuery,_4_key)));
          }
        }
        return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll0);
      }))())(_pat_let_tv0, _pat_let_tv1)) : (Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update((_pat_let_tv2).dtor_pendingByQuery, _pat_let_tv3, _1_nextDocs)))))) : ((state).dtor_pendingByQuery));
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _5_nextPendingByDoc = (((((state).dtor_pendingByDoc).Contains(docId)) && (ThunderDbStack.__default.ContainsQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByDoc,docId), queryId))) ? (Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>(TsLimitQueriesRuntime.__default.RemoveQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByDoc,docId), queryId), _pat_let1_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>(_pat_let1_0, _6_nextQueries => (((new BigInteger((_6_nextQueries).Count)).Sign == 0) ? (Dafny.Helpers.Id<Func<TsLimitQueriesRuntime._ILimitQueriesState, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_7_state, _8_docId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
        var _coll1 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
        foreach (BigInteger _compr_1 in ((_7_state).dtor_pendingByDoc).Keys.Elements) {
          BigInteger _9_key = (BigInteger)_compr_1;
          if ((((_7_state).dtor_pendingByDoc).Contains(_9_key)) && ((_9_key) != (_8_docId))) {
            _coll1.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_9_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_7_state).dtor_pendingByDoc,_9_key)));
          }
        }
        return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll1);
      }))())(_pat_let_tv4, _pat_let_tv5)) : (Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update((_pat_let_tv6).dtor_pendingByDoc, _pat_let_tv7, _6_nextQueries)))))) : ((state).dtor_pendingByDoc));
      return TsLimitQueriesRuntime.LimitQueriesState.create((state).dtor_docs, (state).dtor_queries, (state).dtor_nextId, (state).dtor_infos, (state).dtor_baseScores, _0_nextPendingByQuery, _5_nextPendingByDoc);
    }
    public static BigInteger CountDocsInRange(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger minScore, BigInteger maxScore)
    {
      BigInteger _0_upper = TsDocsRuntime.__default.CountAtMostDoc((state).dtor_docs, maxScore);
      BigInteger _1_lower = TsDocsRuntime.__default.RankDoc((state).dtor_docs, minScore, DocsIndexModel.MaybeDocId.create_NoDoc());
      if ((_1_lower) <= (_0_upper)) {
        return (_0_upper) - (_1_lower);
      } else {
        return BigInteger.Zero;
      }
    }
    public static TsLimitQueriesRuntime._IQueryAddResult AddQuery(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger a, BigInteger k, BigInteger max)
    {
      BigInteger _0_queryId = (state).dtor_nextId;
      BigInteger _1_effectiveScore = (TsDocsRuntime.__default.RankDoc((state).dtor_docs, a, DocsIndexModel.MaybeDocId.create_NoDoc())) + (k);
      TsQueriesRuntime._IQueriesState _2_nextQueries = TsQueriesRuntime.__default.Insert((state).dtor_queries, a, (state).dtor_nextId, _1_effectiveScore, max);
      BigInteger _3_baseScore = (_1_effectiveScore) - (TsQueriesRuntime.__default.AccumulatedAddAtKey((state).dtor_queries, a));
      BigInteger _4_currentMatches = TsLimitQueriesRuntime.__default.NatMin(TsLimitQueriesRuntime.__default.CountDocsInRange(state, a, max), k);
      return TsLimitQueriesRuntime.QueryAddResult.create(TsLimitQueriesRuntime.LimitQueriesState.create((state).dtor_docs, _2_nextQueries, (_0_queryId) + (BigInteger.One), Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Update((state).dtor_infos, _0_queryId, TsLimitQueriesRuntime.QueryInfo.create(_0_queryId, a, k, max, _4_currentMatches)), Dafny.Map<BigInteger, BigInteger>.Update((state).dtor_baseScores, _0_queryId, _3_baseScore), (state).dtor_pendingByQuery, (state).dtor_pendingByDoc), _0_queryId);
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState RemovePendingDocsForQuery(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> docs, BigInteger queryId)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return state;
      } else {
        TsLimitQueriesRuntime._ILimitQueriesState _in0 = TsLimitQueriesRuntime.__default.RemovePendingPair(state, queryId, (docs).Select(BigInteger.Zero));
        Dafny.ISequence<BigInteger> _in1 = (docs).Drop(BigInteger.One);
        BigInteger _in2 = queryId;
        state = _in0;
        docs = _in1;
        queryId = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitQueriesRuntime._IStateChange RemoveQuery(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId)
    {
      if ((!(((state).dtor_infos).Contains(queryId))) || (!(((state).dtor_baseScores).Contains(queryId)))) {
        return TsLimitQueriesRuntime.StateChange.create(state, false);
      } else {
        TsLimitQueriesRuntime._IQueryInfo _0_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,queryId);
        BigInteger _1_baseScore = Dafny.Map<BigInteger, BigInteger>.Select((state).dtor_baseScores,queryId);
        TsLimitQueriesRuntime._ILimitQueriesState _2_state1 = TsLimitQueriesRuntime.LimitQueriesState.create((state).dtor_docs, TsQueriesRuntime.__default.Remove((state).dtor_queries, (_0_info).dtor_a, queryId, _1_baseScore, (_0_info).dtor_max), (state).dtor_nextId, Dafny.Helpers.Id<Func<TsLimitQueriesRuntime._ILimitQueriesState, BigInteger, Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo>>>((_3_state, _4_queryId) => ((System.Func<Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo>>)(() => {
  var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,TsLimitQueriesRuntime._IQueryInfo>>();
  foreach (BigInteger _compr_0 in ((_3_state).dtor_infos).Keys.Elements) {
    BigInteger _5_key = (BigInteger)_compr_0;
    if ((((_3_state).dtor_infos).Contains(_5_key)) && ((_5_key) != (_4_queryId))) {
      _coll0.Add(new Dafny.Pair<BigInteger,TsLimitQueriesRuntime._IQueryInfo>(_5_key, Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((_3_state).dtor_infos,_5_key)));
    }
  }
  return Dafny.Map<BigInteger,TsLimitQueriesRuntime._IQueryInfo>.FromCollection(_coll0);
}))())(state, queryId), Dafny.Helpers.Id<Func<TsLimitQueriesRuntime._ILimitQueriesState, BigInteger, Dafny.IMap<BigInteger,BigInteger>>>((_6_state, _7_queryId) => ((System.Func<Dafny.IMap<BigInteger,BigInteger>>)(() => {
  var _coll1 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,BigInteger>>();
  foreach (BigInteger _compr_1 in ((_6_state).dtor_baseScores).Keys.Elements) {
    BigInteger _8_key = (BigInteger)_compr_1;
    if ((((_6_state).dtor_baseScores).Contains(_8_key)) && ((_8_key) != (_7_queryId))) {
      _coll1.Add(new Dafny.Pair<BigInteger,BigInteger>(_8_key, Dafny.Map<BigInteger, BigInteger>.Select((_6_state).dtor_baseScores,_8_key)));
    }
  }
  return Dafny.Map<BigInteger,BigInteger>.FromCollection(_coll1);
}))())(state, queryId), (state).dtor_pendingByQuery, (state).dtor_pendingByDoc);
        TsLimitQueriesRuntime._ILimitQueriesState _9_state2 = ((((_2_state1).dtor_pendingByQuery).Contains(queryId)) ? (TsLimitQueriesRuntime.__default.RemovePendingDocsForQuery(_2_state1, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_2_state1).dtor_pendingByQuery,queryId), queryId)) : (_2_state1));
        return TsLimitQueriesRuntime.StateChange.create(TsLimitQueriesRuntime.LimitQueriesState.create((_9_state2).dtor_docs, (_9_state2).dtor_queries, (_9_state2).dtor_nextId, (_9_state2).dtor_infos, (_9_state2).dtor_baseScores, Dafny.Helpers.Id<Func<TsLimitQueriesRuntime._ILimitQueriesState, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_10_state2, _11_queryId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
  var _coll2 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
  foreach (BigInteger _compr_2 in ((_10_state2).dtor_pendingByQuery).Keys.Elements) {
    BigInteger _12_key = (BigInteger)_compr_2;
    if ((((_10_state2).dtor_pendingByQuery).Contains(_12_key)) && ((_12_key) != (_11_queryId))) {
      _coll2.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_12_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_10_state2).dtor_pendingByQuery,_12_key)));
    }
  }
  return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll2);
}))())(_9_state2, queryId), (_9_state2).dtor_pendingByDoc), true);
      }
    }
    public static Dafny.ISequence<BigInteger> GetQueriesCovering(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger @value, DocsIndexModel._IMaybeDocId docId)
    {
      return TsQueriesRuntime.__default.CollectForValue((state).dtor_queries, @value, TsDocsRuntime.__default.RankDoc((state).dtor_docs, @value, docId));
    }
    public static Dafny.ISequence<BigInteger> GetDocsForQuery(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId)
    {
      if (!(((state).dtor_infos).Contains(queryId))) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else {
        TsLimitQueriesRuntime._IQueryInfo _0_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,queryId);
        return TsDocsRuntime.__default.CollectRangeDocs((state).dtor_docs, (_0_info).dtor_a, (_0_info).dtor_max, (_0_info).dtor_k);
      }
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState DecrementCurrentMatchesFor(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> affected)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((affected).Count)).Sign == 0) {
        return state;
      } else if (!(((state).dtor_infos).Contains((affected).Select(BigInteger.Zero)))) {
        TsLimitQueriesRuntime._ILimitQueriesState _in0 = state;
        Dafny.ISequence<BigInteger> _in1 = (affected).Drop(BigInteger.One);
        state = _in0;
        affected = _in1;
        goto TAIL_CALL_START;
      } else {
        TsLimitQueriesRuntime._IQueryInfo _0_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,(affected).Select(BigInteger.Zero));
        TsLimitQueriesRuntime._ILimitQueriesState _1_nextState = ((((_0_info).dtor_currentMatches).Sign == 0) ? (state) : (TsLimitQueriesRuntime.__default.SetCurrentMatches(state, (affected).Select(BigInteger.Zero), ((_0_info).dtor_currentMatches) - (BigInteger.One))));
        TsLimitQueriesRuntime._ILimitQueriesState _in2 = _1_nextState;
        Dafny.ISequence<BigInteger> _in3 = (affected).Drop(BigInteger.One);
        state = _in2;
        affected = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitQueriesRuntime._IRemoveDocumentResult RemoveDocument(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger score, BigInteger docId)
    {
      Dafny.ISequence<BigInteger> _0_affected = TsLimitQueriesRuntime.__default.GetQueriesCovering(state, score, DocsIndexModel.MaybeDocId.create_SomeDoc(docId));
      Dafny.ISequence<DocsIndexModel._IEntry> _1_nextDocs = TsDocsRuntime.__default.RemoveDoc((state).dtor_docs, score, docId);
      TsQueriesRuntime._IQueriesState _2_nextQueries = TsQueriesRuntime.__default.RangeAddKeysGreaterThan((state).dtor_queries, score, new BigInteger(-1));
      TsLimitQueriesRuntime._ILimitQueriesState _3_nextState = TsLimitQueriesRuntime.LimitQueriesState.create(_1_nextDocs, _2_nextQueries, (state).dtor_nextId, (state).dtor_infos, (state).dtor_baseScores, (state).dtor_pendingByQuery, (state).dtor_pendingByDoc);
      return TsLimitQueriesRuntime.RemoveDocumentResult.create(TsLimitQueriesRuntime.__default.DecrementCurrentMatchesFor(_3_nextState, _0_affected), _0_affected);
    }
    public static TsLimitQueriesRuntime._IAddDocumentResult ProcessAddedQueries(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> affected, BigInteger docId)
    {
      if ((new BigInteger((affected).Count)).Sign == 0) {
        return TsLimitQueriesRuntime.AddDocumentResult.create(state, Dafny.Sequence<BigInteger>.FromElements(), Dafny.Sequence<BigInteger>.FromElements());
      } else {
        BigInteger _0_queryId = (affected).Select(BigInteger.Zero);
        Dafny.ISequence<BigInteger> _1_rest = (affected).Drop(BigInteger.One);
        if (!(((state).dtor_infos).Contains(_0_queryId))) {
          TsLimitQueriesRuntime._IAddDocumentResult _2_next = TsLimitQueriesRuntime.__default.ProcessAddedQueries(state, _1_rest, docId);
          return TsLimitQueriesRuntime.AddDocumentResult.create((_2_next).dtor_state, Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(_0_queryId), (_2_next).dtor_matched), (_2_next).dtor_blocked);
        } else if ((((state).dtor_pendingByDoc).Contains(docId)) && (ThunderDbStack.__default.ContainsQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByDoc,docId), _0_queryId))) {
          TsLimitQueriesRuntime._IAddDocumentResult _3_next = TsLimitQueriesRuntime.__default.ProcessAddedQueries(TsLimitQueriesRuntime.__default.RemovePendingPair(state, _0_queryId, docId), _1_rest, docId);
          return TsLimitQueriesRuntime.AddDocumentResult.create((_3_next).dtor_state, Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(_0_queryId), (_3_next).dtor_matched), (_3_next).dtor_blocked);
        } else {
          TsLimitQueriesRuntime._IQueryInfo _4_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,_0_queryId);
          if (((_4_info).dtor_currentMatches) < ((_4_info).dtor_k)) {
            TsLimitQueriesRuntime._IAddDocumentResult _5_next = TsLimitQueriesRuntime.__default.ProcessAddedQueries(TsLimitQueriesRuntime.__default.SetCurrentMatches(state, _0_queryId, ((_4_info).dtor_currentMatches) + (BigInteger.One)), _1_rest, docId);
            return TsLimitQueriesRuntime.AddDocumentResult.create((_5_next).dtor_state, Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(_0_queryId), (_5_next).dtor_matched), (_5_next).dtor_blocked);
          } else {
            TsLimitQueriesRuntime._IAddDocumentResult _6_next = TsLimitQueriesRuntime.__default.ProcessAddedQueries(state, _1_rest, docId);
            return TsLimitQueriesRuntime.AddDocumentResult.create((_6_next).dtor_state, Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(_0_queryId), (_6_next).dtor_matched), Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(_0_queryId), (_6_next).dtor_blocked));
          }
        }
      }
    }
    public static TsLimitQueriesRuntime._IAddDocumentResult AddDocument(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger score, BigInteger docId)
    {
      Dafny.ISequence<BigInteger> _0_affected = TsLimitQueriesRuntime.__default.GetQueriesCovering(state, score, DocsIndexModel.MaybeDocId.create_SomeDoc(docId));
      Dafny.ISequence<DocsIndexModel._IEntry> _1_nextDocs = TsDocsRuntime.__default.AddDoc((state).dtor_docs, score, docId);
      TsQueriesRuntime._IQueriesState _2_nextQueries = TsQueriesRuntime.__default.RangeAddKeysGreaterThan((state).dtor_queries, score, BigInteger.One);
      return TsLimitQueriesRuntime.__default.ProcessAddedQueries(TsLimitQueriesRuntime.LimitQueriesState.create(_1_nextDocs, _2_nextQueries, (state).dtor_nextId, (state).dtor_infos, (state).dtor_baseScores, (state).dtor_pendingByQuery, (state).dtor_pendingByDoc), _0_affected, docId);
    }
    public static DocsIndexModel._IMaybeDocId DocForQueryAt(TsLimitQueriesRuntime._ILimitQueriesState state, TsLimitQueriesRuntime._IQueryInfo info, BigInteger offset)
    {
      BigInteger _0_startRank = TsDocsRuntime.__default.RankDoc((state).dtor_docs, (info).dtor_a, DocsIndexModel.MaybeDocId.create_NoDoc());
      DocsIndexModel._IAtRank _source0 = TsDocsRuntime.__default.GetAtRankDoc((state).dtor_docs, (_0_startRank) + (offset));
      {
        if (_source0.is_Missing) {
          return DocsIndexModel.MaybeDocId.create_NoDoc();
        }
      }
      {
        BigInteger _1_score = _source0.dtor_score;
        BigInteger _2_id = _source0.dtor_id;
        BigInteger _3_pos = _source0.dtor_position;
        if ((_1_score) <= ((info).dtor_max)) {
          return DocsIndexModel.MaybeDocId.create_SomeDoc(_2_id);
        } else {
          return DocsIndexModel.MaybeDocId.create_NoDoc();
        }
      }
    }
    public static DocsIndexModel._IMaybeDocId PickOverflowDoc(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId)
    {
      if (!(((state).dtor_infos).Contains(queryId))) {
        return DocsIndexModel.MaybeDocId.create_NoDoc();
      } else {
        TsLimitQueriesRuntime._IQueryInfo _0_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,queryId);
        if (((_0_info).dtor_currentMatches) < ((_0_info).dtor_k)) {
          return DocsIndexModel.MaybeDocId.create_NoDoc();
        } else {
          return TsLimitQueriesRuntime.__default.DocForQueryAt(state, _0_info, (_0_info).dtor_k);
        }
      }
    }
    public static TsLimitQueriesRuntime._IGapFillResult FillGapFrom(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId, BigInteger offset)
    {
    TAIL_CALL_START: ;
      DocsIndexModel._IMaybeDocId _0_candidate = TsLimitQueriesRuntime.__default.DocForQueryAt(state, Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,queryId), offset);
      DocsIndexModel._IMaybeDocId _source0 = _0_candidate;
      {
        if (_source0.is_NoDoc) {
          return TsLimitQueriesRuntime.GapFillResult.create(state, DocsIndexModel.MaybeDocId.create_NoDoc());
        }
      }
      {
        BigInteger _1_docId = _source0.dtor_doc;
        if ((((state).dtor_pendingByQuery).Contains(queryId)) && (ThunderDbStack.__default.ContainsId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByQuery,queryId), _1_docId))) {
          TsLimitQueriesRuntime._ILimitQueriesState _in0 = state;
          BigInteger _in1 = queryId;
          BigInteger _in2 = (offset) + (BigInteger.One);
          state = _in0;
          queryId = _in1;
          offset = _in2;
          goto TAIL_CALL_START;
        } else {
          TsLimitQueriesRuntime._IQueryInfo _2_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,queryId);
          TsLimitQueriesRuntime._ILimitQueriesState _3_state1 = TsLimitQueriesRuntime.__default.SetCurrentMatches(state, queryId, ((_2_info).dtor_currentMatches) + (BigInteger.One));
          return TsLimitQueriesRuntime.GapFillResult.create(TsLimitQueriesRuntime.__default.AddPendingPair(_3_state1, queryId, _1_docId), DocsIndexModel.MaybeDocId.create_SomeDoc(_1_docId));
        }
      }
    }
    public static TsLimitQueriesRuntime._IGapFillResult FillGap(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId)
    {
      if (!(((state).dtor_infos).Contains(queryId))) {
        return TsLimitQueriesRuntime.GapFillResult.create(state, DocsIndexModel.MaybeDocId.create_NoDoc());
      } else {
        TsLimitQueriesRuntime._IQueryInfo _0_info = Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((state).dtor_infos,queryId);
        if (((_0_info).dtor_currentMatches) >= ((_0_info).dtor_k)) {
          return TsLimitQueriesRuntime.GapFillResult.create(state, DocsIndexModel.MaybeDocId.create_NoDoc());
        } else {
          return TsLimitQueriesRuntime.__default.FillGapFrom(state, queryId, (_0_info).dtor_currentMatches);
        }
      }
    }
    public static TsLimitQueriesRuntime._IStateChange CancelPendingForQuery(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger docId, BigInteger queryId)
    {
      if ((!(((state).dtor_pendingByQuery).Contains(queryId))) || (!(ThunderDbStack.__default.ContainsId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByQuery,queryId), docId)))) {
        return TsLimitQueriesRuntime.StateChange.create(state, false);
      } else {
        TsLimitQueriesRuntime._ILimitQueriesState _0_state1 = TsLimitQueriesRuntime.__default.RemovePendingPair(state, queryId, docId);
        TsLimitQueriesRuntime._ILimitQueriesState _1_state2 = (((((_0_state1).dtor_infos).Contains(queryId)) && (((Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((_0_state1).dtor_infos,queryId)).dtor_currentMatches).Sign == 1)) ? (TsLimitQueriesRuntime.__default.SetCurrentMatches(_0_state1, queryId, ((Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select((_0_state1).dtor_infos,queryId)).dtor_currentMatches) - (BigInteger.One))) : (_0_state1));
        return TsLimitQueriesRuntime.StateChange.create(_1_state2, true);
      }
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState ResolvePendingDocQueries(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> queryIds, BigInteger docId)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((queryIds).Count)).Sign == 0) {
        return state;
      } else {
        TsLimitQueriesRuntime._ILimitQueriesState _in0 = TsLimitQueriesRuntime.__default.RemovePendingPair(state, (queryIds).Select(BigInteger.Zero), docId);
        Dafny.ISequence<BigInteger> _in1 = (queryIds).Drop(BigInteger.One);
        BigInteger _in2 = docId;
        state = _in0;
        queryIds = _in1;
        docId = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState ResolvePendingForDoc(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger docId)
    {
      if (!(((state).dtor_pendingByDoc).Contains(docId))) {
        return state;
      } else {
        return TsLimitQueriesRuntime.__default.ResolvePendingDocQueries(state, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingByDoc,docId), docId);
      }
    }
  }

  public interface _IQueryInfo {
    bool is_QueryInfo { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_a { get; }
    BigInteger dtor_k { get; }
    BigInteger dtor_max { get; }
    BigInteger dtor_currentMatches { get; }
    _IQueryInfo DowncastClone();
  }
  public class QueryInfo : _IQueryInfo {
    public readonly BigInteger _id;
    public readonly BigInteger _a;
    public readonly BigInteger _k;
    public readonly BigInteger _max;
    public readonly BigInteger _currentMatches;
    public QueryInfo(BigInteger id, BigInteger a, BigInteger k, BigInteger max, BigInteger currentMatches) {
      this._id = id;
      this._a = a;
      this._k = k;
      this._max = max;
      this._currentMatches = currentMatches;
    }
    public _IQueryInfo DowncastClone() {
      if (this is _IQueryInfo dt) { return dt; }
      return new QueryInfo(_id, _a, _k, _max, _currentMatches);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitQueriesRuntime.QueryInfo;
      return oth != null && this._id == oth._id && this._a == oth._a && this._k == oth._k && this._max == oth._max && this._currentMatches == oth._currentMatches;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._k));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._max));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._currentMatches));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitQueriesRuntime.QueryInfo.QueryInfo";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._a);
      s += ", ";
      s += Dafny.Helpers.ToString(this._k);
      s += ", ";
      s += Dafny.Helpers.ToString(this._max);
      s += ", ";
      s += Dafny.Helpers.ToString(this._currentMatches);
      s += ")";
      return s;
    }
    private static readonly TsLimitQueriesRuntime._IQueryInfo theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static TsLimitQueriesRuntime._IQueryInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitQueriesRuntime._IQueryInfo> _TYPE = new Dafny.TypeDescriptor<TsLimitQueriesRuntime._IQueryInfo>(TsLimitQueriesRuntime.QueryInfo.Default());
    public static Dafny.TypeDescriptor<TsLimitQueriesRuntime._IQueryInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryInfo create(BigInteger id, BigInteger a, BigInteger k, BigInteger max, BigInteger currentMatches) {
      return new QueryInfo(id, a, k, max, currentMatches);
    }
    public static _IQueryInfo create_QueryInfo(BigInteger id, BigInteger a, BigInteger k, BigInteger max, BigInteger currentMatches) {
      return create(id, a, k, max, currentMatches);
    }
    public bool is_QueryInfo { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_a {
      get {
        return this._a;
      }
    }
    public BigInteger dtor_k {
      get {
        return this._k;
      }
    }
    public BigInteger dtor_max {
      get {
        return this._max;
      }
    }
    public BigInteger dtor_currentMatches {
      get {
        return this._currentMatches;
      }
    }
  }

  public interface _ILimitQueriesState {
    bool is_LimitQueriesState { get; }
    Dafny.ISequence<DocsIndexModel._IEntry> dtor_docs { get; }
    TsQueriesRuntime._IQueriesState dtor_queries { get; }
    BigInteger dtor_nextId { get; }
    Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo> dtor_infos { get; }
    Dafny.IMap<BigInteger,BigInteger> dtor_baseScores { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_pendingByQuery { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_pendingByDoc { get; }
    _ILimitQueriesState DowncastClone();
  }
  public class LimitQueriesState : _ILimitQueriesState {
    public readonly Dafny.ISequence<DocsIndexModel._IEntry> _docs;
    public readonly TsQueriesRuntime._IQueriesState _queries;
    public readonly BigInteger _nextId;
    public readonly Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo> _infos;
    public readonly Dafny.IMap<BigInteger,BigInteger> _baseScores;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _pendingByQuery;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _pendingByDoc;
    public LimitQueriesState(Dafny.ISequence<DocsIndexModel._IEntry> docs, TsQueriesRuntime._IQueriesState queries, BigInteger nextId, Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo> infos, Dafny.IMap<BigInteger,BigInteger> baseScores, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByQuery, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByDoc) {
      this._docs = docs;
      this._queries = queries;
      this._nextId = nextId;
      this._infos = infos;
      this._baseScores = baseScores;
      this._pendingByQuery = pendingByQuery;
      this._pendingByDoc = pendingByDoc;
    }
    public _ILimitQueriesState DowncastClone() {
      if (this is _ILimitQueriesState dt) { return dt; }
      return new LimitQueriesState(_docs, _queries, _nextId, _infos, _baseScores, _pendingByQuery, _pendingByDoc);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitQueriesRuntime.LimitQueriesState;
      return oth != null && object.Equals(this._docs, oth._docs) && object.Equals(this._queries, oth._queries) && this._nextId == oth._nextId && object.Equals(this._infos, oth._infos) && object.Equals(this._baseScores, oth._baseScores) && object.Equals(this._pendingByQuery, oth._pendingByQuery) && object.Equals(this._pendingByDoc, oth._pendingByDoc);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queries));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nextId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._infos));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseScores));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pendingByQuery));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pendingByDoc));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitQueriesRuntime.LimitQueriesState.LimitQueriesState";
      s += "(";
      s += Dafny.Helpers.ToString(this._docs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queries);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nextId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._infos);
      s += ", ";
      s += Dafny.Helpers.ToString(this._baseScores);
      s += ", ";
      s += Dafny.Helpers.ToString(this._pendingByQuery);
      s += ", ";
      s += Dafny.Helpers.ToString(this._pendingByDoc);
      s += ")";
      return s;
    }
    private static readonly TsLimitQueriesRuntime._ILimitQueriesState theDefault = create(Dafny.Sequence<DocsIndexModel._IEntry>.Empty, TsQueriesRuntime.QueriesState.Default(), BigInteger.Zero, Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Empty, Dafny.Map<BigInteger, BigInteger>.Empty, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty);
    public static TsLimitQueriesRuntime._ILimitQueriesState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitQueriesRuntime._ILimitQueriesState> _TYPE = new Dafny.TypeDescriptor<TsLimitQueriesRuntime._ILimitQueriesState>(TsLimitQueriesRuntime.LimitQueriesState.Default());
    public static Dafny.TypeDescriptor<TsLimitQueriesRuntime._ILimitQueriesState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ILimitQueriesState create(Dafny.ISequence<DocsIndexModel._IEntry> docs, TsQueriesRuntime._IQueriesState queries, BigInteger nextId, Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo> infos, Dafny.IMap<BigInteger,BigInteger> baseScores, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByQuery, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByDoc) {
      return new LimitQueriesState(docs, queries, nextId, infos, baseScores, pendingByQuery, pendingByDoc);
    }
    public static _ILimitQueriesState create_LimitQueriesState(Dafny.ISequence<DocsIndexModel._IEntry> docs, TsQueriesRuntime._IQueriesState queries, BigInteger nextId, Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo> infos, Dafny.IMap<BigInteger,BigInteger> baseScores, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByQuery, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByDoc) {
      return create(docs, queries, nextId, infos, baseScores, pendingByQuery, pendingByDoc);
    }
    public bool is_LimitQueriesState { get { return true; } }
    public Dafny.ISequence<DocsIndexModel._IEntry> dtor_docs {
      get {
        return this._docs;
      }
    }
    public TsQueriesRuntime._IQueriesState dtor_queries {
      get {
        return this._queries;
      }
    }
    public BigInteger dtor_nextId {
      get {
        return this._nextId;
      }
    }
    public Dafny.IMap<BigInteger,TsLimitQueriesRuntime._IQueryInfo> dtor_infos {
      get {
        return this._infos;
      }
    }
    public Dafny.IMap<BigInteger,BigInteger> dtor_baseScores {
      get {
        return this._baseScores;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_pendingByQuery {
      get {
        return this._pendingByQuery;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_pendingByDoc {
      get {
        return this._pendingByDoc;
      }
    }
  }

  public interface _IStateChange {
    bool is_StateChange { get; }
    TsLimitQueriesRuntime._ILimitQueriesState dtor_state { get; }
    bool dtor_changed { get; }
    _IStateChange DowncastClone();
  }
  public class StateChange : _IStateChange {
    public readonly TsLimitQueriesRuntime._ILimitQueriesState _state;
    public readonly bool _changed;
    public StateChange(TsLimitQueriesRuntime._ILimitQueriesState state, bool changed) {
      this._state = state;
      this._changed = changed;
    }
    public _IStateChange DowncastClone() {
      if (this is _IStateChange dt) { return dt; }
      return new StateChange(_state, _changed);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitQueriesRuntime.StateChange;
      return oth != null && object.Equals(this._state, oth._state) && this._changed == oth._changed;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._changed));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitQueriesRuntime.StateChange.StateChange";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._changed);
      s += ")";
      return s;
    }
    private static readonly TsLimitQueriesRuntime._IStateChange theDefault = create(TsLimitQueriesRuntime.LimitQueriesState.Default(), false);
    public static TsLimitQueriesRuntime._IStateChange Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitQueriesRuntime._IStateChange> _TYPE = new Dafny.TypeDescriptor<TsLimitQueriesRuntime._IStateChange>(TsLimitQueriesRuntime.StateChange.Default());
    public static Dafny.TypeDescriptor<TsLimitQueriesRuntime._IStateChange> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStateChange create(TsLimitQueriesRuntime._ILimitQueriesState state, bool changed) {
      return new StateChange(state, changed);
    }
    public static _IStateChange create_StateChange(TsLimitQueriesRuntime._ILimitQueriesState state, bool changed) {
      return create(state, changed);
    }
    public bool is_StateChange { get { return true; } }
    public TsLimitQueriesRuntime._ILimitQueriesState dtor_state {
      get {
        return this._state;
      }
    }
    public bool dtor_changed {
      get {
        return this._changed;
      }
    }
  }

  public interface _IQueryAddResult {
    bool is_QueryAddResult { get; }
    TsLimitQueriesRuntime._ILimitQueriesState dtor_state { get; }
    BigInteger dtor_queryId { get; }
    _IQueryAddResult DowncastClone();
  }
  public class QueryAddResult : _IQueryAddResult {
    public readonly TsLimitQueriesRuntime._ILimitQueriesState _state;
    public readonly BigInteger _queryId;
    public QueryAddResult(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId) {
      this._state = state;
      this._queryId = queryId;
    }
    public _IQueryAddResult DowncastClone() {
      if (this is _IQueryAddResult dt) { return dt; }
      return new QueryAddResult(_state, _queryId);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitQueriesRuntime.QueryAddResult;
      return oth != null && object.Equals(this._state, oth._state) && this._queryId == oth._queryId;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queryId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitQueriesRuntime.QueryAddResult.QueryAddResult";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queryId);
      s += ")";
      return s;
    }
    private static readonly TsLimitQueriesRuntime._IQueryAddResult theDefault = create(TsLimitQueriesRuntime.LimitQueriesState.Default(), BigInteger.Zero);
    public static TsLimitQueriesRuntime._IQueryAddResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitQueriesRuntime._IQueryAddResult> _TYPE = new Dafny.TypeDescriptor<TsLimitQueriesRuntime._IQueryAddResult>(TsLimitQueriesRuntime.QueryAddResult.Default());
    public static Dafny.TypeDescriptor<TsLimitQueriesRuntime._IQueryAddResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryAddResult create(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId) {
      return new QueryAddResult(state, queryId);
    }
    public static _IQueryAddResult create_QueryAddResult(TsLimitQueriesRuntime._ILimitQueriesState state, BigInteger queryId) {
      return create(state, queryId);
    }
    public bool is_QueryAddResult { get { return true; } }
    public TsLimitQueriesRuntime._ILimitQueriesState dtor_state {
      get {
        return this._state;
      }
    }
    public BigInteger dtor_queryId {
      get {
        return this._queryId;
      }
    }
  }

  public interface _IAddDocumentResult {
    bool is_AddDocumentResult { get; }
    TsLimitQueriesRuntime._ILimitQueriesState dtor_state { get; }
    Dafny.ISequence<BigInteger> dtor_matched { get; }
    Dafny.ISequence<BigInteger> dtor_blocked { get; }
    _IAddDocumentResult DowncastClone();
  }
  public class AddDocumentResult : _IAddDocumentResult {
    public readonly TsLimitQueriesRuntime._ILimitQueriesState _state;
    public readonly Dafny.ISequence<BigInteger> _matched;
    public readonly Dafny.ISequence<BigInteger> _blocked;
    public AddDocumentResult(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> matched, Dafny.ISequence<BigInteger> blocked) {
      this._state = state;
      this._matched = matched;
      this._blocked = blocked;
    }
    public _IAddDocumentResult DowncastClone() {
      if (this is _IAddDocumentResult dt) { return dt; }
      return new AddDocumentResult(_state, _matched, _blocked);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitQueriesRuntime.AddDocumentResult;
      return oth != null && object.Equals(this._state, oth._state) && object.Equals(this._matched, oth._matched) && object.Equals(this._blocked, oth._blocked);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matched));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._blocked));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitQueriesRuntime.AddDocumentResult.AddDocumentResult";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._matched);
      s += ", ";
      s += Dafny.Helpers.ToString(this._blocked);
      s += ")";
      return s;
    }
    private static readonly TsLimitQueriesRuntime._IAddDocumentResult theDefault = create(TsLimitQueriesRuntime.LimitQueriesState.Default(), Dafny.Sequence<BigInteger>.Empty, Dafny.Sequence<BigInteger>.Empty);
    public static TsLimitQueriesRuntime._IAddDocumentResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitQueriesRuntime._IAddDocumentResult> _TYPE = new Dafny.TypeDescriptor<TsLimitQueriesRuntime._IAddDocumentResult>(TsLimitQueriesRuntime.AddDocumentResult.Default());
    public static Dafny.TypeDescriptor<TsLimitQueriesRuntime._IAddDocumentResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAddDocumentResult create(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> matched, Dafny.ISequence<BigInteger> blocked) {
      return new AddDocumentResult(state, matched, blocked);
    }
    public static _IAddDocumentResult create_AddDocumentResult(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> matched, Dafny.ISequence<BigInteger> blocked) {
      return create(state, matched, blocked);
    }
    public bool is_AddDocumentResult { get { return true; } }
    public TsLimitQueriesRuntime._ILimitQueriesState dtor_state {
      get {
        return this._state;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_matched {
      get {
        return this._matched;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_blocked {
      get {
        return this._blocked;
      }
    }
  }

  public interface _IRemoveDocumentResult {
    bool is_RemoveDocumentResult { get; }
    TsLimitQueriesRuntime._ILimitQueriesState dtor_state { get; }
    Dafny.ISequence<BigInteger> dtor_removed { get; }
    _IRemoveDocumentResult DowncastClone();
  }
  public class RemoveDocumentResult : _IRemoveDocumentResult {
    public readonly TsLimitQueriesRuntime._ILimitQueriesState _state;
    public readonly Dafny.ISequence<BigInteger> _removed;
    public RemoveDocumentResult(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> removed) {
      this._state = state;
      this._removed = removed;
    }
    public _IRemoveDocumentResult DowncastClone() {
      if (this is _IRemoveDocumentResult dt) { return dt; }
      return new RemoveDocumentResult(_state, _removed);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitQueriesRuntime.RemoveDocumentResult;
      return oth != null && object.Equals(this._state, oth._state) && object.Equals(this._removed, oth._removed);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._removed));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitQueriesRuntime.RemoveDocumentResult.RemoveDocumentResult";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._removed);
      s += ")";
      return s;
    }
    private static readonly TsLimitQueriesRuntime._IRemoveDocumentResult theDefault = create(TsLimitQueriesRuntime.LimitQueriesState.Default(), Dafny.Sequence<BigInteger>.Empty);
    public static TsLimitQueriesRuntime._IRemoveDocumentResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitQueriesRuntime._IRemoveDocumentResult> _TYPE = new Dafny.TypeDescriptor<TsLimitQueriesRuntime._IRemoveDocumentResult>(TsLimitQueriesRuntime.RemoveDocumentResult.Default());
    public static Dafny.TypeDescriptor<TsLimitQueriesRuntime._IRemoveDocumentResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRemoveDocumentResult create(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> removed) {
      return new RemoveDocumentResult(state, removed);
    }
    public static _IRemoveDocumentResult create_RemoveDocumentResult(TsLimitQueriesRuntime._ILimitQueriesState state, Dafny.ISequence<BigInteger> removed) {
      return create(state, removed);
    }
    public bool is_RemoveDocumentResult { get { return true; } }
    public TsLimitQueriesRuntime._ILimitQueriesState dtor_state {
      get {
        return this._state;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_removed {
      get {
        return this._removed;
      }
    }
  }

  public interface _IGapFillResult {
    bool is_GapFillResult { get; }
    TsLimitQueriesRuntime._ILimitQueriesState dtor_state { get; }
    DocsIndexModel._IMaybeDocId dtor_doc { get; }
    _IGapFillResult DowncastClone();
  }
  public class GapFillResult : _IGapFillResult {
    public readonly TsLimitQueriesRuntime._ILimitQueriesState _state;
    public readonly DocsIndexModel._IMaybeDocId _doc;
    public GapFillResult(TsLimitQueriesRuntime._ILimitQueriesState state, DocsIndexModel._IMaybeDocId doc) {
      this._state = state;
      this._doc = doc;
    }
    public _IGapFillResult DowncastClone() {
      if (this is _IGapFillResult dt) { return dt; }
      return new GapFillResult(_state, _doc);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitQueriesRuntime.GapFillResult;
      return oth != null && object.Equals(this._state, oth._state) && object.Equals(this._doc, oth._doc);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._doc));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitQueriesRuntime.GapFillResult.GapFillResult";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._doc);
      s += ")";
      return s;
    }
    private static readonly TsLimitQueriesRuntime._IGapFillResult theDefault = create(TsLimitQueriesRuntime.LimitQueriesState.Default(), DocsIndexModel.MaybeDocId.Default());
    public static TsLimitQueriesRuntime._IGapFillResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitQueriesRuntime._IGapFillResult> _TYPE = new Dafny.TypeDescriptor<TsLimitQueriesRuntime._IGapFillResult>(TsLimitQueriesRuntime.GapFillResult.Default());
    public static Dafny.TypeDescriptor<TsLimitQueriesRuntime._IGapFillResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGapFillResult create(TsLimitQueriesRuntime._ILimitQueriesState state, DocsIndexModel._IMaybeDocId doc) {
      return new GapFillResult(state, doc);
    }
    public static _IGapFillResult create_GapFillResult(TsLimitQueriesRuntime._ILimitQueriesState state, DocsIndexModel._IMaybeDocId doc) {
      return create(state, doc);
    }
    public bool is_GapFillResult { get { return true; } }
    public TsLimitQueriesRuntime._ILimitQueriesState dtor_state {
      get {
        return this._state;
      }
    }
    public DocsIndexModel._IMaybeDocId dtor_doc {
      get {
        return this._doc;
      }
    }
  }
} // end of namespace TsLimitQueriesRuntime
namespace TsRetrievalRuntime {

  public partial class __default {
    public static TsRetrievalRuntime._IRetrievalWorkerState EmptyWorkerState() {
      return TsRetrievalRuntime.RetrievalWorkerState.create(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements(), Dafny.Sequence<BigInteger>.FromElements(), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements(), Dafny.Sequence<BigInteger>.FromElements(), false);
    }
    public static Dafny.ISequence<BigInteger> RemoveQueryId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (((ids).Select(BigInteger.Zero)) == (id)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, (ids).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool UniqueQueryIds(Dafny.ISequence<BigInteger> ids) {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return true;
      } else {
        return (!(ThunderDbStack.__default.ContainsQueryId((ids).Drop(BigInteger.One), (ids).Select(BigInteger.Zero)))) && (TsRetrievalRuntime.__default.UniqueQueryIds((ids).Drop(BigInteger.One)));
      }
    }
    public static bool RegistryConsistent(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> batch, Dafny.ISequence<BigInteger> order)
    {
      return ((ThunderDbStack.__default.UniqueDocIds(order)) && (Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, Dafny.ISequence<BigInteger>, bool>>((_0_batch, _1_order) => Dafny.Helpers.Quantifier<BigInteger>((_0_batch).Keys.Elements, true, (((_forall_var_0) => {
        BigInteger _2_docId = (BigInteger)_forall_var_0;
        return !((_0_batch).Contains(_2_docId)) || (ThunderDbStack.__default.ContainsId(_1_order, _2_docId));
      }))))(batch, order))) && (Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, bool>>((_3_batch) => Dafny.Helpers.Quantifier<BigInteger>((_3_batch).Keys.Elements, true, (((_forall_var_1) => {
        BigInteger _4_docId = (BigInteger)_forall_var_1;
        return !((_3_batch).Contains(_4_docId)) || (TsRetrievalRuntime.__default.UniqueQueryIds(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_3_batch,_4_docId)));
      }))))(batch));
    }
    public static bool WorkerConsistent(TsRetrievalRuntime._IRetrievalWorkerState state) {
      return (TsRetrievalRuntime.__default.RegistryConsistent((state).dtor_pendingBatch, (state).dtor_pendingOrder)) && (TsRetrievalRuntime.__default.RegistryConsistent((state).dtor_processingBatch, (state).dtor_processingOrder));
    }
    public static bool CanRegister(TsRetrievalRuntime._IRetrievalWorkerState state, BigInteger docId, BigInteger queryId)
    {
      return !((((state).dtor_processingBatch).Contains(docId)) && (ThunderDbStack.__default.ContainsQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_processingBatch,docId), queryId)));
    }
    public static TsRetrievalRuntime._IRetrievalWorkerState Register(TsRetrievalRuntime._IRetrievalWorkerState state, BigInteger docId, BigInteger queryId)
    {
      Dafny.ISequence<BigInteger> _0_nextQueries = ((((state).dtor_pendingBatch).Contains(docId)) ? (ThunderDbStack.__default.AppendQueryIdUnique(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingBatch,docId), queryId)) : (Dafny.Sequence<BigInteger>.FromElements(queryId)));
      Dafny.ISequence<BigInteger> _1_nextOrder = ((((state).dtor_pendingBatch).Contains(docId)) ? ((state).dtor_pendingOrder) : (ThunderDbStack.__default.AppendDocIdIfMissing((state).dtor_pendingOrder, docId)));
      return TsRetrievalRuntime.RetrievalWorkerState.create(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update((state).dtor_pendingBatch, docId, _0_nextQueries), _1_nextOrder, (state).dtor_processingBatch, (state).dtor_processingOrder, (state).dtor_stopped);
    }
    public static TsRetrievalRuntime._IStateChange Cancel(TsRetrievalRuntime._IRetrievalWorkerState state, BigInteger docId, BigInteger queryId)
    {
      if (((state).dtor_pendingBatch).Contains(docId)) {
        bool _0_removed = ThunderDbStack.__default.ContainsQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingBatch,docId), queryId);
        Dafny.ISequence<BigInteger> _1_nextQueries = TsRetrievalRuntime.__default.RemoveQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_pendingBatch,docId), queryId);
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _2_nextBatch = (((_0_removed) && ((new BigInteger((_1_nextQueries).Count)).Sign == 0)) ? (Dafny.Helpers.Id<Func<TsRetrievalRuntime._IRetrievalWorkerState, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_3_state, _4_docId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
          var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
          foreach (BigInteger _compr_0 in ((_3_state).dtor_pendingBatch).Keys.Elements) {
            BigInteger _5_key = (BigInteger)_compr_0;
            if ((((_3_state).dtor_pendingBatch).Contains(_5_key)) && ((_5_key) != (_4_docId))) {
              _coll0.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_5_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_3_state).dtor_pendingBatch,_5_key)));
            }
          }
          return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll0);
        }))())(state, docId)) : (((_0_removed) ? (Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update((state).dtor_pendingBatch, docId, _1_nextQueries)) : ((state).dtor_pendingBatch))));
        Dafny.ISequence<BigInteger> _6_nextOrder = (((_0_removed) && (!((_2_nextBatch).Contains(docId)))) ? (ThunderDbStack.__default.RemoveDocId((state).dtor_pendingOrder, docId)) : ((state).dtor_pendingOrder));
        return TsRetrievalRuntime.StateChange.create(TsRetrievalRuntime.RetrievalWorkerState.create(_2_nextBatch, _6_nextOrder, (state).dtor_processingBatch, (state).dtor_processingOrder, (state).dtor_stopped), _0_removed);
      } else if (((state).dtor_processingBatch).Contains(docId)) {
        bool _7_removed = ThunderDbStack.__default.ContainsQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_processingBatch,docId), queryId);
        Dafny.ISequence<BigInteger> _8_nextQueries = TsRetrievalRuntime.__default.RemoveQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((state).dtor_processingBatch,docId), queryId);
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _9_nextBatch = (((_7_removed) && ((new BigInteger((_8_nextQueries).Count)).Sign == 0)) ? (Dafny.Helpers.Id<Func<TsRetrievalRuntime._IRetrievalWorkerState, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_10_state, _11_docId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
          var _coll1 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
          foreach (BigInteger _compr_1 in ((_10_state).dtor_processingBatch).Keys.Elements) {
            BigInteger _12_key = (BigInteger)_compr_1;
            if ((((_10_state).dtor_processingBatch).Contains(_12_key)) && ((_12_key) != (_11_docId))) {
              _coll1.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_12_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_10_state).dtor_processingBatch,_12_key)));
            }
          }
          return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll1);
        }))())(state, docId)) : (((_7_removed) ? (Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update((state).dtor_processingBatch, docId, _8_nextQueries)) : ((state).dtor_processingBatch))));
        Dafny.ISequence<BigInteger> _13_nextOrder = (((_7_removed) && (!((_9_nextBatch).Contains(docId)))) ? (ThunderDbStack.__default.RemoveDocId((state).dtor_processingOrder, docId)) : ((state).dtor_processingOrder));
        return TsRetrievalRuntime.StateChange.create(TsRetrievalRuntime.RetrievalWorkerState.create((state).dtor_pendingBatch, (state).dtor_pendingOrder, _9_nextBatch, _13_nextOrder, (state).dtor_stopped), _7_removed);
      } else {
        return TsRetrievalRuntime.StateChange.create(state, false);
      }
    }
    public static TsRetrievalRuntime._IStateChange ResolveDoc(TsRetrievalRuntime._IRetrievalWorkerState state, BigInteger docId)
    {
      bool _0_removedPending = ((state).dtor_pendingBatch).Contains(docId);
      bool _1_removedProcessing = ((state).dtor_processingBatch).Contains(docId);
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _2_nextPending = Dafny.Helpers.Id<Func<TsRetrievalRuntime._IRetrievalWorkerState, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_3_state, _4_docId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
        foreach (BigInteger _compr_0 in ((_3_state).dtor_pendingBatch).Keys.Elements) {
          BigInteger _5_key = (BigInteger)_compr_0;
          if ((((_3_state).dtor_pendingBatch).Contains(_5_key)) && ((_5_key) != (_4_docId))) {
            _coll0.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_5_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_3_state).dtor_pendingBatch,_5_key)));
          }
        }
        return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll0);
      }))())(state, docId);
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _6_nextProcessing = Dafny.Helpers.Id<Func<TsRetrievalRuntime._IRetrievalWorkerState, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_7_state, _8_docId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
        var _coll1 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
        foreach (BigInteger _compr_1 in ((_7_state).dtor_processingBatch).Keys.Elements) {
          BigInteger _9_key = (BigInteger)_compr_1;
          if ((((_7_state).dtor_processingBatch).Contains(_9_key)) && ((_9_key) != (_8_docId))) {
            _coll1.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_9_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select((_7_state).dtor_processingBatch,_9_key)));
          }
        }
        return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll1);
      }))())(state, docId);
      return TsRetrievalRuntime.StateChange.create(TsRetrievalRuntime.RetrievalWorkerState.create(_2_nextPending, ThunderDbStack.__default.RemoveDocId((state).dtor_pendingOrder, docId), _6_nextProcessing, ThunderDbStack.__default.RemoveDocId((state).dtor_processingOrder, docId), (state).dtor_stopped), (_0_removedPending) || (_1_removedProcessing));
    }
    public static TsRetrievalRuntime._IRetrievalWorkerState BeginCycle(TsRetrievalRuntime._IRetrievalWorkerState state) {
      return TsRetrievalRuntime.RetrievalWorkerState.create(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements(), Dafny.Sequence<BigInteger>.FromElements(), (state).dtor_pendingBatch, (state).dtor_pendingOrder, (state).dtor_stopped);
    }
    public static TsRetrievalRuntime._IRetrievalWorkerState FinishCycle(TsRetrievalRuntime._IRetrievalWorkerState state) {
      return TsRetrievalRuntime.RetrievalWorkerState.create((state).dtor_pendingBatch, (state).dtor_pendingOrder, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements(), Dafny.Sequence<BigInteger>.FromElements(), (state).dtor_stopped);
    }
    public static TsRetrievalRuntime._IRetrievalWorkerState Stop(TsRetrievalRuntime._IRetrievalWorkerState state) {
      return TsRetrievalRuntime.RetrievalWorkerState.create((state).dtor_pendingBatch, (state).dtor_pendingOrder, (state).dtor_processingBatch, (state).dtor_processingOrder, true);
    }
    public static bool HasPendingWork(TsRetrievalRuntime._IRetrievalWorkerState state) {
      return (new BigInteger(((state).dtor_pendingOrder).Count)).Sign == 1;
    }
    public static bool ShouldExit(TsRetrievalRuntime._IRetrievalWorkerState state) {
      return ((state).dtor_stopped) && (!(TsRetrievalRuntime.__default.HasPendingWork(state)));
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildPayload(TsRetrievalRuntime._IRetrievalWorkerState state, Dafny.IMap<BigInteger,BigInteger> store)
    {
      return TsRetrievalRuntime.__default.BuildPayloadFrom((state).dtor_processingOrder, (state).dtor_processingBatch, store);
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildPayloadFrom(Dafny.ISequence<BigInteger> order, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> batch, Dafny.IMap<BigInteger,BigInteger> store)
    {
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((order).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements());
      } else if (!((batch).Contains((order).Select(BigInteger.Zero)))) {
        Dafny.ISequence<BigInteger> _in0 = (order).Drop(BigInteger.One);
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _in1 = batch;
        Dafny.IMap<BigInteger,BigInteger> _in2 = store;
        order = _in0;
        batch = _in1;
        store = _in2;
        goto TAIL_CALL_START;
      } else {
        ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(store, (order).Select(BigInteger.Zero));
        {
          if (_source0.is_NoState) {
            Dafny.ISequence<BigInteger> _in3 = (order).Drop(BigInteger.One);
            Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _in4 = batch;
            Dafny.IMap<BigInteger,BigInteger> _in5 = store;
            order = _in3;
            batch = _in4;
            store = _in5;
            goto TAIL_CALL_START;
          }
        }
        {
          BigInteger _1_state = _source0.dtor_state;
          return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create((order).Select(BigInteger.Zero), _1_state, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(batch,(order).Select(BigInteger.Zero)))), TsRetrievalRuntime.__default.BuildPayloadFrom((order).Drop(BigInteger.One), batch, store));
        }
      }
    }
  }

  public interface _IRetrievalWorkerState {
    bool is_RetrievalWorkerState { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_pendingBatch { get; }
    Dafny.ISequence<BigInteger> dtor_pendingOrder { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_processingBatch { get; }
    Dafny.ISequence<BigInteger> dtor_processingOrder { get; }
    bool dtor_stopped { get; }
    _IRetrievalWorkerState DowncastClone();
  }
  public class RetrievalWorkerState : _IRetrievalWorkerState {
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _pendingBatch;
    public readonly Dafny.ISequence<BigInteger> _pendingOrder;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _processingBatch;
    public readonly Dafny.ISequence<BigInteger> _processingOrder;
    public readonly bool _stopped;
    public RetrievalWorkerState(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingBatch, Dafny.ISequence<BigInteger> pendingOrder, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> processingBatch, Dafny.ISequence<BigInteger> processingOrder, bool stopped) {
      this._pendingBatch = pendingBatch;
      this._pendingOrder = pendingOrder;
      this._processingBatch = processingBatch;
      this._processingOrder = processingOrder;
      this._stopped = stopped;
    }
    public _IRetrievalWorkerState DowncastClone() {
      if (this is _IRetrievalWorkerState dt) { return dt; }
      return new RetrievalWorkerState(_pendingBatch, _pendingOrder, _processingBatch, _processingOrder, _stopped);
    }
    public override bool Equals(object other) {
      var oth = other as TsRetrievalRuntime.RetrievalWorkerState;
      return oth != null && object.Equals(this._pendingBatch, oth._pendingBatch) && object.Equals(this._pendingOrder, oth._pendingOrder) && object.Equals(this._processingBatch, oth._processingBatch) && object.Equals(this._processingOrder, oth._processingOrder) && this._stopped == oth._stopped;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pendingBatch));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pendingOrder));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._processingBatch));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._processingOrder));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._stopped));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsRetrievalRuntime.RetrievalWorkerState.RetrievalWorkerState";
      s += "(";
      s += Dafny.Helpers.ToString(this._pendingBatch);
      s += ", ";
      s += Dafny.Helpers.ToString(this._pendingOrder);
      s += ", ";
      s += Dafny.Helpers.ToString(this._processingBatch);
      s += ", ";
      s += Dafny.Helpers.ToString(this._processingOrder);
      s += ", ";
      s += Dafny.Helpers.ToString(this._stopped);
      s += ")";
      return s;
    }
    private static readonly TsRetrievalRuntime._IRetrievalWorkerState theDefault = create(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty, Dafny.Sequence<BigInteger>.Empty, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty, Dafny.Sequence<BigInteger>.Empty, false);
    public static TsRetrievalRuntime._IRetrievalWorkerState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsRetrievalRuntime._IRetrievalWorkerState> _TYPE = new Dafny.TypeDescriptor<TsRetrievalRuntime._IRetrievalWorkerState>(TsRetrievalRuntime.RetrievalWorkerState.Default());
    public static Dafny.TypeDescriptor<TsRetrievalRuntime._IRetrievalWorkerState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRetrievalWorkerState create(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingBatch, Dafny.ISequence<BigInteger> pendingOrder, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> processingBatch, Dafny.ISequence<BigInteger> processingOrder, bool stopped) {
      return new RetrievalWorkerState(pendingBatch, pendingOrder, processingBatch, processingOrder, stopped);
    }
    public static _IRetrievalWorkerState create_RetrievalWorkerState(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingBatch, Dafny.ISequence<BigInteger> pendingOrder, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> processingBatch, Dafny.ISequence<BigInteger> processingOrder, bool stopped) {
      return create(pendingBatch, pendingOrder, processingBatch, processingOrder, stopped);
    }
    public bool is_RetrievalWorkerState { get { return true; } }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_pendingBatch {
      get {
        return this._pendingBatch;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_pendingOrder {
      get {
        return this._pendingOrder;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_processingBatch {
      get {
        return this._processingBatch;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_processingOrder {
      get {
        return this._processingOrder;
      }
    }
    public bool dtor_stopped {
      get {
        return this._stopped;
      }
    }
  }

  public interface _IStateChange {
    bool is_StateChange { get; }
    TsRetrievalRuntime._IRetrievalWorkerState dtor_state { get; }
    bool dtor_changed { get; }
    _IStateChange DowncastClone();
  }
  public class StateChange : _IStateChange {
    public readonly TsRetrievalRuntime._IRetrievalWorkerState _state;
    public readonly bool _changed;
    public StateChange(TsRetrievalRuntime._IRetrievalWorkerState state, bool changed) {
      this._state = state;
      this._changed = changed;
    }
    public _IStateChange DowncastClone() {
      if (this is _IStateChange dt) { return dt; }
      return new StateChange(_state, _changed);
    }
    public override bool Equals(object other) {
      var oth = other as TsRetrievalRuntime.StateChange;
      return oth != null && object.Equals(this._state, oth._state) && this._changed == oth._changed;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._changed));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsRetrievalRuntime.StateChange.StateChange";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._changed);
      s += ")";
      return s;
    }
    private static readonly TsRetrievalRuntime._IStateChange theDefault = create(TsRetrievalRuntime.RetrievalWorkerState.Default(), false);
    public static TsRetrievalRuntime._IStateChange Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsRetrievalRuntime._IStateChange> _TYPE = new Dafny.TypeDescriptor<TsRetrievalRuntime._IStateChange>(TsRetrievalRuntime.StateChange.Default());
    public static Dafny.TypeDescriptor<TsRetrievalRuntime._IStateChange> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStateChange create(TsRetrievalRuntime._IRetrievalWorkerState state, bool changed) {
      return new StateChange(state, changed);
    }
    public static _IStateChange create_StateChange(TsRetrievalRuntime._IRetrievalWorkerState state, bool changed) {
      return create(state, changed);
    }
    public bool is_StateChange { get { return true; } }
    public TsRetrievalRuntime._IRetrievalWorkerState dtor_state {
      get {
        return this._state;
      }
    }
    public bool dtor_changed {
      get {
        return this._changed;
      }
    }
  }
} // end of namespace TsRetrievalRuntime
namespace TsLimitStreamRuntime {

  public partial class __default {
    public static TsLimitStreamRuntime._ILimitStreamState EmptyLimitStreamState() {
      return TsLimitStreamRuntime.LimitStreamState.create(Dafny.Map<BigInteger, BigInteger>.FromElements(), TsLimitQueriesRuntime.__default.EmptyLimitQueriesState(), TsRetrievalRuntime.__default.EmptyWorkerState());
    }
    public static bool LimitStreamConsistent(TsLimitStreamRuntime._ILimitStreamState state) {
      return (TsLimitQueriesRuntime.__default.LimitQueriesConsistent((state).dtor_queries)) && (TsRetrievalRuntime.__default.WorkerConsistent((state).dtor_retrieval));
    }
    public static TsLimitStreamRuntime._ILimitStreamState SetQueries(TsLimitStreamRuntime._ILimitStreamState state, TsLimitQueriesRuntime._ILimitQueriesState queries)
    {
      return TsLimitStreamRuntime.LimitStreamState.create((state).dtor_store, queries, (state).dtor_retrieval);
    }
    public static TsLimitStreamRuntime._ILimitStreamState SetRetrieval(TsLimitStreamRuntime._ILimitStreamState state, TsRetrievalRuntime._IRetrievalWorkerState retrieval)
    {
      return TsLimitStreamRuntime.LimitStreamState.create((state).dtor_store, (state).dtor_queries, retrieval);
    }
    public static TsLimitStreamRuntime._ILimitStreamState SetStore(TsLimitStreamRuntime._ILimitStreamState state, Dafny.IMap<BigInteger,BigInteger> store)
    {
      return TsLimitStreamRuntime.LimitStreamState.create(store, (state).dtor_queries, (state).dtor_retrieval);
    }
    public static TsLimitStreamRuntime._ILimitStreamState RegisterIfAllowed(TsLimitStreamRuntime._ILimitStreamState state, BigInteger docId, BigInteger queryId)
    {
      if (TsRetrievalRuntime.__default.CanRegister((state).dtor_retrieval, docId, queryId)) {
        return TsLimitStreamRuntime.__default.SetRetrieval(state, TsRetrievalRuntime.__default.Register((state).dtor_retrieval, docId, queryId));
      } else {
        return state;
      }
    }
    public static TsLimitStreamRuntime._ILimitStreamState NotifyRetrievalResolved(TsLimitStreamRuntime._ILimitStreamState state, BigInteger docId)
    {
      return TsLimitStreamRuntime.LimitStreamState.create((state).dtor_store, TsLimitQueriesRuntime.__default.ResolvePendingForDoc((state).dtor_queries, docId), (TsRetrievalRuntime.__default.ResolveDoc((state).dtor_retrieval, docId)).dtor_state);
    }
    public static TsLimitStreamRuntime._ILimitStreamState RegisterDocsForQuery(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<BigInteger> docs, BigInteger queryId)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return state;
      } else {
        TsLimitStreamRuntime._ILimitStreamState _in0 = TsLimitStreamRuntime.__default.RegisterIfAllowed(state, (docs).Select(BigInteger.Zero), queryId);
        Dafny.ISequence<BigInteger> _in1 = (docs).Drop(BigInteger.One);
        BigInteger _in2 = queryId;
        state = _in0;
        docs = _in1;
        queryId = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.IMap<BigInteger,BigInteger> SeedDocsStore(Dafny.IMap<BigInteger,BigInteger> store, Dafny.ISequence<ThunderDbStack._ISeedDoc> docs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return store;
      } else {
        Dafny.IMap<BigInteger,BigInteger> _in0 = Dafny.Map<BigInteger, BigInteger>.Update(store, ((docs).Select(BigInteger.Zero)).dtor_id, ((docs).Select(BigInteger.Zero)).dtor_state);
        Dafny.ISequence<ThunderDbStack._ISeedDoc> _in1 = (docs).Drop(BigInteger.One);
        store = _in0;
        docs = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState SeedDocsQueries(TsLimitQueriesRuntime._ILimitQueriesState queries, Dafny.ISequence<ThunderDbStack._ISeedDoc> docs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return queries;
      } else {
        TsLimitQueriesRuntime._ILimitQueriesState _0_newState = TsLimitQueriesRuntime.LimitQueriesState.create(TsDocsRuntime.__default.AddDoc((queries).dtor_docs, ThunderDbStack.__default.GetScore(((docs).Select(BigInteger.Zero)).dtor_state), ((docs).Select(BigInteger.Zero)).dtor_id), (queries).dtor_queries, (queries).dtor_nextId, (queries).dtor_infos, (queries).dtor_baseScores, (queries).dtor_pendingByQuery, (queries).dtor_pendingByDoc);
        TsLimitQueriesRuntime._ILimitQueriesState _in0 = _0_newState;
        Dafny.ISequence<ThunderDbStack._ISeedDoc> _in1 = (docs).Drop(BigInteger.One);
        queries = _in0;
        docs = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FilterMissing(Dafny.ISequence<BigInteger> ids, Dafny.ISequence<BigInteger> keep)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (ThunderDbStack.__default.ContainsQueryId(keep, (ids).Select(BigInteger.Zero))) {
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        Dafny.ISequence<BigInteger> _in1 = keep;
        ids = _in0;
        keep = _in1;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in2 = (ids).Drop(BigInteger.One);
        Dafny.ISequence<BigInteger> _in3 = keep;
        ids = _in2;
        keep = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitStreamRuntime._ILimitStreamState HandleLostQueries(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<BigInteger> queries)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return state;
      } else {
        TsLimitQueriesRuntime._IGapFillResult _0_gap = TsLimitQueriesRuntime.__default.FillGap((state).dtor_queries, (queries).Select(BigInteger.Zero));
        TsLimitStreamRuntime._ILimitStreamState _1_nextState = TsLimitStreamRuntime.__default.SetQueries(state, (_0_gap).dtor_state);
        TsLimitStreamRuntime._ILimitStreamState _2_registered = ((System.Func<TsLimitStreamRuntime._ILimitStreamState>)(() => {
          DocsIndexModel._IMaybeDocId _source0 = (_0_gap).dtor_doc;
          {
            if (_source0.is_NoDoc) {
              return _1_nextState;
            }
          }
          {
            BigInteger _3_docId = _source0.dtor_doc;
            return TsLimitStreamRuntime.__default.RegisterIfAllowed(_1_nextState, _3_docId, (queries).Select(BigInteger.Zero));
          }
        }))();
        TsLimitStreamRuntime._ILimitStreamState _in0 = _2_registered;
        Dafny.ISequence<BigInteger> _in1 = (queries).Drop(BigInteger.One);
        state = _in0;
        queries = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitStreamRuntime._IOverflowResult HandleOverflowQueries(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<BigInteger> queries)
    {
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return TsLimitStreamRuntime.OverflowResult.create(state, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements());
      } else {
        BigInteger _0_queryId = (queries).Select(BigInteger.Zero);
        DocsIndexModel._IMaybeDocId _1_overflowDoc = TsLimitQueriesRuntime.__default.PickOverflowDoc((state).dtor_queries, _0_queryId);
        DocsIndexModel._IMaybeDocId _source0 = _1_overflowDoc;
        {
          if (_source0.is_NoDoc) {
            return TsLimitStreamRuntime.__default.HandleOverflowQueries(state, (queries).Drop(BigInteger.One));
          }
        }
        {
          BigInteger _2_docId = _source0.dtor_doc;
          TsLimitQueriesRuntime._IStateChange _3_cancelledPending = TsLimitQueriesRuntime.__default.CancelPendingForQuery((state).dtor_queries, _2_docId, _0_queryId);
          TsRetrievalRuntime._IStateChange _4_retrievalCancelled = TsRetrievalRuntime.__default.Cancel((state).dtor_retrieval, _2_docId, _0_queryId);
          TsLimitStreamRuntime._ILimitStreamState _5_state1 = TsLimitStreamRuntime.LimitStreamState.create((state).dtor_store, (_3_cancelledPending).dtor_state, (_4_retrievalCancelled).dtor_state);
          TsLimitStreamRuntime._ILimitStreamState _6_state2 = (((_3_cancelledPending).dtor_changed) ? (Dafny.Helpers.Let<TsLimitQueriesRuntime._IGapFillResult, TsLimitStreamRuntime._ILimitStreamState>(TsLimitQueriesRuntime.__default.FillGap((_5_state1).dtor_queries, _0_queryId), _pat_let2_0 => Dafny.Helpers.Let<TsLimitQueriesRuntime._IGapFillResult, TsLimitStreamRuntime._ILimitStreamState>(_pat_let2_0, _7_gap => Dafny.Helpers.Let<TsLimitStreamRuntime._ILimitStreamState, TsLimitStreamRuntime._ILimitStreamState>(TsLimitStreamRuntime.__default.SetQueries(_5_state1, (_7_gap).dtor_state), _pat_let3_0 => Dafny.Helpers.Let<TsLimitStreamRuntime._ILimitStreamState, TsLimitStreamRuntime._ILimitStreamState>(_pat_let3_0, _8_gapState => ((System.Func<TsLimitStreamRuntime._ILimitStreamState>)(() => {
            DocsIndexModel._IMaybeDocId _source1 = (_7_gap).dtor_doc;
            {
              if (_source1.is_NoDoc) {
                return _8_gapState;
              }
            }
            {
              BigInteger _9_replacement = _source1.dtor_doc;
              return TsLimitStreamRuntime.__default.RegisterIfAllowed(_8_gapState, _9_replacement, _0_queryId);
            }
          }))()))))) : (_5_state1));
          TsLimitStreamRuntime._IOverflowResult _10_rest = TsLimitStreamRuntime.__default.HandleOverflowQueries(_6_state2, (queries).Drop(BigInteger.One));
          return TsLimitStreamRuntime.OverflowResult.create((_10_rest).dtor_state, Dafny.Sequence<ThunderDbStack._IEviction>.Concat(Dafny.Sequence<ThunderDbStack._IEviction>.FromElements(ThunderDbStack.Eviction.create(_0_queryId, _2_docId)), (_10_rest).dtor_evictions));
        }
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IDownstreamEvent> MatchEventIfAny(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions)
    {
      if ((((new BigInteger((matchesOld).Count)).Sign == 0) && ((new BigInteger((matchesNew).Count)).Sign == 0)) && ((new BigInteger((evictions).Count)).Sign == 0)) {
        return Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      } else {
        return Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(ThunderDbStack.MatchPayload.create(docId, oldState, newState, matchesOld, matchesNew, evictions)));
      }
    }
    public static TsLimitStreamRuntime._IStreamStep HandleDocChange(TsLimitStreamRuntime._ILimitStreamState state, BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      ThunderDbStack._IMaybeDocState _source0 = oldState;
      {
        if (_source0.is_NoState) {
          return TsLimitStreamRuntime.__default.HandleDocChangeNoOld(state, docId, newState);
        }
      }
      {
        BigInteger _0_oldDocState = _source0.dtor_state;
        ThunderDbStack._IMaybeDocState _source1 = newState;
        {
          if (_source1.is_HasState) {
            BigInteger _1_nextDocState = _source1.dtor_state;
            if ((ThunderDbStack.__default.GetScore(_0_oldDocState)) == (ThunderDbStack.__default.GetScore(_1_nextDocState))) {
              Dafny.ISequence<BigInteger> _2_covering = TsLimitQueriesRuntime.__default.GetQueriesCovering((state).dtor_queries, ThunderDbStack.__default.GetScore(_0_oldDocState), DocsIndexModel.MaybeDocId.create_SomeDoc(docId));
              return TsLimitStreamRuntime.StreamStep.create(TsLimitStreamRuntime.__default.NotifyRetrievalResolved(state, docId), Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(ThunderDbStack.MatchPayload.create(docId, oldState, newState, _2_covering, _2_covering, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements()))));
            } else {
              return TsLimitStreamRuntime.__default.HandleDocChangeGeneral(state, docId, oldState, newState, ThunderDbStack.__default.GetScore(_0_oldDocState), ThunderDbStack.MaybeDocState.create_HasState(_1_nextDocState));
            }
          }
        }
        {
          return TsLimitStreamRuntime.__default.HandleDocChangeGeneral(state, docId, oldState, newState, ThunderDbStack.__default.GetScore(_0_oldDocState), ThunderDbStack.MaybeDocState.create_NoState());
        }
      }
    }
    public static TsLimitStreamRuntime._IStreamStep HandleDocChangeNoOld(TsLimitStreamRuntime._ILimitStreamState state, BigInteger docId, ThunderDbStack._IMaybeDocState newState)
    {
      ThunderDbStack._IMaybeDocState _source0 = newState;
      {
        if (_source0.is_NoState) {
          return TsLimitStreamRuntime.StreamStep.create(TsLimitStreamRuntime.__default.NotifyRetrievalResolved(state, docId), Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements());
        }
      }
      {
        BigInteger _0_nextDocState = _source0.dtor_state;
        TsLimitQueriesRuntime._IAddDocumentResult _1_added = TsLimitQueriesRuntime.__default.AddDocument((state).dtor_queries, ThunderDbStack.__default.GetScore(_0_nextDocState), docId);
        TsLimitStreamRuntime._ILimitStreamState _2_state1 = TsLimitStreamRuntime.__default.SetQueries(state, (_1_added).dtor_state);
        TsLimitStreamRuntime._IOverflowResult _3_overflow = TsLimitStreamRuntime.__default.HandleOverflowQueries(_2_state1, TsLimitStreamRuntime.__default.FilterMissing((_1_added).dtor_blocked, Dafny.Sequence<BigInteger>.FromElements()));
        TsLimitStreamRuntime._ILimitStreamState _4_state2 = TsLimitStreamRuntime.__default.NotifyRetrievalResolved((_3_overflow).dtor_state, docId);
        return TsLimitStreamRuntime.StreamStep.create(_4_state2, TsLimitStreamRuntime.__default.MatchEventIfAny(docId, ThunderDbStack.MaybeDocState.create_NoState(), newState, Dafny.Sequence<BigInteger>.FromElements(), (_1_added).dtor_matched, (_3_overflow).dtor_evictions));
      }
    }
    public static TsLimitStreamRuntime._IStreamStep HandleDocChangeGeneral(TsLimitStreamRuntime._ILimitStreamState state, BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, BigInteger oldScore, ThunderDbStack._IMaybeDocState nextDocState)
    {
      TsLimitQueriesRuntime._IRemoveDocumentResult _0_removed = TsLimitQueriesRuntime.__default.RemoveDocument((state).dtor_queries, oldScore, docId);
      TsLimitStreamRuntime._ILimitStreamState _1_state1 = TsLimitStreamRuntime.__default.SetQueries(state, (_0_removed).dtor_state);
      TsLimitQueriesRuntime._IAddDocumentResult _2_added = ((System.Func<TsLimitQueriesRuntime._IAddDocumentResult>)(() => {
        ThunderDbStack._IMaybeDocState _source0 = nextDocState;
        {
          if (_source0.is_NoState) {
            return TsLimitQueriesRuntime.AddDocumentResult.create((_1_state1).dtor_queries, Dafny.Sequence<BigInteger>.FromElements(), Dafny.Sequence<BigInteger>.FromElements());
          }
        }
        {
          BigInteger _3_nextState = _source0.dtor_state;
          return TsLimitQueriesRuntime.__default.AddDocument((_1_state1).dtor_queries, ThunderDbStack.__default.GetScore(_3_nextState), docId);
        }
      }))();
      TsLimitStreamRuntime._ILimitStreamState _4_state2 = TsLimitStreamRuntime.__default.SetQueries(_1_state1, (_2_added).dtor_state);
      Dafny.ISequence<BigInteger> _5_lostQueries = TsLimitStreamRuntime.__default.FilterMissing((_0_removed).dtor_removed, (_2_added).dtor_matched);
      TsLimitStreamRuntime._ILimitStreamState _6_state3 = TsLimitStreamRuntime.__default.HandleLostQueries(_4_state2, _5_lostQueries);
      Dafny.ISequence<BigInteger> _7_overflowQueries = TsLimitStreamRuntime.__default.FilterMissing((_2_added).dtor_blocked, (_0_removed).dtor_removed);
      TsLimitStreamRuntime._IOverflowResult _8_overflow = TsLimitStreamRuntime.__default.HandleOverflowQueries(_6_state3, _7_overflowQueries);
      TsLimitStreamRuntime._ILimitStreamState _9_state4 = TsLimitStreamRuntime.__default.NotifyRetrievalResolved((_8_overflow).dtor_state, docId);
      return TsLimitStreamRuntime.StreamStep.create(_9_state4, TsLimitStreamRuntime.__default.MatchEventIfAny(docId, oldState, newState, (_0_removed).dtor_removed, (_2_added).dtor_matched, (_8_overflow).dtor_evictions));
    }
    public static TsLimitStreamRuntime._IStreamStep HandleQueryAdd(TsLimitStreamRuntime._ILimitStreamState state, ThunderDbStack._IQuerySpec spec)
    {
      TsLimitQueriesRuntime._IQueryAddResult _0_added = TsLimitQueriesRuntime.__default.AddQuery((state).dtor_queries, (spec).dtor_minScore, (spec).dtor_limit, (spec).dtor_maxScore);
      TsLimitStreamRuntime._ILimitStreamState _1_state1 = TsLimitStreamRuntime.__default.SetQueries(state, (_0_added).dtor_state);
      Dafny.ISequence<BigInteger> _2_seedDocs = TsDocsRuntime.__default.CollectRangeDocs(((state).dtor_queries).dtor_docs, (spec).dtor_minScore, (spec).dtor_maxScore, (spec).dtor_limit);
      return TsLimitStreamRuntime.StreamStep.create(TsLimitStreamRuntime.__default.RegisterDocsForQuery(_1_state1, _2_seedDocs, (_0_added).dtor_queryId), Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements());
    }
    public static TsLimitStreamRuntime._IStreamStep HandleQueryRemove(TsLimitStreamRuntime._ILimitStreamState state, BigInteger queryId)
    {
      TsLimitQueriesRuntime._IStateChange _0_removed = TsLimitQueriesRuntime.__default.RemoveQuery((state).dtor_queries, queryId);
      return TsLimitStreamRuntime.StreamStep.create(TsLimitStreamRuntime.__default.SetQueries(state, (_0_removed).dtor_state), Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements());
    }
    public static TsLimitStreamRuntime._IStreamStep HandleSeedDocs(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<ThunderDbStack._ISeedDoc> docs)
    {
      return TsLimitStreamRuntime.StreamStep.create(TsLimitStreamRuntime.LimitStreamState.create(TsLimitStreamRuntime.__default.SeedDocsStore((state).dtor_store, docs), TsLimitStreamRuntime.__default.SeedDocsQueries((state).dtor_queries, docs), (state).dtor_retrieval), Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements());
    }
    public static TsLimitStreamRuntime._IStreamStep HandleItem(TsLimitStreamRuntime._ILimitStreamState state, ThunderDbStack._IStreamItem item)
    {
      ThunderDbStack._IStreamItem _source0 = item;
      {
        if (_source0.is_QueryAddItem) {
          ThunderDbStack._IQuerySpec _0_spec = _source0.dtor_spec;
          return TsLimitStreamRuntime.__default.HandleQueryAdd(state, _0_spec);
        }
      }
      {
        if (_source0.is_QueryRemoveItem) {
          BigInteger _1_id = _source0.dtor_id;
          return TsLimitStreamRuntime.__default.HandleQueryRemove(state, _1_id);
        }
      }
      {
        if (_source0.is_SeedDocsItem) {
          Dafny.ISequence<ThunderDbStack._ISeedDoc> _2_docs = _source0.dtor_docs;
          return TsLimitStreamRuntime.__default.HandleSeedDocs(state, _2_docs);
        }
      }
      {
        BigInteger _3_id = _source0.dtor_id;
        ThunderDbStack._IMaybeDocState _4_oldState = _source0.dtor_oldState;
        ThunderDbStack._IMaybeDocState _5_newState = _source0.dtor_newState;
        Dafny.IMap<BigInteger,BigInteger> _6_nextStore = ((System.Func<Dafny.IMap<BigInteger,BigInteger>>)(() => {
          ThunderDbStack._IMaybeDocState _source1 = _5_newState;
          {
            if (_source1.is_NoState) {
              return ThunderDbStack.__default.RemoveStoredDoc((state).dtor_store, _3_id);
            }
          }
          {
            BigInteger _7_docState = _source1.dtor_state;
            return ThunderDbStack.__default.PutStoredDoc((state).dtor_store, _3_id, _7_docState);
          }
        }))();
        return TsLimitStreamRuntime.__default.HandleDocChange(TsLimitStreamRuntime.__default.SetStore(state, _6_nextStore), _3_id, _4_oldState, _5_newState);
      }
    }
    public static TsLimitQueriesRuntime._ILimitQueriesState ResolveDeliveredDocs(TsLimitQueriesRuntime._ILimitQueriesState queries, Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return queries;
      } else {
        TsLimitQueriesRuntime._ILimitQueriesState _in0 = TsLimitQueriesRuntime.__default.ResolvePendingForDoc(queries, ((docs).Select(BigInteger.Zero)).dtor_docId);
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _in1 = (docs).Drop(BigInteger.One);
        queries = _in0;
        docs = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static TsLimitStreamRuntime._IStreamStep DrainRetrievalCycle(TsLimitStreamRuntime._ILimitStreamState state) {
      if (!(TsRetrievalRuntime.__default.HasPendingWork((state).dtor_retrieval))) {
        return TsLimitStreamRuntime.StreamStep.create(state, Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements());
      } else {
        TsRetrievalRuntime._IRetrievalWorkerState _0_processing = TsRetrievalRuntime.__default.BeginCycle((state).dtor_retrieval);
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _1_payload = TsRetrievalRuntime.__default.BuildPayload(_0_processing, (state).dtor_store);
        TsRetrievalRuntime._IRetrievalWorkerState _2_finished = TsRetrievalRuntime.__default.FinishCycle(_0_processing);
        TsLimitQueriesRuntime._ILimitQueriesState _3_nextQueries = TsLimitStreamRuntime.__default.ResolveDeliveredDocs((state).dtor_queries, _1_payload);
        TsLimitStreamRuntime._ILimitStreamState _4_nextState = TsLimitStreamRuntime.LimitStreamState.create((state).dtor_store, _3_nextQueries, _2_finished);
        if ((new BigInteger((_1_payload).Count)).Sign == 0) {
          return TsLimitStreamRuntime.StreamStep.create(_4_nextState, Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements());
        } else {
          return TsLimitStreamRuntime.StreamStep.create(_4_nextState, Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_1_payload)));
        }
      }
    }
    public static TsLimitStreamRuntime._ILimitStreamState Stop(TsLimitStreamRuntime._ILimitStreamState state) {
      return TsLimitStreamRuntime.__default.SetRetrieval(state, TsRetrievalRuntime.__default.Stop((state).dtor_retrieval));
    }
  }

  public interface _ILimitStreamState {
    bool is_LimitStreamState { get; }
    Dafny.IMap<BigInteger,BigInteger> dtor_store { get; }
    TsLimitQueriesRuntime._ILimitQueriesState dtor_queries { get; }
    TsRetrievalRuntime._IRetrievalWorkerState dtor_retrieval { get; }
    _ILimitStreamState DowncastClone();
  }
  public class LimitStreamState : _ILimitStreamState {
    public readonly Dafny.IMap<BigInteger,BigInteger> _store;
    public readonly TsLimitQueriesRuntime._ILimitQueriesState _queries;
    public readonly TsRetrievalRuntime._IRetrievalWorkerState _retrieval;
    public LimitStreamState(Dafny.IMap<BigInteger,BigInteger> store, TsLimitQueriesRuntime._ILimitQueriesState queries, TsRetrievalRuntime._IRetrievalWorkerState retrieval) {
      this._store = store;
      this._queries = queries;
      this._retrieval = retrieval;
    }
    public _ILimitStreamState DowncastClone() {
      if (this is _ILimitStreamState dt) { return dt; }
      return new LimitStreamState(_store, _queries, _retrieval);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitStreamRuntime.LimitStreamState;
      return oth != null && object.Equals(this._store, oth._store) && object.Equals(this._queries, oth._queries) && object.Equals(this._retrieval, oth._retrieval);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._store));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queries));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retrieval));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitStreamRuntime.LimitStreamState.LimitStreamState";
      s += "(";
      s += Dafny.Helpers.ToString(this._store);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queries);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retrieval);
      s += ")";
      return s;
    }
    private static readonly TsLimitStreamRuntime._ILimitStreamState theDefault = create(Dafny.Map<BigInteger, BigInteger>.Empty, TsLimitQueriesRuntime.LimitQueriesState.Default(), TsRetrievalRuntime.RetrievalWorkerState.Default());
    public static TsLimitStreamRuntime._ILimitStreamState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitStreamRuntime._ILimitStreamState> _TYPE = new Dafny.TypeDescriptor<TsLimitStreamRuntime._ILimitStreamState>(TsLimitStreamRuntime.LimitStreamState.Default());
    public static Dafny.TypeDescriptor<TsLimitStreamRuntime._ILimitStreamState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ILimitStreamState create(Dafny.IMap<BigInteger,BigInteger> store, TsLimitQueriesRuntime._ILimitQueriesState queries, TsRetrievalRuntime._IRetrievalWorkerState retrieval) {
      return new LimitStreamState(store, queries, retrieval);
    }
    public static _ILimitStreamState create_LimitStreamState(Dafny.IMap<BigInteger,BigInteger> store, TsLimitQueriesRuntime._ILimitQueriesState queries, TsRetrievalRuntime._IRetrievalWorkerState retrieval) {
      return create(store, queries, retrieval);
    }
    public bool is_LimitStreamState { get { return true; } }
    public Dafny.IMap<BigInteger,BigInteger> dtor_store {
      get {
        return this._store;
      }
    }
    public TsLimitQueriesRuntime._ILimitQueriesState dtor_queries {
      get {
        return this._queries;
      }
    }
    public TsRetrievalRuntime._IRetrievalWorkerState dtor_retrieval {
      get {
        return this._retrieval;
      }
    }
  }

  public interface _IStreamStep {
    bool is_StreamStep { get; }
    TsLimitStreamRuntime._ILimitStreamState dtor_state { get; }
    Dafny.ISequence<ThunderDbStack._IDownstreamEvent> dtor_events { get; }
    _IStreamStep DowncastClone();
  }
  public class StreamStep : _IStreamStep {
    public readonly TsLimitStreamRuntime._ILimitStreamState _state;
    public readonly Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _events;
    public StreamStep(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events) {
      this._state = state;
      this._events = events;
    }
    public _IStreamStep DowncastClone() {
      if (this is _IStreamStep dt) { return dt; }
      return new StreamStep(_state, _events);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitStreamRuntime.StreamStep;
      return oth != null && object.Equals(this._state, oth._state) && object.Equals(this._events, oth._events);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._events));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitStreamRuntime.StreamStep.StreamStep";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._events);
      s += ")";
      return s;
    }
    private static readonly TsLimitStreamRuntime._IStreamStep theDefault = create(TsLimitStreamRuntime.LimitStreamState.Default(), Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty);
    public static TsLimitStreamRuntime._IStreamStep Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitStreamRuntime._IStreamStep> _TYPE = new Dafny.TypeDescriptor<TsLimitStreamRuntime._IStreamStep>(TsLimitStreamRuntime.StreamStep.Default());
    public static Dafny.TypeDescriptor<TsLimitStreamRuntime._IStreamStep> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStreamStep create(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events) {
      return new StreamStep(state, events);
    }
    public static _IStreamStep create_StreamStep(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events) {
      return create(state, events);
    }
    public bool is_StreamStep { get { return true; } }
    public TsLimitStreamRuntime._ILimitStreamState dtor_state {
      get {
        return this._state;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IDownstreamEvent> dtor_events {
      get {
        return this._events;
      }
    }
  }

  public interface _IOverflowResult {
    bool is_OverflowResult { get; }
    TsLimitStreamRuntime._ILimitStreamState dtor_state { get; }
    Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions { get; }
    _IOverflowResult DowncastClone();
  }
  public class OverflowResult : _IOverflowResult {
    public readonly TsLimitStreamRuntime._ILimitStreamState _state;
    public readonly Dafny.ISequence<ThunderDbStack._IEviction> _evictions;
    public OverflowResult(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      this._state = state;
      this._evictions = evictions;
    }
    public _IOverflowResult DowncastClone() {
      if (this is _IOverflowResult dt) { return dt; }
      return new OverflowResult(_state, _evictions);
    }
    public override bool Equals(object other) {
      var oth = other as TsLimitStreamRuntime.OverflowResult;
      return oth != null && object.Equals(this._state, oth._state) && object.Equals(this._evictions, oth._evictions);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._evictions));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TsLimitStreamRuntime.OverflowResult.OverflowResult";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._evictions);
      s += ")";
      return s;
    }
    private static readonly TsLimitStreamRuntime._IOverflowResult theDefault = create(TsLimitStreamRuntime.LimitStreamState.Default(), Dafny.Sequence<ThunderDbStack._IEviction>.Empty);
    public static TsLimitStreamRuntime._IOverflowResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TsLimitStreamRuntime._IOverflowResult> _TYPE = new Dafny.TypeDescriptor<TsLimitStreamRuntime._IOverflowResult>(TsLimitStreamRuntime.OverflowResult.Default());
    public static Dafny.TypeDescriptor<TsLimitStreamRuntime._IOverflowResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOverflowResult create(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return new OverflowResult(state, evictions);
    }
    public static _IOverflowResult create_OverflowResult(TsLimitStreamRuntime._ILimitStreamState state, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return create(state, evictions);
    }
    public bool is_OverflowResult { get { return true; } }
    public TsLimitStreamRuntime._ILimitStreamState dtor_state {
      get {
        return this._state;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions {
      get {
        return this._evictions;
      }
    }
  }
} // end of namespace TsLimitStreamRuntime
namespace TsLimitStreamSmoke {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      TsLimitStreamRuntime._ILimitStreamState _0_state;
      _0_state = TsLimitStreamRuntime.__default.EmptyLimitStreamState();
      if (!(TsLimitStreamRuntime.__default.LimitStreamConsistent(_0_state))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(10,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      TsLimitStreamRuntime._IStreamStep _1_seeded;
      _1_seeded = TsLimitStreamRuntime.__default.HandleItem(_0_state, ThunderDbStack.StreamItem.create_SeedDocsItem(Dafny.Sequence<ThunderDbStack._ISeedDoc>.FromElements(ThunderDbStack.SeedDoc.create(BigInteger.One, new BigInteger(10)), ThunderDbStack.SeedDoc.create(new BigInteger(2), new BigInteger(20)), ThunderDbStack.SeedDoc.create(new BigInteger(3), new BigInteger(30)))));
      _0_state = (_1_seeded).dtor_state;
      if (!(((_1_seeded).dtor_events).Equals(Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements()))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(14,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(((_0_state).dtor_store).Equals(Dafny.Map<BigInteger, BigInteger>.FromElements(new Dafny.Pair<BigInteger, BigInteger>(BigInteger.One, new BigInteger(10)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(2), new BigInteger(20)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(3), new BigInteger(30)))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(15,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(((((_0_state).dtor_queries).dtor_docs)).Equals(Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(new BigInteger(10), BigInteger.One), DocsIndexModel.Entry.create(new BigInteger(20), new BigInteger(2)), DocsIndexModel.Entry.create(new BigInteger(30), new BigInteger(3)))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(16,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      TsLimitStreamRuntime._IStreamStep _2_added;
      _2_added = TsLimitStreamRuntime.__default.HandleItem(_0_state, ThunderDbStack.StreamItem.create_QueryAddItem(ThunderDbStack.QuerySpec.create(BigInteger.Zero, new BigInteger(100), new BigInteger(2))));
      _0_state = (_2_added).dtor_state;
      if (!(((_2_added).dtor_events).Equals(Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements()))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(20,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!((((_0_state).dtor_queries).dtor_infos).Contains(BigInteger.One))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(21,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(((Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select(((_0_state).dtor_queries).dtor_infos,BigInteger.One)).dtor_currentMatches) == (new BigInteger(2)))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(22,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!((((_0_state).dtor_retrieval).dtor_pendingOrder).Equals(Dafny.Sequence<BigInteger>.FromElements(BigInteger.One, new BigInteger(2))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(23,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      TsLimitStreamRuntime._IStreamStep _3_retrieval;
      _3_retrieval = TsLimitStreamRuntime.__default.DrainRetrievalCycle(_0_state);
      _0_state = (_3_retrieval).dtor_state;
      if (!(((_3_retrieval).dtor_events).Equals(Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(BigInteger.One, new BigInteger(10), Dafny.Sequence<BigInteger>.FromElements(BigInteger.One)), ThunderDbStack.RetrievalDoc.create(new BigInteger(2), new BigInteger(20), Dafny.Sequence<BigInteger>.FromElements(BigInteger.One)))))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(27,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!((((_0_state).dtor_retrieval).dtor_pendingOrder).Equals(Dafny.Sequence<BigInteger>.FromElements()))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(28,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      TsLimitStreamRuntime._IStreamStep _4_removed;
      _4_removed = TsLimitStreamRuntime.__default.HandleItem(_0_state, ThunderDbStack.StreamItem.create_DocChangeItem(BigInteger.One, ThunderDbStack.MaybeDocState.create_HasState(new BigInteger(10)), ThunderDbStack.MaybeDocState.create_NoState()));
      _0_state = (_4_removed).dtor_state;
      if (!(((_4_removed).dtor_events).Equals(Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(ThunderDbStack.MatchPayload.create(BigInteger.One, ThunderDbStack.MaybeDocState.create_HasState(new BigInteger(10)), ThunderDbStack.MaybeDocState.create_NoState(), Dafny.Sequence<BigInteger>.FromElements(BigInteger.One), Dafny.Sequence<BigInteger>.FromElements(), Dafny.Sequence<ThunderDbStack._IEviction>.FromElements())))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(32,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(((Dafny.Map<BigInteger, TsLimitQueriesRuntime._IQueryInfo>.Select(((_0_state).dtor_queries).dtor_infos,BigInteger.One)).dtor_currentMatches) == (new BigInteger(2)))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(33,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!((Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(((_0_state).dtor_queries).dtor_pendingByQuery,BigInteger.One)).Equals(Dafny.Sequence<BigInteger>.FromElements(new BigInteger(3))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(34,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!((((_0_state).dtor_retrieval).dtor_pendingOrder).Equals(Dafny.Sequence<BigInteger>.FromElements(new BigInteger(3))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(35,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      _3_retrieval = TsLimitStreamRuntime.__default.DrainRetrievalCycle(_0_state);
      _0_state = (_3_retrieval).dtor_state;
      if (!(((_3_retrieval).dtor_events).Equals(Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(new BigInteger(3), new BigInteger(30), Dafny.Sequence<BigInteger>.FromElements(BigInteger.One)))))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(39,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(!((((_0_state).dtor_queries).dtor_pendingByQuery).Contains(BigInteger.One)))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(40,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      TsLimitStreamRuntime._IStreamStep _5_changed;
      _5_changed = TsLimitStreamRuntime.__default.HandleItem(_0_state, ThunderDbStack.StreamItem.create_DocChangeItem(BigInteger.Zero, ThunderDbStack.MaybeDocState.create_NoState(), ThunderDbStack.MaybeDocState.create_HasState(new BigInteger(5))));
      _0_state = (_5_changed).dtor_state;
      if (!(((_5_changed).dtor_events).Equals(Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(ThunderDbStack.MatchPayload.create(BigInteger.Zero, ThunderDbStack.MaybeDocState.create_NoState(), ThunderDbStack.MaybeDocState.create_HasState(new BigInteger(5)), Dafny.Sequence<BigInteger>.FromElements(), Dafny.Sequence<BigInteger>.FromElements(BigInteger.One), Dafny.Sequence<ThunderDbStack._IEviction>.FromElements(ThunderDbStack.Eviction.create(BigInteger.One, new BigInteger(3))))))))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(44,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!((((_0_state).dtor_retrieval).dtor_pendingOrder).Equals(Dafny.Sequence<BigInteger>.FromElements()))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(45,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(!((((_0_state).dtor_queries).dtor_pendingByQuery).Contains(BigInteger.One)))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(46,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      TsLimitStreamRuntime._IStreamStep _6_removedQuery;
      _6_removedQuery = TsLimitStreamRuntime.__default.HandleItem(_0_state, ThunderDbStack.StreamItem.create_QueryRemoveItem(BigInteger.One));
      _0_state = (_6_removedQuery).dtor_state;
      if (!(((_6_removedQuery).dtor_events).Equals(Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements()))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(50,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      if (!(!((((_0_state).dtor_queries).dtor_infos).Contains(BigInteger.One)))) {
        throw new Dafny.HaltException("specs/dafny-ts/TsLimitStreamSmoke.dfy(51,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ts-limit-stream-smoke passed\n")).ToVerbatimString(false));
    }
  }
} // end of namespace TsLimitStreamSmoke
namespace TsLimitStreamLemmas {

} // end of namespace TsLimitStreamLemmas
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => TsLimitStreamSmoke.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
