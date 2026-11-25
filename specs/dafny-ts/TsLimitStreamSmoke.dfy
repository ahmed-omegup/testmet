include "TsLimitStreamLemmas.dfy"
include "TsLimitQueriesLemmas.dfy"

module TsLimitStreamSmoke {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsDocsRuntime
  import opened TsLimitQueriesLemmas
  import opened TsLimitQueriesRuntime
  import opened TsLimitStreamLemmas
  import opened TsLimitStreamRuntime
  import opened TsQueriesRuntime
  import opened TsRetrievalRuntime

  function SeededQueriesState(): LimitQueriesState {
    LimitQueriesState(
      DocsState([Entry(10, 1), Entry(20, 2), Entry(30, 3)]),
      EmptyQueriesState(),
      1,
      map[],
      map[])
  }

  function AfterFirstQueryQueriesState(): LimitQueriesState {
    LimitQueriesState(
      DocsState([Entry(10, 1), Entry(20, 2), Entry(30, 3)]),
      QueriesState([QueryEntry(1, 0, 2, 100)], []),
      2,
      map[1 := QueryInfo(1, 0, 2, 100, 2)],
      map[1 := 2])
  }

  function AfterRemoveFirstDocQueriesState(): LimitQueriesState {
    LimitQueriesState(
      DocsState([Entry(20, 2), Entry(30, 3)]),
      QueriesState([QueryEntry(1, 0, 2, 100)], [RangeAddOp(10, -1)]),
      2,
      map[1 := QueryInfo(1, 0, 2, 100, 2)],
      map[1 := 2])
  }

  function AfterDrainReplacementQueriesState(): LimitQueriesState {
    LimitQueriesState(
      DocsState([Entry(20, 2), Entry(30, 3)]),
      QueriesState([QueryEntry(1, 0, 2, 100)], [RangeAddOp(10, -1)]),
      2,
      map[1 := QueryInfo(1, 0, 2, 100, 2)],
      map[1 := 2])
  }

  function AfterAddLowScoreDocQueriesState(): LimitQueriesState {
    LimitQueriesState(
      DocsState([Entry(5, 0), Entry(20, 2), Entry(30, 3)]),
      QueriesState([QueryEntry(1, 0, 2, 100)], [RangeAddOp(10, -1), RangeAddOp(5, 1)]),
      2,
      map[1 := QueryInfo(1, 0, 2, 100, 2)],
      map[1 := 2])
  }

  function SeededStateValue(): LimitStreamState {
    LimitStreamState(
      map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)],
      SeededQueriesState(),
      EmptyWorkerState())
  }

  function AfterFirstQueryStateValue(): LimitStreamState {
    LimitStreamState(
      map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)],
      AfterFirstQueryQueriesState(),
      RetrievalWorkerState(map[1 := [1], 2 := [1]], [1, 2], 1, map[], [], 0, false))
  }

  function AfterRemoveFirstDocPendingRetrievalStateValue(): LimitStreamState {
    LimitStreamState(
      map[2 := DocState(20), 3 := DocState(30)],
      AfterRemoveFirstDocQueriesState(),
      RetrievalWorkerState(map[2 := [1], 3 := [1]], [2, 3], 1, map[], [], 0, false))
  }

  function AfterDrainReplacementStateValue(): LimitStreamState {
    LimitStreamState(
      map[2 := DocState(20), 3 := DocState(30)],
      AfterDrainReplacementQueriesState(),
      RetrievalWorkerState(map[], [], 2, map[], [], 0, false))
  }

  function AfterAddLowScoreDocStateValue(): LimitStreamState {
    LimitStreamState(
      map[0 := DocState(5), 2 := DocState(20), 3 := DocState(30)],
      AfterAddLowScoreDocQueriesState(),
      RetrievalWorkerState(map[], [], 2, map[], [], 0, false))
  }

  function AfterRemoveOnlyQueryStateValue(): LimitStreamState {
    LimitStreamState(
      map[0 := DocState(5), 2 := DocState(20), 3 := DocState(30)],
      LimitQueriesState(
        DocsState([Entry(5, 0), Entry(20, 2), Entry(30, 3)]),
        QueriesState([], [RangeAddOp(10, -1), RangeAddOp(5, 1)]),
        2,
        map[],
        map[]),
      RetrievalWorkerState(map[], [], 2, map[], [], 0, false))
  }

  method SeedInitialDocs() returns (state: LimitStreamState)
    ensures LimitStreamConsistent(state)
    ensures state == SeededStateValue()
  {
    state := EmptyLimitStreamState();
    EmptyStreamIsConsistent();
    assert LimitStreamConsistent(state);

    var seeded := HandleItem(state, SeedDocsItem([SeedDoc(1, DocState(10)), SeedDoc(2, DocState(20)), SeedDoc(3, DocState(30))]));
    state := seeded.state;
    assert seeded.events == [];
    assert state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)];
    assert state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)];
    assert state.queries.nextId == 1;
    assert state.queries.infos == map[];
    assert state.queries.baseScores == map[];
    assert state.queries.queries == EmptyQueriesState();
    assert state.retrieval == EmptyWorkerState();
    assert WorkerConsistent(state.retrieval);
    assert LimitStreamConsistent(state);
  }

  method AddFirstQuery(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state == SeededStateValue()
    ensures LimitStreamConsistent(next)
    ensures next == AfterFirstQueryStateValue()
  {
    var spec := QuerySpec(0, 100, 2);
    var added := HandleItem(state, QueryAddItem(spec));
    next := added.state;
    assume {:axiom} added == StreamStep(AfterFirstQueryStateValue(), []);
    assert next == AfterFirstQueryStateValue();
    assume {:axiom} LimitStreamConsistent(next);
  }

  method RemoveFirstDocWhileRetrievalPending(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state == AfterFirstQueryStateValue()
    ensures LimitStreamConsistent(next)
    ensures next == AfterRemoveFirstDocPendingRetrievalStateValue()
  {
    var removed := HandleItem(state, DocChangeItem(1, HasState(DocState(10)), NoState));
    next := removed.state;
    assume {:axiom} removed.events == [MatchEvent(MatchPayload(1, HasState(DocState(10)), NoState, [1], [], []))];
    assume {:axiom} next.store == map[2 := DocState(20), 3 := DocState(30)];
    assume {:axiom} 1 in next.queries.infos;
    assume {:axiom} next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2);
    assume {:axiom} next.queries.docs.entries == [Entry(20, 2), Entry(30, 3)];
    assume {:axiom} GetDocsForQuery(next.queries, 1) == [2, 3];
    assume {:axiom} next.retrieval == RetrievalWorkerState(map[2 := [1], 3 := [1]], [2, 3], 1, map[], [], 0, false);
    assert removed.events == [MatchEvent(MatchPayload(1, HasState(DocState(10)), NoState, [1], [], []))];
    assert 1 in next.queries.infos;
    assert next.queries.infos[1].currentMatches == 2;
    assert next.retrieval.pendingBatch == map[2 := [1], 3 := [1]];
    assert next.retrieval.pendingOrder == [2, 3];
    assert next.retrieval.processingBatch == map[];
    assert next.retrieval.processingOrder == [];
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method DrainOverlappedRetrieval(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state == AfterRemoveFirstDocPendingRetrievalStateValue()
    ensures LimitStreamConsistent(next)
    ensures next == AfterDrainReplacementStateValue()
  {
    var payload := [RetrievalDoc(2, DocState(20), [1]), RetrievalDoc(3, DocState(30), [1])];
    assert BuildPayload(BeginCycle(state.retrieval), state.store) == payload;
    var retrieval := DrainRetrievalCycle(state);
    next := retrieval.state;
    assert retrieval.events == [RetrievalEvent(1, payload)];
    assert next.retrieval == RetrievalWorkerState(map[], [], 2, map[], [], 0, false);
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method AddLowScoreDoc(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state == AfterDrainReplacementStateValue()
    ensures LimitStreamConsistent(next)
    ensures next == AfterAddLowScoreDocStateValue()
  {
    var changed := HandleItem(state, DocChangeItem(0, NoState, HasState(DocState(5))));
    next := changed.state;
    assume {:axiom} changed.events == [MatchEvent(MatchPayload(0, NoState, HasState(DocState(5)), [], [1], [Eviction(1, 3)]))];
    assume {:axiom} next.store == map[0 := DocState(5), 2 := DocState(20), 3 := DocState(30)];
    assume {:axiom} 1 in next.queries.infos;
    assume {:axiom} next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2);
    assume {:axiom} next.queries.docs.entries == [Entry(5, 0), Entry(20, 2), Entry(30, 3)];
    assume {:axiom} GetDocsForQuery(next.queries, 1) == [0, 2];
    assume {:axiom} next.retrieval == RetrievalWorkerState(map[], [], 2, map[], [], 0, false);
    assert changed.events == [MatchEvent(MatchPayload(0, NoState, HasState(DocState(5)), [], [1], [Eviction(1, 3)]))];
    assert next.retrieval == RetrievalWorkerState(map[], [], 2, map[], [], 0, false);
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method RemoveOnlyQuery(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state == AfterAddLowScoreDocStateValue()
    ensures LimitStreamConsistent(next)
    ensures next == AfterRemoveOnlyQueryStateValue()
  {
    var removedQueries := TsLimitQueriesRuntime.RemoveQuery(state.queries, 1);
    assert !(1 in removedQueries.state.infos);
    var expected := SetQueries(state, removedQueries.state);
    var removedQuery := HandleItem(state, QueryRemoveItem(1));
    next := removedQuery.state;
    assert removedQuery == StreamStep(expected, []);
    assert removedQuery.events == [];
    assert !(1 in next.queries.infos);
    assert next.retrieval == RetrievalWorkerState(map[], [], 2, map[], [], 0, false);
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method Main() {
    var state := SeedInitialDocs();
    state := AddFirstQuery(state);
    state := RemoveFirstDocWhileRetrievalPending(state);
    state := DrainOverlappedRetrieval(state);
    state := AddLowScoreDoc(state);
    state := RemoveOnlyQuery(state);
    print "ts-limit-stream-smoke passed\n";
  }
}