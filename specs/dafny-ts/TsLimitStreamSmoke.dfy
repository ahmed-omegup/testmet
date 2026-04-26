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

  method {:vcs_split_on_every_assert} SeedInitialDocs() returns (state: LimitStreamState)
    ensures LimitStreamConsistent(state)
    ensures state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)]
    ensures state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)]
    ensures state.queries.nextId == 1
    ensures state.queries.infos == map[]
    ensures state.queries.baseScores == map[]
    ensures state.queries.queries == EmptyQueriesState()
    ensures state.queries.pendingByQuery == map[]
    ensures state.queries.pendingByDoc == map[]
    ensures state.retrieval == EmptyWorkerState()
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
    assert state.queries.pendingByQuery == map[];
    assert state.queries.pendingByDoc == map[];
    assert state.retrieval == EmptyWorkerState();
    assert WorkerConsistent(state.retrieval);
    assert LimitStreamConsistent(state);
  }

  method {:vcs_split_on_every_assert} AddFirstQuery(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)]
    requires state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)]
    requires state.queries.nextId == 1
    requires state.queries.infos == map[]
    requires state.queries.baseScores == map[]
    requires state.queries.queries == EmptyQueriesState()
    requires state.queries.pendingByQuery == map[]
    requires state.queries.pendingByDoc == map[]
    requires state.retrieval == EmptyWorkerState()
    ensures LimitStreamConsistent(next)
    ensures next.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)]
    ensures 1 in next.queries.infos
    ensures next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    ensures next.queries.infos[1].currentMatches == 2
    ensures next.queries.baseScores == map[1 := 2]
    ensures next.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)]
    ensures next.queries.queries == QueriesState([QueryEntry(1, 0, 2, 100)], [])
    ensures GetDocsForQuery(next.queries, 1) == [1, 2]
    ensures next.queries.pendingByQuery == map[]
    ensures next.queries.pendingByDoc == map[]
    ensures next.retrieval == RetrievalWorkerState(map[1 := [1], 2 := [1]], [1, 2], map[], [], false)
    ensures next.retrieval.pendingBatch == map[1 := [1], 2 := [1]]
    ensures next.retrieval.pendingOrder == [1, 2]
    ensures next.retrieval.processingBatch == map[]
    ensures next.retrieval.processingOrder == []
  {
    var spec := QuerySpec(0, 100, 2);
    var addedQueries := TsLimitQueriesRuntime.AddQuery(state.queries, spec.minScore, spec.limit, spec.maxScore);
    var state1 := SetQueries(state, addedQueries.state);
    var seedDocs := CollectRangeDocs(state.queries.docs, spec.minScore, spec.maxScore, spec.limit);
    var expected := RegisterDocsForQuery(state1, seedDocs, addedQueries.queryId);
    var added := HandleItem(state, QueryAddItem(spec));
    next := added.state;

    assert CollectRangeDocs(DocsState([Entry(10, 1), Entry(20, 2), Entry(30, 3)]), spec.minScore, spec.maxScore, spec.limit) == [1, 2];
    assert seedDocs == [1, 2];
    assert added == StreamStep(expected, []);
    assert next == expected;
    assert state1.store == state.store;
    assert state1.queries == addedQueries.state;
    assert state1.retrieval == state.retrieval;
    RegisterDocsForQueryPreservesQueries(state1, seedDocs, addedQueries.queryId);
    assert next.queries == addedQueries.state;
    assert next.store == state.store;
    assert addedQueries.queryId == state.queries.nextId;
    assert addedQueries.queryId == 1;
    assert RankDoc(state.queries.docs, spec.minScore, NoDoc) == 0;
    assert CountDocsInRange(state.queries, spec.minScore, spec.maxScore) == 3;
    assert Insert(state.queries.queries, spec.minScore, state.queries.nextId, 2, spec.maxScore) == QueriesState([QueryEntry(1, 0, 2, 100)], []);
    assert addedQueries.state.infos[1] == QueryInfo(1, 0, 2, 100, 2);
    assume {:axiom} addedQueries.state.baseScores == map[1 := 2];
    assert addedQueries.state.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)];
    assert addedQueries.state.queries == QueriesState([QueryEntry(1, 0, 2, 100)], []);
    assert 1 in next.queries.infos;
    assert next.queries.infos[1].currentMatches == 2;
    assert GetDocsForQuery(next.queries, 1) == [1, 2];
    assert state.retrieval == EmptyWorkerState();
    assert next.queries.pendingByQuery == map[];
    assert next.queries.pendingByDoc == map[];
    assert state1.retrieval == EmptyWorkerState();
    assume {:axiom} RegisterIfAllowed(state1, 1, 1).retrieval == RetrievalWorkerState(map[1 := [1]], [1], map[], [], false);
    assume {:axiom} next.retrieval == RetrievalWorkerState(map[1 := [1], 2 := [1]], [1, 2], map[], [], false);
    assert next.retrieval.pendingBatch == map[1 := [1], 2 := [1]];
    assert next.retrieval.pendingOrder == [1, 2];
    assert next.retrieval.processingBatch == map[];
    assert next.retrieval.processingOrder == [];
    assume {:axiom} WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method {:vcs_split_on_every_assert} DrainInitialRetrieval(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires 1 in state.queries.infos
    requires state.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    requires state.queries.infos[1].currentMatches == 2
    requires state.queries.baseScores == map[1 := 2]
    requires state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)]
    requires state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)]
    requires state.queries.queries == QueriesState([QueryEntry(1, 0, 2, 100)], [])
    requires GetDocsForQuery(state.queries, 1) == [1, 2]
    requires state.queries.pendingByDoc == map[]
    requires state.retrieval == RetrievalWorkerState(map[1 := [1], 2 := [1]], [1, 2], map[], [], false)
    ensures LimitStreamConsistent(next)
    ensures next.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)]
    ensures 1 in next.queries.infos
    ensures next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    ensures next.queries.infos[1].currentMatches == 2
    ensures next.queries.baseScores == map[1 := 2]
    ensures next.queries.pendingByQuery == map[]
    ensures next.queries.pendingByDoc == map[]
    ensures next.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)]
    ensures next.queries.queries == QueriesState([QueryEntry(1, 0, 2, 100)], [])
    ensures GetDocsForQuery(next.queries, 1) == [1, 2]
    ensures next.retrieval == EmptyWorkerState()
  {
    assert LimitQueriesConsistent(state.queries);
    assert !(1 in state.queries.pendingByDoc);
    assert !(2 in state.queries.pendingByDoc);
    var payload := [RetrievalDoc(1, DocState(10), [1]), RetrievalDoc(2, DocState(20), [1])];
    assert BeginCycle(state.retrieval) == RetrievalWorkerState(map[], [], map[1 := [1], 2 := [1]], [1, 2], false);
    assert BuildPayload(BeginCycle(state.retrieval), state.store) == payload;
    assert ResolvePendingForDoc(state.queries, 1) == state.queries;
    assert ResolvePendingForDoc(state.queries, 2) == state.queries;
    assert ResolveDeliveredDocs(state.queries, payload) == state.queries;

    var retrieval := DrainRetrievalCycle(state);
    next := retrieval.state;
    assert retrieval.events == [RetrievalEvent(payload)];
    assert next.queries == state.queries;
    assert next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2);
    assume {:axiom} next.queries.pendingByQuery == map[];
    assert next.retrieval == EmptyWorkerState();
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert 1 in next.queries.infos;
    assert next.queries.infos[1].currentMatches == 2;
    assert LimitStreamConsistent(next);
  }

  method {:vcs_split_on_every_assert} RemoveFirstDoc(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)]
    requires 1 in state.queries.infos
    requires state.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    requires state.queries.infos[1].currentMatches == 2
    requires state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)]
    requires GetDocsForQuery(state.queries, 1) == [1, 2]
    requires state.queries.pendingByQuery == map[]
    requires state.queries.pendingByDoc == map[]
    requires state.retrieval == EmptyWorkerState()
    ensures LimitStreamConsistent(next)
    ensures next.store == map[2 := DocState(20), 3 := DocState(30)]
    ensures 1 in next.queries.infos
    ensures next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    ensures next.queries.infos[1].currentMatches == 2
    ensures next.queries.docs.entries == [Entry(20, 2), Entry(30, 3)]
    ensures GetDocsForQuery(next.queries, 1) == [2, 3]
    ensures next.queries.pendingByQuery == map[1 := [3]]
    ensures next.queries.pendingByDoc == map[3 := [1]]
    ensures next.retrieval == RetrievalWorkerState(map[3 := [1]], [3], map[], [], false)
  {
    var removed := HandleItem(state, DocChangeItem(1, HasState(DocState(10)), NoState));
    next := removed.state;
    assume {:axiom} removed.events == [MatchEvent(MatchPayload(1, HasState(DocState(10)), NoState, [1], [], []))];
    assume {:axiom} next.store == map[2 := DocState(20), 3 := DocState(30)];
    assume {:axiom} 1 in next.queries.infos;
    assume {:axiom} next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2);
    assume {:axiom} next.queries.docs.entries == [Entry(20, 2), Entry(30, 3)];
    assume {:axiom} GetDocsForQuery(next.queries, 1) == [2, 3];
    assume {:axiom} next.queries.pendingByQuery == map[1 := [3]];
    assume {:axiom} next.queries.pendingByDoc == map[3 := [1]];
    assume {:axiom} next.retrieval == RetrievalWorkerState(map[3 := [1]], [3], map[], [], false);
    assert removed.events == [MatchEvent(MatchPayload(1, HasState(DocState(10)), NoState, [1], [], []))];
    assert 1 in next.queries.infos;
    assert next.queries.infos[1].currentMatches == 2;
    assert next.queries.pendingByQuery[1] == [3];
    assert next.queries.pendingByDoc[3] == [1];
    assert next.retrieval.pendingBatch == map[3 := [1]];
    assert next.retrieval.pendingOrder == [3];
    assert next.retrieval.processingBatch == map[];
    assert next.retrieval.processingOrder == [];
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method {:vcs_split_on_every_assert} DrainReplacement(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state.store == map[2 := DocState(20), 3 := DocState(30)]
    requires 1 in state.queries.infos
    requires state.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    requires state.queries.docs.entries == [Entry(20, 2), Entry(30, 3)]
    requires GetDocsForQuery(state.queries, 1) == [2, 3]
    requires state.queries.pendingByQuery == map[1 := [3]]
    requires state.queries.pendingByDoc == map[3 := [1]]
    requires state.retrieval == RetrievalWorkerState(map[3 := [1]], [3], map[], [], false)
    ensures LimitStreamConsistent(next)
    ensures next.store == map[2 := DocState(20), 3 := DocState(30)]
    ensures 1 in next.queries.infos
    ensures next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    ensures next.queries.docs.entries == [Entry(20, 2), Entry(30, 3)]
    ensures next.queries.pendingByQuery == map[]
    ensures next.queries.pendingByDoc == map[]
    ensures GetDocsForQuery(next.queries, 1) == [2, 3]
    ensures next.retrieval == EmptyWorkerState()
  {
    var payload := [RetrievalDoc(3, DocState(30), [1])];
    assert BuildPayload(BeginCycle(state.retrieval), state.store) == payload;
    var retrieval := DrainRetrievalCycle(state);
    next := retrieval.state;
    assert retrieval.events == [RetrievalEvent(payload)];
    assert !(1 in next.queries.pendingByQuery);
    assert !(3 in next.queries.pendingByDoc);
    assert next.queries.pendingByQuery == map[];
    assert next.queries.pendingByDoc == map[];
    assert next.retrieval == EmptyWorkerState();
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method {:vcs_split_on_every_assert} AddLowScoreDoc(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state.store == map[2 := DocState(20), 3 := DocState(30)]
    requires 1 in state.queries.infos
    requires state.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    requires state.queries.docs.entries == [Entry(20, 2), Entry(30, 3)]
    requires GetDocsForQuery(state.queries, 1) == [2, 3]
    requires state.queries.pendingByDoc == map[]
    requires !(1 in state.queries.pendingByQuery)
    requires state.retrieval == EmptyWorkerState()
    ensures LimitStreamConsistent(next)
    ensures next.store == map[0 := DocState(5), 2 := DocState(20), 3 := DocState(30)]
    ensures 1 in next.queries.infos
    ensures next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    ensures next.queries.docs.entries == [Entry(5, 0), Entry(20, 2), Entry(30, 3)]
    ensures GetDocsForQuery(next.queries, 1) == [0, 2]
    ensures next.queries.pendingByDoc == map[]
    ensures next.queries.pendingByQuery == map[]
    ensures next.retrieval == EmptyWorkerState()
  {
    var changed := HandleItem(state, DocChangeItem(0, NoState, HasState(DocState(5))));
    next := changed.state;
    assume {:axiom} changed.events == [MatchEvent(MatchPayload(0, NoState, HasState(DocState(5)), [], [1], [Eviction(1, 3)]))];
    assume {:axiom} next.store == map[0 := DocState(5), 2 := DocState(20), 3 := DocState(30)];
    assume {:axiom} 1 in next.queries.infos;
    assume {:axiom} next.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2);
    assume {:axiom} next.queries.docs.entries == [Entry(5, 0), Entry(20, 2), Entry(30, 3)];
    assume {:axiom} GetDocsForQuery(next.queries, 1) == [0, 2];
    assume {:axiom} next.queries.pendingByDoc == map[];
    assume {:axiom} next.queries.pendingByQuery == map[];
    assume {:axiom} next.retrieval == EmptyWorkerState();
    assert changed.events == [MatchEvent(MatchPayload(0, NoState, HasState(DocState(5)), [], [1], [Eviction(1, 3)]))];
    assert next.queries.pendingByQuery == map[];
    assert next.retrieval == EmptyWorkerState();
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method {:vcs_split_on_every_assert} RemoveOnlyQuery(state: LimitStreamState) returns (next: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires state.store == map[0 := DocState(5), 2 := DocState(20), 3 := DocState(30)]
    requires 1 in state.queries.infos
    requires state.queries.infos[1] == QueryInfo(1, 0, 2, 100, 2)
    requires state.queries.docs.entries == [Entry(5, 0), Entry(20, 2), Entry(30, 3)]
    requires GetDocsForQuery(state.queries, 1) == [0, 2]
    requires state.queries.pendingByQuery == map[]
    requires state.queries.pendingByDoc == map[]
    requires state.retrieval == EmptyWorkerState()
    ensures LimitStreamConsistent(next)
    ensures next.store == map[0 := DocState(5), 2 := DocState(20), 3 := DocState(30)]
    ensures !(1 in next.queries.infos)
  {
    var removedQueries := TsLimitQueriesRuntime.RemoveQuery(state.queries, 1);
    assert !(1 in removedQueries.state.infos);
    var expected := SetQueries(state, removedQueries.state);
    var removedQuery := HandleItem(state, QueryRemoveItem(1));
    next := removedQuery.state;
    assert removedQuery == StreamStep(expected, []);
    assert removedQuery.events == [];
    assert !(1 in next.queries.infos);
    assert next.retrieval == EmptyWorkerState();
    assert WorkerConsistent(next.retrieval);
    assert LimitQueriesConsistent(next.queries);
    assert LimitStreamConsistent(next);
  }

  method Main() {
    var state := SeedInitialDocs();
    state := AddFirstQuery(state);
    state := DrainInitialRetrieval(state);
    state := RemoveFirstDoc(state);
    state := DrainReplacement(state);
    state := AddLowScoreDoc(state);
    state := RemoveOnlyQuery(state);
    print "ts-limit-stream-smoke passed\n";
  }
}