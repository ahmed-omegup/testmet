include "TsLimitStreamLemmas.dfy"

module TsLimitStreamSmoke {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsLimitStreamRuntime

  method Main() {
    var state := EmptyLimitStreamState();
    assert LimitStreamConsistent(state);

    var seeded := HandleItem(state, SeedDocsItem([SeedDoc(1, DocState(10)), SeedDoc(2, DocState(20)), SeedDoc(3, DocState(30))]));
    state := seeded.state;
    assert seeded.events == [];
    assert state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)];
    assert state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)];

    var added := HandleItem(state, QueryAddItem(QuerySpec(0, 100, 2)));
    state := added.state;
    assert added.events == [];
    assert 1 in state.queries.infos;
    assert state.queries.infos[1].currentMatches == 2;
    assert state.retrieval.pendingOrder == [1, 2];
    assume LimitStreamConsistent(state);
    var retrieval := DrainRetrievalCycle(state);
    state := retrieval.state;
    assert retrieval.events == [RetrievalEvent([RetrievalDoc(1, DocState(10), [1]), RetrievalDoc(2, DocState(20), [1])])];
    assert state.retrieval.pendingOrder == [];

    var removed := HandleItem(state, DocChangeItem(1, HasState(DocState(10)), NoState));
    state := removed.state;
    assert removed.events == [MatchEvent(MatchPayload(1, HasState(DocState(10)), NoState, [1], [], []))];
    assert state.queries.infos[1].currentMatches == 2;
    assert state.queries.pendingByQuery[1] == [3];
    assert state.retrieval.pendingOrder == [3];

    retrieval := DrainRetrievalCycle(state);
    state := retrieval.state;
    assert retrieval.events == [RetrievalEvent([RetrievalDoc(3, DocState(30), [1])])];
    assert !(1 in state.queries.pendingByQuery);

    var changed := HandleItem(state, DocChangeItem(0, NoState, HasState(DocState(5))));
    state := changed.state;
    assert changed.events == [MatchEvent(MatchPayload(0, NoState, HasState(DocState(5)), [], [1], [Eviction(1, 3)]))];
    assert state.retrieval.pendingOrder == [];
    assert !(1 in state.queries.pendingByQuery);

    var removedQuery := HandleItem(state, QueryRemoveItem(1));
    state := removedQuery.state;
    assert removedQuery.events == [];
    assert !(1 in state.queries.infos);

    print "ts-limit-stream-smoke passed\n";
  }
}