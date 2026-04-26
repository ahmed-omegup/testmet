include "TsLimitStreamLemmas.dfy"

module TsLimitStreamSmoke {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsLimitStreamRuntime

  method Main() {
    var state := EmptyLimitStreamState();
    expect LimitStreamConsistent(state);

    var seeded := HandleItem(state, SeedDocsItem([SeedDoc(1, DocState(10)), SeedDoc(2, DocState(20)), SeedDoc(3, DocState(30))]));
    state := seeded.state;
    expect seeded.events == [];
    expect state.store == map[1 := DocState(10), 2 := DocState(20), 3 := DocState(30)];
    expect state.queries.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)];

    var added := HandleItem(state, QueryAddItem(QuerySpec(0, 100, 2)));
    state := added.state;
    expect added.events == [];
    expect 1 in state.queries.infos;
    expect state.queries.infos[1].currentMatches == 2;
    expect state.retrieval.pendingOrder == [1, 2];

    var retrieval := DrainRetrievalCycle(state);
    state := retrieval.state;
    expect retrieval.events == [RetrievalEvent([RetrievalDoc(1, DocState(10), [1]), RetrievalDoc(2, DocState(20), [1])])];
    expect state.retrieval.pendingOrder == [];

    var removed := HandleItem(state, DocChangeItem(1, HasState(DocState(10)), NoState));
    state := removed.state;
    expect removed.events == [MatchEvent(MatchPayload(1, HasState(DocState(10)), NoState, [1], [], []))];
    expect state.queries.infos[1].currentMatches == 2;
    expect state.queries.pendingByQuery[1] == [3];
    expect state.retrieval.pendingOrder == [3];

    retrieval := DrainRetrievalCycle(state);
    state := retrieval.state;
    expect retrieval.events == [RetrievalEvent([RetrievalDoc(3, DocState(30), [1])])];
    expect !(1 in state.queries.pendingByQuery);

    var changed := HandleItem(state, DocChangeItem(0, NoState, HasState(DocState(5))));
    state := changed.state;
    expect changed.events == [MatchEvent(MatchPayload(0, NoState, HasState(DocState(5)), [], [1], [Eviction(1, 3)]))];
    expect state.retrieval.pendingOrder == [];
    expect !(1 in state.queries.pendingByQuery);

    var removedQuery := HandleItem(state, QueryRemoveItem(1));
    state := removedQuery.state;
    expect removedQuery.events == [];
    expect !(1 in state.queries.infos);

    print "ts-limit-stream-smoke passed\n";
  }
}