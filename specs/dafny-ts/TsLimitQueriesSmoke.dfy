include "TsLimitQueriesLemmas.dfy"

module TsLimitQueriesSmoke {
  import opened DocsIndexModel
  import opened TsLimitQueriesRuntime

  method Main() {
    var state := EmptyLimitQueriesState();
    expect LimitQueriesConsistent(state);

    state := AddDocument(state, 10, 1).state;
    state := AddDocument(state, 20, 2).state;
    state := AddDocument(state, 30, 3).state;
    expect state.docs.entries == [Entry(10, 1), Entry(20, 2), Entry(30, 3)];

    var added := TsLimitQueriesRuntime.AddQuery(state, 0, 2, 100);
    state := added.state;
    expect added.queryId == 1;
    expect state.infos[1] == QueryInfo(1, 0, 2, 100, 2);
    expect GetDocsForQuery(state, 1) == [1, 2];

    var removed := RemoveDocument(state, 10, 1);
    state := removed.state;
    expect removed.removed == [1];
    expect state.infos[1].currentMatches == 1;

    var gap := FillGap(state, 1);
    state := gap.state;
    expect gap.doc == SomeDoc(3);
    expect state.infos[1].currentMatches == 2;

    var cancelled := CancelPendingForQuery(state, 3, 1);
    state := cancelled.state;
    expect !cancelled.changed;
    expect state.infos[1].currentMatches == 2;

    gap := FillGap(state, 1);
    state := gap.state;
    expect gap.doc == NoDoc;
    state := ResolvePendingForDoc(state, 3);
    expect state.infos[1].currentMatches == 2;

    var addedDoc := AddDocument(state, 5, 0);
    state := addedDoc.state;
    expect addedDoc.matched == [1];
    expect addedDoc.blocked == [1];
    expect state.infos[1].currentMatches == 2;

    expect PickOverflowDoc(state, 1) == SomeDoc(3);

    var removedQuery := TsLimitQueriesRuntime.RemoveQuery(state, 1);
    state := removedQuery.state;
    expect removedQuery.changed;
    expect !(1 in state.infos);
    expect !(1 in state.baseScores);

    print "ts-limit-queries-smoke passed\n";
  }
}