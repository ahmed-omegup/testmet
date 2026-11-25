include "TsDocsLemmas.dfy"

module TsDocsSmoke {
  import opened DocsIndexModel
  import opened TsDocsRuntime

  method Main() {
    var state := EmptyDocsState();
    expect DocsConsistent(state);
    expect RankDoc(state, 10, NoDoc) == 0;
    expect CountAtMostDoc(state, 10) == 0;
    expect GetAtRankDoc(state, 0) == Missing;

    state := AddDoc(state, 20, 2);
    state := AddDoc(state, 10, 5);
    state := AddDoc(state, 10, 3);
    state := AddDoc(state, 10, 3);
    state := AddDoc(state, 30, 1);

    expect DocsConsistent(state);
    expect state.entries == [Entry(10, 3), Entry(10, 5), Entry(20, 2), Entry(30, 1)];
    expect RankDoc(state, 10, NoDoc) == 0;
    expect RankDoc(state, 10, SomeDoc(4)) == 1;
    expect RankDoc(state, 10, SomeDoc(5)) == 1;
    expect RankDoc(state, 20, NoDoc) == 2;
    expect CountAtMostDoc(state, 9) == 0;
    expect CountAtMostDoc(state, 10) == 2;
    expect CountAtMostDoc(state, 25) == 3;
    expect CountAtMostDoc(state, 30) == 4;

    expect GetAtRankDoc(state, 0) == Found(10, 3, 0);
    expect GetAtRankDoc(state, 1) == Found(10, 5, 1);
    expect GetAtRankDoc(state, 2) == Found(20, 2, 0);
    expect GetAtRankDoc(state, 4) == Missing;

    expect CollectRangeDocs(state, 10, 20, 10) == [3, 5, 2];
    expect CollectRangeDocs(state, 11, 30, 2) == [2, 1];
    expect CollectRangeDocs(state, 31, 40, 5) == [];

    state := RemoveDoc(state, 10, 5);
    expect state.entries == [Entry(10, 3), Entry(20, 2), Entry(30, 1)];

    state := RemoveDoc(state, 20, 999);
    expect state.entries == [Entry(10, 3), Entry(20, 2), Entry(30, 1)];

    state := RemoveDoc(state, 10, 3);
    state := RemoveDoc(state, 20, 2);
    state := RemoveDoc(state, 30, 1);
    expect state.entries == [];
    expect GetAtRankDoc(state, 0) == Missing;

    print "ts-docs-smoke passed\n";
  }
}