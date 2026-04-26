include "TsQueriesLemmas.dfy"

module TsQueriesSmoke {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsQueriesRuntime

  method Main() {
    var state := EmptyQueriesState();
    expect QueriesConsistent(state);
    expect AccumulatedAddAtKey(state, 10) == 0;

    state := RangeAddKeysGreaterThan(state, 7, 2);
    expect AccumulatedAddAtKey(state, 5) == 0;
    expect AccumulatedAddAtKey(state, 8) == 2;
    expect AccumulatedAddAtKey(state, 10) == 2;

    state := Insert(state, 10, 1, 8, 20);
    state := Insert(state, 5, 2, 3, 15);
    state := Insert(state, 10, 3, 4, 25);

    expect QueriesConsistent(state);
  expect |state.entries| == 3;
    expect state.entries[0] == QueryEntry(2, 5, 3, 15);
    expect state.entries[1] == QueryEntry(3, 10, 2, 25);
    expect state.entries[2] == QueryEntry(1, 10, 6, 20);
    expect EffectiveScore(state, state.entries[1]) == 4;
    expect EffectiveScore(state, state.entries[2]) == 8;

    var cover12cutoff4 := CollectForValue(state, 12, 4);
    expect cover12cutoff4 == [1];

    var cover10cutoff2 := CollectForValue(state, 10, 2);
    expect cover10cutoff2 == [2, 3, 1];

    state := RangeAddKeysGreaterThan(state, 9, 1);
    expect AccumulatedAddAtKey(state, 10) == 3;
    expect CollectForValue(state, 10, 4) == [3, 1];

    state := Remove(state, 10, 1, 6, 20);
    expect QueriesConsistent(state);
    expect !ContainsQueryEntryId(state.entries, 1);
    expect CollectForValue(state, 12, 4) == [3];

    print "ts-queries-smoke passed\n";
  }
}