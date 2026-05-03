include "TsLimitStreamPerfSurface.dfy"

module TsLimitStreamPerfParity {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsLimitStreamPerfSurface
  import opened TsLimitStreamRuntime

  method Main()
    decreases *
  {
    var engine := new PerfEngine();
    var state := EmptyLimitStreamState();

    var seedItem := SeedDocsItem([SeedDoc(1, DocState(10)), SeedDoc(2, DocState(20)), SeedDoc(3, DocState(30))]);
    var step := HandleItem(state, seedItem);
    state := step.state;
    var events := engine.Apply(seedItem);
    expect events == step.events;
    expect engine.state == state;

    var addItem := QueryAddItem(QuerySpec(0, 100, 2));
    step := HandleItem(state, addItem);
    state := step.state;
    events := engine.Apply(addItem);
    expect events == step.events;
    expect engine.state == state;

    var removeItem := DocChangeItem(1, HasState(DocState(10)), NoState);
    step := HandleItem(state, removeItem);
    state := step.state;
    events := engine.Apply(removeItem);
    expect events == step.events;
    expect engine.state == state;

    var drained := DrainRetrievalCycle(state);
    state := drained.state;
    events := engine.DrainOnce();
    expect events == drained.events;
    expect engine.state == state;

    var lowItem := DocChangeItem(0, NoState, HasState(DocState(5)));
    step := HandleItem(state, lowItem);
    state := step.state;
    events := engine.Apply(lowItem);
    expect events == step.events;
    expect engine.state == state;

    var removeQueryItem := QueryRemoveItem(1);
    step := HandleItem(state, removeQueryItem);
    state := step.state;
    events := engine.Apply(removeQueryItem);
    expect events == step.events;
    expect engine.state == state;

    expect engine.summary == StreamSummary(5, 2, 1, 1, 2);
    print "ts-limit-stream-perf-parity passed\n";
  }
}