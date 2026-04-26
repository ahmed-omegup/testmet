include "TsRetrievalLemmas.dfy"

module TsRetrievalSmoke {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsRetrievalRuntime

  method Main() {
    var state := EmptyWorkerState();

    expect WorkerConsistent(state);
    expect !ShouldExit(state);

    state := Register(state, 10, 1);
    state := Register(state, 10, 2);
    state := Register(state, 11, 1);
    state := Register(state, 10, 1);

    expect state.pendingOrder == [10, 11];
    expect state.pendingBatch[10] == [1, 2];
    expect state.pendingBatch[11] == [1];
    expect HasPendingWork(state);

    var cancelledPending := Cancel(state, 10, 2);
    state := cancelledPending.state;
    expect cancelledPending.changed;
    expect state.pendingBatch[10] == [1];

    state := BeginCycle(state);
    expect state.pendingOrder == [];
    expect state.processingOrder == [10, 11];
    expect !CanRegister(state, 10, 1);

    state := Register(state, 12, 3);
    expect state.pendingOrder == [12];
    expect state.pendingBatch[12] == [3];

    var store := map[10 := DocState(5), 11 := DocState(7), 12 := DocState(9)];
    var docs := BuildPayload(state, store);
    expect |docs| == 2;
    expect docs[0] == RetrievalDoc(10, DocState(5), [1]);
    expect docs[1] == RetrievalDoc(11, DocState(7), [1]);

    var resolved := ResolveDoc(state, 10);
    state := resolved.state;
    expect resolved.changed;
    expect !(10 in state.processingBatch);

    var cancelledProcessing := Cancel(state, 11, 1);
    state := cancelledProcessing.state;
    expect cancelledProcessing.changed;
    expect state.processingOrder == [];

    state := FinishCycle(state);
    expect state.processingBatch == map[];

    state := Stop(state);
    expect !ShouldExit(state);

    state := BeginCycle(state);
    var docs2 := BuildPayload(state, store);
    expect |docs2| == 1;
    expect docs2[0] == RetrievalDoc(12, DocState(9), [3]);

    state := ResolveDoc(state, 12).state;
    state := FinishCycle(state);
    expect ShouldExit(state);

    print "ts-retrieval-smoke passed\n";
  }
}