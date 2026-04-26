include "CleanPendingLemmas.dfy"

module CleanPendingSmoke {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened CleanPendingRuntime

  method {:verify false} Main()
    decreases *
  {
    var registry := new PendingRegistry();

    registry.Register(10, 1);
    registry.Register(10, 2);
    registry.Register(11, 1);

    var pendingQueries10 := registry.PendingQueries(10);
    var pendingDocs1 := registry.PendingDocs(1);
    expect registry.state.docOrder == [10, 11];
    expect pendingQueries10 == [1, 2];
    expect pendingDocs1 == [10, 11];

    var cancelled := registry.Cancel(10, 2);
    var pendingQueries10AfterCancel := registry.PendingQueries(10);
    expect cancelled;
    expect pendingQueries10AfterCancel == [1];

    registry.ResolveDoc(11);
    var pendingDocs1AfterResolve := registry.PendingDocs(1);
    expect pendingDocs1AfterResolve == [10];

    registry.Register(12, 3);

    var store := map[10 := DocState(5), 12 := DocState(9)];
    var docs := registry.DrainGrouped(store);

    expect |docs| == 2;
    expect docs[0].docId == 10;
    expect docs[0].queries == [1];
    expect docs[1].docId == 12;
    expect docs[1].queries == [3];
    expect registry.state == EmptyPendingState();

    print "clean-pending-smoke passed\n";
  }
}