include "CleanLimitEngine.dfy"

module CleanLimitSmoke {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened CleanLimitEngine
  import opened CleanPendingRuntime

  method Main()
    decreases *
  {
    var engine := new CleanEngine();

    var ignoredEvents, ignoredQueryId := engine.ProcessItemDeferred(SeedDocsItem([
      SeedDoc(1, DocState(10)),
      SeedDoc(2, DocState(20)),
      SeedDoc(3, DocState(30))
    ]));

    var addEvents, queryId := engine.ProcessItemDeferred(QueryAddItem(QuerySpec(0, 100, 2)));
    expect |addEvents| == 0;
    expect queryId == 1;

    var addRetrievals := engine.DrainPendingRetrievalsGrouped();
    expect |addRetrievals| == 1;
    match addRetrievals[0]
    case MatchEvent(payload) => {
      expect false;
    }
    case RetrievalEvent(docs) => {
      expect |docs| == 2;
      expect docs[0].docId == 1;
      expect docs[0].queries == [1];
      expect docs[1].docId == 2;
      expect docs[1].queries == [1];
    }

    var updateEvents, ignoredQueryId2 := engine.ProcessItemDeferred(DocChangeItem(1, HasState(DocState(10)), HasState(DocState(40))));
    expect |updateEvents| == 1;
    match updateEvents[0]
    case MatchEvent(payload) => {
      expect payload.matchesOld == [1];
      expect payload.matchesNew == [];
    }
    case RetrievalEvent(docs) => {
      expect false;
    }

    var updateRetrievals := engine.DrainPendingRetrievalsGrouped();
    match updateRetrievals[0]
    case MatchEvent(payload) => {
      expect false;
    }
    case RetrievalEvent(docs) => {
      expect |docs| == 1;
      expect docs[0].docId == 3;
      expect docs[0].queries == [1];
    }

    var insertEvents, ignoredQueryId3 := engine.ProcessItemDeferred(DocChangeItem(0, NoState, HasState(DocState(5))));
    expect |insertEvents| == 1;
    match insertEvents[0]
    case MatchEvent(payload) => {
      expect payload.matchesOld == [];
      expect payload.matchesNew == [1];
      expect |payload.evictions| == 1;
      expect payload.evictions[0] == Eviction(1, 3);
    }
    case RetrievalEvent(docs) => {
      expect false;
    }

    var visible := engine.QueryVisible(1);
    expect visible == [0, 2];
    expect engine.pendingState == EmptyPendingState();

    print "clean-limit-smoke passed\n";
  }
}