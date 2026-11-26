include "CleanLimitEngine.dfy"

module CleanLimitCrossTrace {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened CleanLimitEngine

  method PrintState(state: MaybeDocState) {
    match state
    case NoState => print "null";
    case HasState(value) => print value.scoreValue;
  }

  method PrintIds(ids: seq<int>) {
    print "[";
    var index := 0;
    while index < |ids|
      invariant 0 <= index <= |ids|
      decreases |ids| - index
    {
      if index > 0 { print ","; }
      print ids[index];
      index := index + 1;
    }
    print "]";
  }

  method PrintInput(item: StreamItem) {
    match item
    case SeedDocsItem(docs) => {
      print "{\"kind\":\"seed-docs\",\"docs\":[";
      var index := 0;
      while index < |docs|
        invariant 0 <= index <= |docs|
        decreases |docs| - index
      {
        if index > 0 { print ","; }
        print "{\"id\":", docs[index].id, ",\"score\":", docs[index].state.scoreValue, "}";
        index := index + 1;
      }
      print "]}";
    }
    case QueryAddItem(spec) => {
      print "{\"kind\":\"query-add\",\"minScore\":", spec.minScore, ",\"maxScore\":", spec.maxScore, ",\"limit\":", spec.limit, "}";
    }
    case QueryRemoveItem(id) => {
      print "{\"kind\":\"query-remove\",\"id\":", id, "}";
    }
    case DocChangeItem(id, oldState, newState) => {
      print "{\"kind\":\"doc-change\",\"id\":", id, ",\"old\":";
      PrintState(oldState);
      print ",\"new\":";
      PrintState(newState);
      print "}";
    }
  }

  method PrintEvents(events: seq<DownstreamEvent>) {
    print "[";
    var index := 0;
    while index < |events|
      invariant 0 <= index <= |events|
      decreases |events| - index
    {
      if index > 0 { print ","; }
      match events[index] {
      case MatchEvent(payload) => {
        print "{\"kind\":\"match\",\"docId\":", payload.docId, ",\"old\":";
        PrintState(payload.oldState);
        print ",\"new\":";
        PrintState(payload.newState);
        print ",\"matchesOld\":";
        PrintIds(payload.matchesOld);
        print ",\"matchesNew\":";
        PrintIds(payload.matchesNew);
        print ",\"evictions\":[";
        var eviction := 0;
        while eviction < |payload.evictions|
          invariant 0 <= eviction <= |payload.evictions|
          decreases |payload.evictions| - eviction
        {
          if eviction > 0 { print ","; }
          print "[", payload.evictions[eviction].queryId, ",", payload.evictions[eviction].docId, "]";
          eviction := eviction + 1;
        }
        print "]}";
      }
      case RetrievalEvent(docs) => {
        print "{\"kind\":\"retrieval\",\"docs\":[";
        var doc := 0;
        while doc < |docs|
          invariant 0 <= doc <= |docs|
          decreases |docs| - doc
        {
          if doc > 0 { print ","; }
          print "{\"docId\":", docs[doc].docId, ",\"score\":", docs[doc].state.scoreValue, ",\"queries\":";
          PrintIds(docs[doc].queries);
          print "}";
          doc := doc + 1;
        }
        print "]}";
      }
      }
      index := index + 1;
    }
    print "]";
  }

  method RunStep(engine: CleanEngine, item: StreamItem, trace: bool)
    requires engine.Ready()
    ensures engine.Ready()
    modifies engine
  {
    var events, queryId := engine.ProcessItem(item);
    if trace {
      print "{\"input\":";
      PrintInput(item);
      print ",\"queryId\":", queryId, ",\"events\":";
      PrintEvents(events);
      print "}\n";
    }
  }

  method CaptureStep(engine: CleanEngine, item: StreamItem, trace: bool, items: seq<StreamItem>) returns (next: seq<StreamItem>)
    requires engine.Ready()
    ensures engine.Ready()
    ensures next == items + [item]
    modifies engine
  {
    RunStep(engine, item, trace);
    next := items + [item];
  }

  method NextRandom(current: int) returns (next: int)
    requires current > 0
    ensures next > 0
  {
    next := (current * 48271) % 2147483647;
    if next <= 0 { next := next + 2147483647; }
  }

  method WorkloadMain(trace: bool) returns (items: seq<StreamItem>) {
    var engine := new CleanEngine();
    items := [];
    var random := 123;
    var seedDocs := new SeedDoc[800];
    var index := 0;
    while index < 800
      invariant 0 <= index <= 800
      invariant random > 0
      invariant engine.Ready()
    {
      random := NextRandom(random);
      seedDocs[index] := SeedDoc(index, DocState(random % 81));
      index := index + 1;
    }
    items := CaptureStep(engine, SeedDocsItem(seedDocs[..]), trace, items);

    index := 0;
    while index < 120
      invariant 0 <= index <= 120
      invariant random > 0
      invariant engine.Ready()
    {
      random := NextRandom(random);
      var width := 1 + random % 41;
      random := NextRandom(random);
      var minimum := random % 81;
      items := CaptureStep(engine, QueryAddItem(QuerySpec(minimum, minimum + width, 25)), trace, items);
      index := index + 1;
    }

    var nextDocId := 800;
    var tick := 0;
    while tick < 30
      invariant 0 <= tick <= 30
      invariant random > 0
      invariant engine.Ready()
    {
      var update := 0;
      while update < 35
        invariant 0 <= update <= 35
        invariant random > 0
        invariant engine.Ready()
      {
        if |engine.docIds| > 0 {
          random := NextRandom(random);
          var docId := engine.docIds[random % |engine.docIds|];
          random := NextRandom(random);
          if docId in engine.store {
            items := CaptureStep(engine, DocChangeItem(docId, HasState(engine.store[docId]), HasState(DocState(random % 81))), trace, items);
          }
        }
        update := update + 1;
      }

      var insert := 0;
      while insert < 8
        invariant 0 <= insert <= 8
        invariant random > 0
        invariant engine.Ready()
      {
        random := NextRandom(random);
        items := CaptureStep(engine, DocChangeItem(nextDocId, NoState, HasState(DocState(random % 81))), trace, items);
        nextDocId := nextDocId + 1;
        insert := insert + 1;
      }

      var delete := 0;
      while delete < 8
        invariant 0 <= delete <= 8
        invariant random > 0
        invariant engine.Ready()
      {
        if |engine.docIds| > 0 {
          random := NextRandom(random);
          var docId := engine.docIds[random % |engine.docIds|];
          if docId in engine.store {
            items := CaptureStep(engine, DocChangeItem(docId, HasState(engine.store[docId]), NoState), trace, items);
          }
        }
        delete := delete + 1;
      }
      tick := tick + 1;
    }
  }

  method Main(args: seq<string>) {
    if |args| > 0 && args[|args| - 1] == "workload" {
      var ignored := WorkloadMain(true);
      return;
    }
    if |args| > 0 && args[|args| - 1] == "benchmark" {
      var items := WorkloadMain(false);
      var engine := new CleanEngine();
      print "benchmark-start\n";
      var index := 0;
      while index < |items|
        invariant 0 <= index <= |items|
        invariant engine.Ready()
      {
        RunStep(engine, items[index], false);
        index := index + 1;
      }
      print "benchmark-end\n";
      return;
    }
    var engine := new CleanEngine();
    RunStep(engine, SeedDocsItem([SeedDoc(1, DocState(10)), SeedDoc(2, DocState(20)), SeedDoc(3, DocState(30))]), true);
    RunStep(engine, QueryAddItem(QuerySpec(0, 100, 2)), true);
    RunStep(engine, QueryAddItem(QuerySpec(5, 25, 1)), true);
    RunStep(engine, DocChangeItem(1, HasState(DocState(10)), HasState(DocState(35))), true);
    RunStep(engine, DocChangeItem(2, HasState(DocState(20)), HasState(DocState(20))), true);
    RunStep(engine, DocChangeItem(3, HasState(DocState(30)), NoState), true);
    RunStep(engine, DocChangeItem(4, NoState, HasState(DocState(5))), true);
    RunStep(engine, QueryRemoveItem(1), true);
    RunStep(engine, DocChangeItem(4, HasState(DocState(5)), NoState), true);
    RunStep(engine, QueryRemoveItem(2), true);
    RunStep(engine, DocChangeItem(2, HasState(DocState(20)), HasState(DocState(20))), true);
    RunStep(engine, DocChangeItem(0, NoState, HasState(DocState(5))), true);
    RunStep(engine, QueryAddItem(QuerySpec(0, 100, 1)), true);
    RunStep(engine, DocChangeItem(1, HasState(DocState(35)), HasState(DocState(3))), true);
    RunStep(engine, DocChangeItem(1, HasState(DocState(3)), NoState), true);
  }
}