include "CleanLimitEngine.dfy"

module CleanLimitPerf400k {
  import opened DocsIndexTreap
  import opened ThunderDbStack
  import opened CleanLimitEngine

  const Modulus: int := 2147483647
  const Multiplier: int := 48271

  function NextState(state: int): int {
    var next := (state * Multiplier) % Modulus;
    if next <= 0 then next + Modulus else next
  }

  method NextRand(state: int) returns (nextState: int, value: int)
    requires state > 0
    ensures nextState > 0
    ensures value == nextState
  {
    nextState := NextState(state);
    value := nextState;
  }

  method Main()
    decreases *
  {
    var documents: nat := 400000;
    var customers: nat := 10000;
    var ticks: nat := 5;
    var updatesPerTick: nat := 70000;
    var insertsPerTick: nat := 0;
    var deletesPerTick: nat := 0;
    var queryLimit: nat := 50;
    var density: nat := 10;
    var range := documents / density + 1;

    var engine: CleanEngine := new CleanEngine();
    var summary := SummaryZero();
    var rng := 42;

    var seedDocs := new SeedDoc[documents];
    var i := 0;
    while i < documents
      invariant 0 <= i <= documents
      invariant rng > 0
      invariant engine.Ready()
      decreases documents - i
    {
      var nextRng, scoreSeed := NextRand(rng);
      rng := nextRng;
      seedDocs[i] := SeedDoc(i, DocState(scoreSeed % range));
      i := i + 1;
      if i % 100000 == 0 {
        print "[perf] seeded ";
        print i;
        print " documents\n";
      }
    }

    print "[debug] starting document seeding into engine: ";
    print documents;
    print " docs\n";
    var seedEvents, ignoredSeedQueryId := engine.ProcessItem(SeedDocsItem(seedDocs[..]));
    summary := UpdateSummary(summary, seedEvents);
    print "[debug] engine seeding complete: docs=";
    print |engine.store|;
    print " treapEntries=";
    print |engine.docIds|;
    print "\n";

    print "[debug] starting customer registration: ";
    print customers;
    print " customers\n";
    i := 0;
    while i < customers
      invariant 0 <= i <= customers
      invariant rng > 0
      invariant engine.Ready()
      decreases customers - i
    {
      var nextRng1, widthSeed := NextRand(rng);
      rng := nextRng1;
      var nextRng2, minSeed := NextRand(rng);
      rng := nextRng2;
      var width := 1 + (widthSeed % (range / 2 + 1));
      var minScore := minSeed % range;
      var spec := QuerySpec(minScore, minScore + width, queryLimit);
      if i == 0 || i == 99 || i == 999 {
        print "[debug] registering customer ";
        print i + 1;
        print " before ProcessItem\n";
      }
      var events, ignoredQueryId := engine.ProcessItem(QueryAddItem(spec));
      summary := UpdateSummary(summary, events);
      if i == 0 || i == 99 || i == 999 {
        print "[debug] registered customer ";
        print i + 1;
        print " queries=";
        print |engine.queryIds|;
        print " pendingDocs=";
        print |engine.pendingState.byDoc|;
        print "\n";
      }
      i := i + 1;
      if i % 1000 == 0 {
        print "[perf] added ";
        print i;
        print " customers\n";
      }
    }

    print "[debug] customer registration complete: queries=";
    print |engine.queryIds|;
    print " pendingDocs=";
    print |engine.pendingState.byDoc|;
    print "\n";

    var nextDocId := documents;
    var tick := 0;
    while tick < ticks
      invariant 0 <= tick <= ticks
      invariant rng > 0
      invariant engine.Ready()
      decreases ticks - tick
    {
      print "[debug] starting tick ";
      print tick + 1;
      print " with docs=";
      print |engine.store|;
      print " queries=";
      print |engine.queryIds|;
      print "\n";
      var update := 0;
      while update < updatesPerTick
        invariant 0 <= update <= updatesPerTick
        invariant rng > 0
        invariant engine.Ready()
        decreases updatesPerTick - update
      {
        if |engine.docIds| > 0 {
          var nextRng3, pickSeed := NextRand(rng);
          rng := nextRng3;
          var nextRng4, scoreSeed := NextRand(rng);
          rng := nextRng4;
          var docId := engine.docIds[pickSeed % |engine.docIds|];
          match LookupState(engine.store, docId)
          case NoState => {}
          case HasState(docState) => {
            var updatedDocState := DocState(scoreSeed % range);
            if update == 0 {
            print "[debug] first update starting on tick ";
            print tick + 1;
            print "\n";
          }
          var events, ignoredQueryId2 := engine.ProcessItem(DocChangeItem(docId, HasState(docState), HasState(updatedDocState)));
          summary := UpdateSummary(summary, events);
          }
        }
        update := update + 1;
        if update % 10000 == 0 {
          print "[perf] tick ";
          print tick + 1;
          print " updates=";
          print update;
          print "\n";
        }
      }

      print "[perf] completed tick ";
      print tick + 1;
      print "/";
      print ticks;
      print "\n";

      var insert := 0;
      while insert < insertsPerTick
        invariant 0 <= insert <= insertsPerTick
        invariant rng > 0
        invariant engine.Ready()
        decreases insertsPerTick - insert
      {
        var nextRng5, scoreSeed := NextRand(rng);
        rng := nextRng5;
        var events, ignoredQueryId3 := engine.ProcessItem(DocChangeItem(nextDocId, NoState, HasState(DocState(scoreSeed % range))));
        summary := UpdateSummary(summary, events);
        nextDocId := nextDocId + 1;
        insert := insert + 1;
      }

      var delete := 0;
      while delete < deletesPerTick
        invariant 0 <= delete <= deletesPerTick
        invariant rng > 0
        invariant engine.Ready()
        decreases deletesPerTick - delete
      {
        if |engine.docIds| > 0 {
          var nextRng6, pickSeed := NextRand(rng);
          rng := nextRng6;
          var docId := engine.docIds[pickSeed % |engine.docIds|];
          match LookupState(engine.store, docId)
          case NoState => {}
          case HasState(docState) => {
            var events, ignoredQueryId4 := engine.ProcessItem(DocChangeItem(docId, HasState(docState), NoState));
            summary := UpdateSummary(summary, events);
          }
        }
        delete := delete + 1;
      }

      tick := tick + 1;
    }

    print "[perf] documents=";
    print documents;
    print " customers=";
    print customers;
    print " changes=";
    print ticks * (updatesPerTick + insertsPerTick + deletesPerTick);
    print " matchEvents=";
    print summary.matchEvents;
    print " evictions=";
    print summary.evictions;
    print " retrievalBatches=";
    print summary.retrievalBatches;
    print " retrievalDocs=";
    print summary.retrievalDocs;
    print "\n";
  }
}
