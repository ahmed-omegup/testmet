include "CleanLimitEngine.dfy"

module CleanLimitPerf {
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

  method RunScenario(name: string, seed: int, documents: nat, customers: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, queryLimit: nat, density: nat)
    decreases *
  {
    var engine: CleanEngine := new CleanEngine();
    var summary := SummaryZero();
    var rng := if seed <= 0 then 1 else seed;
    var seedDocs := new SeedDoc[documents];
    var nextDocId := documents;
    var range := if density == 0 then 1 else documents / density + 1;

    var i := 0;
    while i < documents
      invariant 0 <= i <= documents
      invariant rng > 0
      decreases documents - i
    {
      var nextRng, scoreSeed := NextRand(rng);
      rng := nextRng;
      seedDocs[i] := SeedDoc(i, DocState(scoreSeed % range));
      i := i + 1;
    }

    var seedEvents, ignoredSeedQueryId := engine.ProcessItemWhenReady(SeedDocsItem(seedDocs[..]));
    summary := UpdateSummary(summary, seedEvents);

    if !engine.Ready() {
      expect false;
      return;
    }

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
      var maxScore := minScore + width;
      var spec := QuerySpec(minScore, maxScore, queryLimit);
      var events, ignoredQueryId := engine.ProcessItemWhenReady(QueryAddItem(spec));
      summary := UpdateSummary(summary, events);
      i := i + 1;
    }

    var tick := 0;
    while tick < ticks
      invariant 0 <= tick <= ticks
      invariant rng > 0
      invariant engine.Ready()
      decreases ticks - tick
    {
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
          var picked := pickSeed % |engine.docIds|;
          var docId := engine.docIds[picked];
          match LookupState(engine.store, docId)
          case NoState => {
          }
          case HasState(docState) => {
            var updatedDocState := DocState(scoreSeed % range);
            var events, ignoredQueryId2 := engine.ProcessItemWhenReady(DocChangeItem(docId, HasState(docState), HasState(updatedDocState)));
            summary := UpdateSummary(summary, events);
          }
        }
        update := update + 1;
      }

      var insert := 0;
      while insert < insertsPerTick
        invariant 0 <= insert <= insertsPerTick
        invariant rng > 0
        invariant engine.Ready()
        decreases insertsPerTick - insert
      {
        var nextRng5, scoreSeed := NextRand(rng);
        rng := nextRng5;
        var newDoc := DocState(scoreSeed % range);
        var events, ignoredQueryId3 := engine.ProcessItemWhenReady(DocChangeItem(nextDocId, NoState, HasState(newDoc)));
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
          var picked := pickSeed % |engine.docIds|;
          var docId := engine.docIds[picked];
          match LookupState(engine.store, docId)
          case NoState => {
          }
          case HasState(docState) => {
            var events, ignoredQueryId4 := engine.ProcessItemWhenReady(DocChangeItem(docId, HasState(docState), NoState));
            summary := UpdateSummary(summary, events);
          }
        }
        delete := delete + 1;
      }

      tick := tick + 1;
    }

    print "scenario ";
    print name;
    print " done: events=";
    print summary.eventsProcessed;
    print ", matches=";
    print summary.matchEvents;
    print ", evictions=";
    print summary.evictions;
    print ", retrievalBatches=";
    print summary.retrievalBatches;
    print ", retrievalDocs=";
    print summary.retrievalDocs;
    print "\n";
  }

  method Main()
    decreases *
  {
    RunScenario("whole-stack-benchmark-like-clean", 123, 800, 120, 30, 35, 8, 8, 25, 10);
  }
}