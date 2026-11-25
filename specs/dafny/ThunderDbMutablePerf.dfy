include "ThunderDbMutable.dfy"

module ThunderDbMutablePerf {
  import opened DocsIndexTreap
  import opened ThunderDbStack
  import opened ThunderDbMutable

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

  class MutablePerfRunner {
    var engine: MutableEngine

    constructor ()
      ensures this.engine.Ready()
    {
      this.engine := new MutableEngine();
    }

    method {:verify false} RunScenario(name: string, seed: int, documents: nat, customers: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, queryLimit: nat, density: nat, drainPerTick: bool)
      decreases *
    {
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

      var seedEvents, ignoredQueryId := engine.ProcessItem(SeedDocsItem(seedDocs[..]));
      summary := UpdateSummary(summary, seedEvents);

      i := 0;
      while i < customers
        invariant 0 <= i <= customers
        invariant rng > 0
        invariant SumConsistent(engine.docs)
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
        var events: seq<DownstreamEvent>;
        var queryId: QueryId;
        if drainPerTick {
          events, queryId := engine.ProcessItemDeferred(QueryAddItem(spec));
        } else {
          events, queryId := engine.ProcessItem(QueryAddItem(spec));
        }
        summary := UpdateSummary(summary, events);
        i := i + 1;
      }
      if drainPerTick {
        var retrievalEvents := engine.DrainPendingRetrievalsGrouped();
        summary := UpdateSummary(summary, retrievalEvents);
      }

      var tick := 0;
      while tick < ticks
        invariant 0 <= tick <= ticks
        invariant rng > 0
        invariant SumConsistent(engine.docs)
        decreases ticks - tick
      {
        var update := 0;
        while update < updatesPerTick
          invariant 0 <= update <= updatesPerTick
          invariant rng > 0
          invariant SumConsistent(engine.docs)
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
              var events: seq<DownstreamEvent>;
              var ignoredQueryId2: QueryId;
              if drainPerTick {
                events, ignoredQueryId2 := engine.ProcessItemDeferred(DocChangeItem(docId, HasState(docState), HasState(updatedDocState)));
              } else {
                events, ignoredQueryId2 := engine.ProcessItem(DocChangeItem(docId, HasState(docState), HasState(updatedDocState)));
              }
              summary := UpdateSummary(summary, events);
            }
          }
          update := update + 1;
        }

        var insert := 0;
        while insert < insertsPerTick
          invariant 0 <= insert <= insertsPerTick
          invariant rng > 0
          invariant SumConsistent(engine.docs)
          decreases insertsPerTick - insert
        {
          var nextRng5, scoreSeed := NextRand(rng);
          rng := nextRng5;
          var newDoc := DocState(scoreSeed % range);
          var events: seq<DownstreamEvent>;
          var ignoredQueryId3: QueryId;
          if drainPerTick {
            events, ignoredQueryId3 := engine.ProcessItemDeferred(DocChangeItem(nextDocId, NoState, HasState(newDoc)));
          } else {
            events, ignoredQueryId3 := engine.ProcessItem(DocChangeItem(nextDocId, NoState, HasState(newDoc)));
          }
          summary := UpdateSummary(summary, events);
          nextDocId := nextDocId + 1;
          insert := insert + 1;
        }

        var delete := 0;
        while delete < deletesPerTick
          invariant 0 <= delete <= deletesPerTick
          invariant rng > 0
          invariant SumConsistent(engine.docs)
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
              var events: seq<DownstreamEvent>;
              var ignoredQueryId4: QueryId;
              if drainPerTick {
                events, ignoredQueryId4 := engine.ProcessItemDeferred(DocChangeItem(docId, HasState(docState), NoState));
              } else {
                events, ignoredQueryId4 := engine.ProcessItem(DocChangeItem(docId, HasState(docState), NoState));
              }
              summary := UpdateSummary(summary, events);
            }
          }
          delete := delete + 1;
        }

        if drainPerTick {
          var retrievalEvents := engine.DrainPendingRetrievalsGrouped();
          summary := UpdateSummary(summary, retrievalEvents);
        }

        tick := tick + 1;
      }

      if drainPerTick {
        var retrievalEvents := engine.DrainPendingRetrievalsGrouped();
        summary := UpdateSummary(summary, retrievalEvents);
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
  }

  method {:verify false} Main()
    decreases *
  {
    var runner := new MutablePerfRunner();
    runner.RunScenario("whole-stack-benchmark-like-mutable", 123, 800, 120, 30, 35, 8, 8, 25, 10, false);
    runner := new MutablePerfRunner();
    runner.RunScenario("whole-stack-benchmark-like-mutable-per-tick", 123, 800, 120, 30, 35, 8, 8, 25, 10, true);
  }
}
