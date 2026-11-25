include "ThunderDbStack.dfy"

module ThunderDbStackPerf {
  import opened DocsIndexTreap
  import opened ThunderDbStack

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
  {
    var state := EmptyState();
    var summary := SummaryZero();
    var rng := if seed <= 0 then 1 else seed;
    var seedDocs: seq<SeedDoc> := [];
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
      seedDocs := seedDocs + [SeedDoc(i, DocState(scoreSeed % range))];
      i := i + 1;
    }

    var nextState, seedEvents, ignoredQueryId := ProcessItem(state, SeedDocsItem(seedDocs));
    state := nextState;
    summary := UpdateSummary(summary, seedEvents);

    i := 0;
    while i < customers
      invariant 0 <= i <= customers
      invariant rng > 0
      invariant SumConsistent(state.treap)
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
      var stateAfterAdd, events, queryId := ProcessItem(state, QueryAddItem(spec));
      state := stateAfterAdd;
      summary := UpdateSummary(summary, events);
      i := i + 1;
    }

    var tick := 0;
    while tick < ticks
      invariant 0 <= tick <= ticks
      invariant rng > 0
      invariant SumConsistent(state.treap)
      decreases ticks - tick
    {
      var update := 0;
      while update < updatesPerTick
        invariant 0 <= update <= updatesPerTick
        invariant rng > 0
        invariant SumConsistent(state.treap)
        decreases updatesPerTick - update
      {
        if |state.docIds| > 0 {
          var nextRng3, pickSeed := NextRand(rng);
          rng := nextRng3;
          var nextRng4, scoreSeed := NextRand(rng);
          rng := nextRng4;
          var picked := pickSeed % |state.docIds|;
          var docId := state.docIds[picked];
          match LookupState(state.store, docId)
          case NoState => {
          }
          case HasState(docState) => {
            var updatedDocState := DocState(scoreSeed % range);
            var stateAfterUpdate, events, ignoredQueryId2 := ProcessItem(state, DocChangeItem(docId, HasState(docState), HasState(updatedDocState)));
            state := stateAfterUpdate;
            summary := UpdateSummary(summary, events);
          }
        }
        update := update + 1;
      }

      var insert := 0;
      while insert < insertsPerTick
        invariant 0 <= insert <= insertsPerTick
        invariant rng > 0
        invariant SumConsistent(state.treap)
        decreases insertsPerTick - insert
      {
        var nextRng5, scoreSeed := NextRand(rng);
        rng := nextRng5;
        var newDoc := DocState(scoreSeed % range);
        var stateAfterInsert, events, ignoredQueryId3 := ProcessItem(state, DocChangeItem(nextDocId, NoState, HasState(newDoc)));
        state := stateAfterInsert;
        summary := UpdateSummary(summary, events);
        nextDocId := nextDocId + 1;
        insert := insert + 1;
      }

      var delete := 0;
      while delete < deletesPerTick
        invariant 0 <= delete <= deletesPerTick
        invariant rng > 0
        invariant SumConsistent(state.treap)
        decreases deletesPerTick - delete
      {
        if |state.docIds| > 0 {
          var nextRng6, pickSeed := NextRand(rng);
          rng := nextRng6;
          var picked := pickSeed % |state.docIds|;
          var docId := state.docIds[picked];
          match LookupState(state.store, docId)
          case NoState => {
          }
          case HasState(docState) => {
            var stateAfterDelete, events, ignoredQueryId4 := ProcessItem(state, DocChangeItem(docId, HasState(docState), NoState));
            state := stateAfterDelete;
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

  method Main() {
    RunScenario("whole-stack-benchmark-like", 123, 800, 120, 30, 35, 8, 8, 25, 10);
  }
}