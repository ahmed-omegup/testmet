include "ThunderDbMutable.dfy"

module ThunderDbMutableParity {
  import opened DocsIndexModel
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

  function MutableQueryVisible(queries: map<QueryId, QueryState>, id: QueryId): seq<DocId> {
    if id in queries then queries[id].visible else []
  }

  class MutableParityRunner {
    var engine: MutableEngine

    constructor ()
      ensures this.engine.Ready()
    {
      this.engine := new MutableEngine();
    }

    method {:verify false} CheckState(name: string, opIndex: nat, item: StreamItem, state: EngineState, functionalEvents: seq<DownstreamEvent>, mutableEvents: seq<DownstreamEvent>, functionalQueryId: QueryId, mutableQueryId: QueryId)
      decreases *
    {
      var functionalDelta := UpdateSummary(SummaryZero(), functionalEvents);
      var mutableDelta := UpdateSummary(SummaryZero(), mutableEvents);
      var mismatch := functionalQueryId != mutableQueryId || functionalDelta != mutableDelta || state.store != this.engine.store || state.docIds != this.engine.docIds || Entries(state.treap) != Entries(this.engine.docs) || state.nextQueryId != this.engine.nextQueryId || |state.queries| != |this.engine.queries|;
      if mismatch {
        print "scenario ";
        print name;
        print " mismatch at op ";
        print opIndex;
        print " item=";
        print item;
        print "\nfunctional queryId=";
        print functionalQueryId;
        print ", mutable queryId=";
        print mutableQueryId;
        print "\nfunctional events=";
        print functionalEvents;
        print "\nmutable events=";
        print mutableEvents;
        print "\nfunctional delta=";
        print functionalDelta;
        print "\nmutable delta=";
        print mutableDelta;
        print "\n";
      }

      var i := 0;
      while i < |state.queries|
        invariant 0 <= i <= |state.queries|
        decreases |state.queries| - i
      {
        var query := state.queries[i];
        if !(query.id in this.engine.queries) || this.engine.queries[query.id].spec != query.spec || this.engine.queries[query.id].visible != query.visible {
          print "scenario ";
          print name;
          print " query mismatch at op ";
          print opIndex;
          print " item=";
          print item;
          print " query=";
          print query.id;
          print "\nfunctional visible=";
          print query.visible;
          print "\nmutable visible=";
          print MutableQueryVisible(this.engine.queries, query.id);
          print "\nfunctional spec=";
          print query.spec;
          print "\nmutable spec=";
          if query.id in this.engine.queries {
            print this.engine.queries[query.id].spec;
          } else {
            print "<missing>";
          }
          print "\nfunctional store=";
          print state.store;
          print "\nmutable store=";
          print this.engine.store;
          print "\n";
          mismatch := true;
        }
        i := i + 1;
      }

      if mismatch {
        expect false;
      }
    }

    method {:verify false} RunScenario(name: string, seed: int, documents: nat, customers: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, queryLimit: nat, density: nat)
      decreases *
    {
      var state := EmptyState();
      var summary := SummaryZero();
      var rng := if seed <= 0 then 1 else seed;
      var seedDocs: seq<SeedDoc> := [];
      var nextDocId := documents;
      var range := if density == 0 then 1 else documents / density + 1;
      var opIndex: nat := 0;

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

      var seedItem := SeedDocsItem(seedDocs);
      var nextState, functionalEvents, functionalQueryId := ProcessItem(state, seedItem);
      var mutableEvents, mutableQueryId := this.engine.ProcessItem(seedItem);
      state := nextState;
      summary := UpdateSummary(summary, functionalEvents);
      this.CheckState(name, opIndex, seedItem, state, functionalEvents, mutableEvents, functionalQueryId, mutableQueryId);

      i := 0;
      while i < customers
        invariant 0 <= i <= customers
        invariant rng > 0
        invariant SumConsistent(state.treap)
        invariant this.engine.Ready()
        decreases customers - i
      {
        var nextRng1, widthSeed := NextRand(rng);
        rng := nextRng1;
        var nextRng2, minSeed := NextRand(rng);
        rng := nextRng2;
        var width := 1 + (widthSeed % (range / 2 + 1));
        var minScore := minSeed % range;
        var maxScore := minScore + width;
        var item := QueryAddItem(QuerySpec(minScore, maxScore, queryLimit));
        var stateAfterAdd, functionalAddEvents, functionalAddQueryId := ProcessItem(state, item);
        var mutableAddEvents, mutableAddQueryId := this.engine.ProcessItem(item);
        state := stateAfterAdd;
        summary := UpdateSummary(summary, functionalAddEvents);
        opIndex := opIndex + 1;
        this.CheckState(name, opIndex, item, state, functionalAddEvents, mutableAddEvents, functionalAddQueryId, mutableAddQueryId);
        i := i + 1;
      }

      var tick := 0;
      while tick < ticks
        invariant 0 <= tick <= ticks
        invariant rng > 0
        invariant SumConsistent(state.treap)
        invariant this.engine.Ready()
        decreases ticks - tick
      {
        var update := 0;
        while update < updatesPerTick
          invariant 0 <= update <= updatesPerTick
          invariant rng > 0
          invariant SumConsistent(state.treap)
          invariant this.engine.Ready()
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
              var item := DocChangeItem(docId, HasState(docState), HasState(DocState(scoreSeed % range)));
              var stateAfterUpdate, functionalUpdateEvents, functionalUpdateQueryId := ProcessItem(state, item);
              var mutableUpdateEvents, mutableUpdateQueryId := this.engine.ProcessItem(item);
              state := stateAfterUpdate;
              summary := UpdateSummary(summary, functionalUpdateEvents);
              opIndex := opIndex + 1;
              this.CheckState(name, opIndex, item, state, functionalUpdateEvents, mutableUpdateEvents, functionalUpdateQueryId, mutableUpdateQueryId);
            }
          }
          update := update + 1;
        }

        var insert := 0;
        while insert < insertsPerTick
          invariant 0 <= insert <= insertsPerTick
          invariant rng > 0
          invariant SumConsistent(state.treap)
          invariant this.engine.Ready()
          decreases insertsPerTick - insert
        {
          var nextRng5, scoreSeed := NextRand(rng);
          rng := nextRng5;
          var item := DocChangeItem(nextDocId, NoState, HasState(DocState(scoreSeed % range)));
          var stateAfterInsert, functionalInsertEvents, functionalInsertQueryId := ProcessItem(state, item);
          var mutableInsertEvents, mutableInsertQueryId := this.engine.ProcessItem(item);
          state := stateAfterInsert;
          summary := UpdateSummary(summary, functionalInsertEvents);
          nextDocId := nextDocId + 1;
          opIndex := opIndex + 1;
          this.CheckState(name, opIndex, item, state, functionalInsertEvents, mutableInsertEvents, functionalInsertQueryId, mutableInsertQueryId);
          insert := insert + 1;
        }

        var delete := 0;
        while delete < deletesPerTick
          invariant 0 <= delete <= deletesPerTick
          invariant rng > 0
          invariant SumConsistent(state.treap)
          invariant this.engine.Ready()
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
              var item := DocChangeItem(docId, HasState(docState), NoState);
              var stateAfterDelete, functionalDeleteEvents, functionalDeleteQueryId := ProcessItem(state, item);
              var mutableDeleteEvents, mutableDeleteQueryId := this.engine.ProcessItem(item);
              state := stateAfterDelete;
              summary := UpdateSummary(summary, functionalDeleteEvents);
              opIndex := opIndex + 1;
              this.CheckState(name, opIndex, item, state, functionalDeleteEvents, mutableDeleteEvents, functionalDeleteQueryId, mutableDeleteQueryId);
            }
          }
          delete := delete + 1;
        }

        tick := tick + 1;
      }

      print "scenario ";
      print name;
      print " passed: events=";
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
    var runner := new MutableParityRunner();
    runner.RunScenario("whole-stack-small-parity", 42, 200, 30, 20, 10, 2, 2, 12, 8);
    runner := new MutableParityRunner();
    runner.RunScenario("whole-stack-benchmark-like-parity", 123, 800, 120, 30, 35, 8, 8, 25, 10);
  }
}