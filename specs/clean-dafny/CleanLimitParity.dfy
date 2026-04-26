include "CleanLimitEngine.dfy"

module CleanLimitParity {
  import opened DocsIndexModel
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

  function InsertQueryIdSorted(ids: seq<QueryId>, id: QueryId): seq<QueryId> {
    if |ids| == 0 then [id]
    else if id == ids[0] then ids
    else if id < ids[0] then [id] + ids
    else [ids[0]] + InsertQueryIdSorted(ids[1..], id)
  }

  function NormalizeQueryIds(ids: seq<QueryId>): seq<QueryId>
    decreases |ids|
  {
    if |ids| == 0 then []
    else InsertQueryIdSorted(NormalizeQueryIds(ids[1..]), ids[0])
  }

  function NormalizeRetrievalDoc(doc: RetrievalDoc): RetrievalDoc {
    RetrievalDoc(doc.docId, doc.state, NormalizeQueryIds(doc.queries))
  }

  function InsertRetrievalDocSorted(docs: seq<RetrievalDoc>, doc: RetrievalDoc): seq<RetrievalDoc> {
    if |docs| == 0 then [NormalizeRetrievalDoc(doc)]
    else if doc.docId < docs[0].docId then [NormalizeRetrievalDoc(doc)] + docs
    else if doc.docId == docs[0].docId then [RetrievalDoc(doc.docId, docs[0].state, NormalizeQueryIds(docs[0].queries + doc.queries))] + docs[1..]
    else [docs[0]] + InsertRetrievalDocSorted(docs[1..], doc)
  }

  function NormalizeRetrievalDocs(docs: seq<RetrievalDoc>): seq<RetrievalDoc>
    decreases |docs|
  {
    if |docs| == 0 then []
    else InsertRetrievalDocSorted(NormalizeRetrievalDocs(docs[1..]), docs[0])
  }

  function NormalizeEvents(events: seq<DownstreamEvent>): seq<DownstreamEvent>
    decreases |events|
  {
    if |events| == 0 then []
    else
      match events[0]
      case MatchEvent(payload) => [MatchEvent(payload)] + NormalizeEvents(events[1..])
      case RetrievalEvent(docs) => [RetrievalEvent(NormalizeRetrievalDocs(docs))] + NormalizeEvents(events[1..])
  }

  method NewReadyEngine() returns (engine: CleanEngine)
    ensures engine.Ready()
    ensures fresh(engine)
  {
    engine := new CleanEngine();
  }

  method CheckState(engine: CleanEngine, name: string, opIndex: nat, item: StreamItem, state: EngineState, functionalEvents: seq<DownstreamEvent>, cleanEvents: seq<DownstreamEvent>, functionalQueryId: QueryId, cleanQueryId: QueryId)
    decreases *
  {
    var mismatch := !engine.Ready() || functionalQueryId != cleanQueryId || NormalizeEvents(functionalEvents) != NormalizeEvents(cleanEvents) || state.store != engine.store || state.docIds != engine.docIds || Entries(state.treap) != Entries(engine.docs) || state.nextQueryId != engine.nextQueryId || |state.queries| != |engine.queries|;
    if mismatch {
      print "scenario ";
      print name;
      print " mismatch at op ";
      print opIndex;
      print " item=";
      print item;
      print "\nfunctional queryId=";
      print functionalQueryId;
      print ", clean queryId=";
      print cleanQueryId;
      print "\nfunctional events=";
      print functionalEvents;
      print "\nclean events=";
      print cleanEvents;
      print "\nfunctional store=";
      print state.store;
      print "\nclean store=";
      print engine.store;
      print "\nfunctional entries=";
      print Entries(state.treap);
      print "\nclean entries=";
      print Entries(engine.docs);
      print "\n";
    }

    if engine.Ready() {
      var i := 0;
      while i < |state.queries|
        invariant 0 <= i <= |state.queries|
        decreases |state.queries| - i
      {
        var query := state.queries[i];
        var cleanVisible := engine.QueryVisible(query.id);
        if !(query.id in engine.queries) || engine.queries[query.id].spec != query.spec || cleanVisible != query.visible {
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
          print "\nclean visible=";
          print cleanVisible;
          print "\nfunctional spec=";
          print query.spec;
          print "\nclean spec=";
          if query.id in engine.queries {
            print engine.queries[query.id].spec;
          } else {
            print "<missing>";
          }
          print "\n";
          mismatch := true;
        }
        i := i + 1;
      }
    }

    if mismatch {
      expect false;
    }
  }

  method RunScenario(name: string, seed: int, documents: nat, customers: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, queryLimit: nat, density: nat)
    decreases *
  {
    var engine := NewReadyEngine();
    var state := EmptyState();
    var summary := SummaryZero();
    var rng := if seed <= 0 then 1 else seed;
    var seedDocs: seq<SeedDoc> := [];
    var nextDocId := documents;
    var range := if density == 0 then 1 else documents / density + 1;
    var opIndex: nat := 0;

    if !engine.Ready() {
      expect false;
      return;
    }

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
    var cleanEvents, cleanQueryId := engine.ProcessItemWhenReady(seedItem);
    state := nextState;
    summary := UpdateSummary(summary, functionalEvents);
    CheckState(engine, name, opIndex, seedItem, state, functionalEvents, cleanEvents, functionalQueryId, cleanQueryId);

    if !engine.Ready() {
      expect false;
      return;
    }

    i := 0;
    while i < customers
      invariant 0 <= i <= customers
      invariant rng > 0
      invariant SumConsistent(state.treap)
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
      var item := QueryAddItem(QuerySpec(minScore, maxScore, queryLimit));
      var stateAfterAdd, functionalAddEvents, functionalAddQueryId := ProcessItem(state, item);
      var cleanAddEvents, cleanAddQueryId := engine.ProcessItemWhenReady(item);
      state := stateAfterAdd;
      summary := UpdateSummary(summary, functionalAddEvents);
      opIndex := opIndex + 1;
      CheckState(engine, name, opIndex, item, state, functionalAddEvents, cleanAddEvents, functionalAddQueryId, cleanAddQueryId);
      i := i + 1;
    }

    var tick := 0;
    while tick < ticks
      invariant 0 <= tick <= ticks
      invariant rng > 0
      invariant SumConsistent(state.treap)
      invariant engine.Ready()
      decreases ticks - tick
    {
      var update := 0;
      while update < updatesPerTick
        invariant 0 <= update <= updatesPerTick
        invariant rng > 0
        invariant SumConsistent(state.treap)
        invariant engine.Ready()
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
            var cleanUpdateEvents, cleanUpdateQueryId := engine.ProcessItemWhenReady(item);
            state := stateAfterUpdate;
            summary := UpdateSummary(summary, functionalUpdateEvents);
            opIndex := opIndex + 1;
            CheckState(engine, name, opIndex, item, state, functionalUpdateEvents, cleanUpdateEvents, functionalUpdateQueryId, cleanUpdateQueryId);
          }
        }
        update := update + 1;
      }

      var insert := 0;
      while insert < insertsPerTick
        invariant 0 <= insert <= insertsPerTick
        invariant rng > 0
        invariant SumConsistent(state.treap)
        invariant engine.Ready()
        decreases insertsPerTick - insert
      {
        var nextRng5, scoreSeed := NextRand(rng);
        rng := nextRng5;
        var item := DocChangeItem(nextDocId, NoState, HasState(DocState(scoreSeed % range)));
        var stateAfterInsert, functionalInsertEvents, functionalInsertQueryId := ProcessItem(state, item);
        var cleanInsertEvents, cleanInsertQueryId := engine.ProcessItemWhenReady(item);
        state := stateAfterInsert;
        summary := UpdateSummary(summary, functionalInsertEvents);
        nextDocId := nextDocId + 1;
        opIndex := opIndex + 1;
        CheckState(engine, name, opIndex, item, state, functionalInsertEvents, cleanInsertEvents, functionalInsertQueryId, cleanInsertQueryId);
        insert := insert + 1;
      }

      var delete := 0;
      while delete < deletesPerTick
        invariant 0 <= delete <= deletesPerTick
        invariant rng > 0
        invariant SumConsistent(state.treap)
        invariant engine.Ready()
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
            var cleanDeleteEvents, cleanDeleteQueryId := engine.ProcessItemWhenReady(item);
            state := stateAfterDelete;
            summary := UpdateSummary(summary, functionalDeleteEvents);
            opIndex := opIndex + 1;
            CheckState(engine, name, opIndex, item, state, functionalDeleteEvents, cleanDeleteEvents, functionalDeleteQueryId, cleanDeleteQueryId);
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

  method Main()
    decreases *
  {
    RunScenario("clean-small", 1, 8, 4, 4, 2, 1, 1, 3, 2);
    RunScenario("clean-medium", 17, 20, 8, 8, 3, 2, 2, 5, 3);
  }
}