include "ThunderDbStack.dfy"

module ThunderDbStackBench {
  import opened DocsIndexModel
  import opened DocsIndexTreap
  import opened ThunderDbStack

  const Modulus: int := 2147483647
  const Multiplier: int := 48271

  datatype ObservedQuery = ObservedQuery(id: QueryId, spec: QuerySpec, docs: seq<StoredDoc>)

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

  function EntryIds(entries: seq<Entry>): seq<DocId> {
    if |entries| == 0 then [] else [entries[0].id] + EntryIds(entries[1..])
  }

  function QueryKnown(observed: seq<ObservedQuery>, id: QueryId): bool {
    if |observed| == 0 then false
    else observed[0].id == id || QueryKnown(observed[1..], id)
  }

  function PutObservedQueryDoc(docs: seq<StoredDoc>, id: DocId, state: DocState): seq<StoredDoc> {
    if |docs| == 0 then [StoredDoc(id, state)]
    else if docs[0].id == id then [StoredDoc(id, state)] + docs[1..]
    else [docs[0]] + PutObservedQueryDoc(docs[1..], id, state)
  }

  function RemoveObservedQueryDoc(docs: seq<StoredDoc>, id: DocId): seq<StoredDoc> {
    if |docs| == 0 then []
    else if docs[0].id == id then docs[1..]
    else [docs[0]] + RemoveObservedQueryDoc(docs[1..], id)
  }

  function EvictedDocForQuery(evictions: seq<Eviction>, queryId: QueryId): seq<DocId> {
    if |evictions| == 0 then []
    else if evictions[0].queryId == queryId then [evictions[0].docId]
    else EvictedDocForQuery(evictions[1..], queryId)
  }

  function ApplyMatchToObservedQuery(query: ObservedQuery, payload: MatchPayload): ObservedQuery {
    var docs := if ContainsQueryId(payload.matchesOld, query.id) then RemoveObservedQueryDoc(query.docs, payload.docId) else query.docs;
    var evicted := EvictedDocForQuery(payload.evictions, query.id);
    var docs2 := if |evicted| == 0 then docs else RemoveObservedQueryDoc(docs, evicted[0]);
    if ContainsQueryId(payload.matchesNew, query.id) then
      match payload.newState
      case NoState => ObservedQuery(query.id, query.spec, RemoveObservedQueryDoc(docs2, payload.docId))
      case HasState(state) => ObservedQuery(query.id, query.spec, PutObservedQueryDoc(docs2, payload.docId, state))
    else
      ObservedQuery(query.id, query.spec, docs2)
  }

  function ApplyMatchToObservedQueries(observed: seq<ObservedQuery>, payload: MatchPayload): seq<ObservedQuery>
    decreases |observed|
  {
    if |observed| == 0 then []
    else [ApplyMatchToObservedQuery(observed[0], payload)] + ApplyMatchToObservedQueries(observed[1..], payload)
  }

  function ApplyRetrievalDocToObservedQuery(query: ObservedQuery, retrieval: RetrievalDoc): ObservedQuery {
    if ContainsQueryId(retrieval.queries, query.id)
      then ObservedQuery(query.id, query.spec, PutObservedQueryDoc(query.docs, retrieval.docId, retrieval.state))
      else query
  }

  function ApplyRetrievalDocsToObservedQuery(query: ObservedQuery, docs: seq<RetrievalDoc>): ObservedQuery
    decreases |docs|
  {
    if |docs| == 0 then query
    else ApplyRetrievalDocsToObservedQuery(ApplyRetrievalDocToObservedQuery(query, docs[0]), docs[1..])
  }

  function ApplyRetrievalToObservedQueries(observed: seq<ObservedQuery>, docs: seq<RetrievalDoc>): seq<ObservedQuery>
    decreases |observed|
  {
    if |observed| == 0 then []
    else [ApplyRetrievalDocsToObservedQuery(observed[0], docs)] + ApplyRetrievalToObservedQueries(observed[1..], docs)
  }

  function ApplyEventsToObserved(observed: seq<ObservedQuery>, events: seq<DownstreamEvent>): seq<ObservedQuery>
    decreases |events|
  {
    if |events| == 0 then observed
    else
      match events[0]
      case MatchEvent(payload) => ApplyEventsToObserved(ApplyMatchToObservedQueries(observed, payload), events[1..])
      case RetrievalEvent(docs) => ApplyEventsToObserved(ApplyRetrievalToObservedQueries(observed, docs), events[1..])
  }

  method CheckObservedState(name: string, opIndex: nat, state: EngineState, observed: seq<ObservedQuery>)
  {
    var i := 0;
    while i < |observed|
      invariant 0 <= i <= |observed|
      decreases |observed| - i
    {
      var expectedIds := QueryVisible(state.queries, observed[i].id);
      var actualIds := EntryIds(BuildEntriesFromStore(observed[i].docs));
      if expectedIds != actualIds {
        print "scenario ";
        print name;
        print " mismatch at op ";
        print opIndex;
        print " query ";
        print observed[i].id;
        print "\n";
        expect expectedIds == actualIds;
      }
      var j := 0;
      while j < |observed[i].docs|
        invariant 0 <= j <= |observed[i].docs|
        decreases |observed[i].docs| - j
      {
        match LookupState(state.store, observed[i].docs[j].id)
        case NoState => {
          expect false;
        }
        case HasState(docState) => {
          expect docState == observed[i].docs[j].state;
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }

  method RunScenario(name: string, seed: int, documents: nat, customers: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, queryLimit: nat, density: nat, checksEveryOps: nat)
  {
    var state := EmptyState();
    var observed: seq<ObservedQuery> := [];
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
    observed := ApplyEventsToObserved(observed, seedEvents);
    summary := UpdateSummary(summary, seedEvents);
    CheckObservedState(name, 0, state, observed);

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
      observed := observed + [ObservedQuery(queryId, spec, [])];
      observed := ApplyEventsToObserved(observed, events);
      summary := UpdateSummary(summary, events);
      i := i + 1;
    }
    CheckObservedState(name, customers, state, observed);

    var opIndex: nat := customers;
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
            observed := ApplyEventsToObserved(observed, events);
            summary := UpdateSummary(summary, events);
            opIndex := opIndex + 1;
            if checksEveryOps > 0 && opIndex % checksEveryOps == 0 {
              CheckObservedState(name, opIndex, state, observed);
            }
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
        observed := ApplyEventsToObserved(observed, events);
        summary := UpdateSummary(summary, events);
        nextDocId := nextDocId + 1;
        opIndex := opIndex + 1;
        if checksEveryOps > 0 && opIndex % checksEveryOps == 0 {
          CheckObservedState(name, opIndex, state, observed);
        }
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
            observed := ApplyEventsToObserved(observed, events);
            summary := UpdateSummary(summary, events);
            opIndex := opIndex + 1;
            if checksEveryOps > 0 && opIndex % checksEveryOps == 0 {
              CheckObservedState(name, opIndex, state, observed);
            }
          }
        }
        delete := delete + 1;
      }

      tick := tick + 1;
    }

    CheckObservedState(name, opIndex, state, observed);
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

  method Main() {
    RunScenario("whole-stack-small", 42, 200, 30, 20, 10, 2, 2, 12, 8, 1);
    RunScenario("whole-stack-benchmark-like", 123, 800, 120, 30, 35, 8, 8, 25, 10, 100);
  }
}