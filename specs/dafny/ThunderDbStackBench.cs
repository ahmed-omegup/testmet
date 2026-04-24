// Dafny program ThunderDbStackBench.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.11.0.0
// Command-line arguments: run specs/dafny/ThunderDbStackBench.dfy --no-verify
// ThunderDbStackBench.dfy


module ThunderDbStackBench {
  const Modulus: int := 2147483647
  const Multiplier: int := 48271

  function NextState(state: int): int
    decreases state
  {
    var next: int := state * Multiplier % Modulus;
    if next <= 0 then
      next + Modulus
    else
      next
  }

  method NextRand(state: int) returns (nextState: int, value: int)
    requires state > 0
    ensures nextState > 0
    ensures value == nextState
    decreases state
  {
    nextState := NextState(state);
    value := nextState;
  }

  function EntryIds(entries: seq<Entry>): seq<DocId>
    decreases entries
  {
    if |entries| == 0 then
      []
    else
      [entries[0].id] + EntryIds(entries[1..])
  }

  function QueryKnown(observed: seq<ObservedQuery>, id: QueryId): bool
    decreases observed, id
  {
    if |observed| == 0 then
      false
    else
      observed[0].id == id || QueryKnown(observed[1..], id)
  }

  function PutObservedQueryDoc(docs: seq<StoredDoc>, id: DocId, state: DocState): seq<StoredDoc>
    decreases docs, id, state
  {
    if |docs| == 0 then
      [StoredDoc(id, state)]
    else if docs[0].id == id then
      [StoredDoc(id, state)] + docs[1..]
    else
      [docs[0]] + PutObservedQueryDoc(docs[1..], id, state)
  }

  function RemoveObservedQueryDoc(docs: seq<StoredDoc>, id: DocId): seq<StoredDoc>
    decreases docs, id
  {
    if |docs| == 0 then
      []
    else if docs[0].id == id then
      docs[1..]
    else
      [docs[0]] + RemoveObservedQueryDoc(docs[1..], id)
  }

  function EvictedDocForQuery(evictions: seq<Eviction>, queryId: QueryId): seq<DocId>
    decreases evictions, queryId
  {
    if |evictions| == 0 then
      []
    else if evictions[0].queryId == queryId then
      [evictions[0].docId]
    else
      EvictedDocForQuery(evictions[1..], queryId)
  }

  function ApplyMatchToObservedQuery(query: ObservedQuery, payload: MatchPayload): ObservedQuery
    decreases query, payload
  {
    var docs: seq<StoredDoc> := if ContainsQueryId(payload.matchesOld, query.id) then RemoveObservedQueryDoc(query.docs, payload.docId) else query.docs;
    var evicted: seq<DocId> := EvictedDocForQuery(payload.evictions, query.id);
    var docs2: seq<StoredDoc> := if |evicted| == 0 then docs else RemoveObservedQueryDoc(docs, evicted[0]);
    if ContainsQueryId(payload.matchesNew, query.id) then
      match payload.newState
      case NoState() =>
        ObservedQuery(query.id, query.spec, RemoveObservedQueryDoc(docs2, payload.docId))
      case HasState(state) =>
        ObservedQuery(query.id, query.spec, PutObservedQueryDoc(docs2, payload.docId, state))
    else
      ObservedQuery(query.id, query.spec, docs2)
  }

  function ApplyMatchToObservedQueries(observed: seq<ObservedQuery>, payload: MatchPayload): seq<ObservedQuery>
    decreases |observed|
  {
    if |observed| == 0 then
      []
    else
      [ApplyMatchToObservedQuery(observed[0], payload)] + ApplyMatchToObservedQueries(observed[1..], payload)
  }

  function ApplyRetrievalDocToObservedQuery(query: ObservedQuery, retrieval: RetrievalDoc): ObservedQuery
    decreases query, retrieval
  {
    if ContainsQueryId(retrieval.queries, query.id) then
      ObservedQuery(query.id, query.spec, PutObservedQueryDoc(query.docs, retrieval.docId, retrieval.state))
    else
      query
  }

  function ApplyRetrievalDocsToObservedQuery(query: ObservedQuery, docs: seq<RetrievalDoc>): ObservedQuery
    decreases |docs|
  {
    if |docs| == 0 then
      query
    else
      ApplyRetrievalDocsToObservedQuery(ApplyRetrievalDocToObservedQuery(query, docs[0]), docs[1..])
  }

  function ApplyRetrievalToObservedQueries(observed: seq<ObservedQuery>, docs: seq<RetrievalDoc>): seq<ObservedQuery>
    decreases |observed|
  {
    if |observed| == 0 then
      []
    else
      [ApplyRetrievalDocsToObservedQuery(observed[0], docs)] + ApplyRetrievalToObservedQueries(observed[1..], docs)
  }

  function ApplyEventsToObserved(observed: seq<ObservedQuery>, events: seq<DownstreamEvent>): seq<ObservedQuery>
    decreases |events|
  {
    if |events| == 0 then
      observed
    else
      match events[0] case MatchEvent(payload) => ApplyEventsToObserved(ApplyMatchToObservedQueries(observed, payload), events[1..]) case RetrievalEvent(docs) => ApplyEventsToObserved(ApplyRetrievalToObservedQueries(observed, docs), events[1..])
  }

  method CheckObservedState(name: string, opIndex: nat, state: EngineState, observed: seq<ObservedQuery>)
    decreases name, opIndex, state, observed
  {
    var i := 0;
    while i < |observed|
      invariant 0 <= i <= |observed|
      decreases |observed| - i
    {
      var expectedIds := QueryVisible(state.queries, observed[i].id);
      var actualIds := EntryIds(BuildEntriesFromStore(observed[i].docs));
      if expectedIds != actualIds {
        print ""scenario "";
        print name;
        print "" mismatch at op "";
        print opIndex;
        print "" query "";
        print observed[i].id;
        print ""\n"";
        expect expectedIds == actualIds, ""expectation violation"";
      }
      var j := 0;
      while j < |observed[i].docs|
        invariant 0 <= j <= |observed[i].docs|
        decreases |observed[i].docs| - j
      {
        match LookupState(state.store, observed[i].docs[j].id)
        case {:split false} NoState() =>
          {
            expect false, ""expectation violation"";
          }
        case {:split false} HasState(docState) =>
          {
            expect docState == observed[i].docs[j].state, ""expectation violation"";
          }
          j := j + 1;
      }
      i := i + 1;
    }
  }

  method RunScenario(name: string, seed: int, documents: nat, customers: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, queryLimit: nat, density: nat, checksEveryOps: nat)
    decreases name, seed, documents, customers, ticks, updatesPerTick, insertsPerTick, deletesPerTick, queryLimit, density, checksEveryOps
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
      decreases customers - i
    {
      var nextRng1, widthSeed := NextRand(rng);
      rng := nextRng1;
      var nextRng2, minSeed := NextRand(rng);
      rng := nextRng2;
      var width := 1 + widthSeed % (range / 2 + 1);
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
      decreases ticks - tick
    {
      var update := 0;
      while update < updatesPerTick
        invariant 0 <= update <= updatesPerTick
        invariant rng > 0
        decreases updatesPerTick - update
      {
        if |state.store| > 0 {
          var nextRng3, pickSeed := NextRand(rng);
          rng := nextRng3;
          var nextRng4, scoreSeed := NextRand(rng);
          rng := nextRng4;
          var picked := pickSeed % |state.store|;
          var doc := state.store[picked];
          var updatedDocState := DocState(scoreSeed % range);
          var stateAfterUpdate, events, ignoredQueryId2 := ProcessItem(state, DocChangeItem(doc.id, HasState(doc.state), HasState(updatedDocState)));
          state := stateAfterUpdate;
          observed := ApplyEventsToObserved(observed, events);
          summary := UpdateSummary(summary, events);
          opIndex := opIndex + 1;
          if checksEveryOps > 0 && opIndex % checksEveryOps == 0 {
            CheckObservedState(name, opIndex, state, observed);
          }
        }
        update := update + 1;
      }
      var insert := 0;
      while insert < insertsPerTick
        invariant 0 <= insert <= insertsPerTick
        invariant rng > 0
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
        decreases deletesPerTick - delete
      {
        if |state.store| > 0 {
          var nextRng6, pickSeed := NextRand(rng);
          rng := nextRng6;
          var picked := pickSeed % |state.store|;
          var doc := state.store[picked];
          var stateAfterDelete, events, ignoredQueryId4 := ProcessItem(state, DocChangeItem(doc.id, HasState(doc.state), NoState));
          state := stateAfterDelete;
          observed := ApplyEventsToObserved(observed, events);
          summary := UpdateSummary(summary, events);
          opIndex := opIndex + 1;
          if checksEveryOps > 0 && opIndex % checksEveryOps == 0 {
            CheckObservedState(name, opIndex, state, observed);
          }
        }
        delete := delete + 1;
      }
      tick := tick + 1;
    }
    CheckObservedState(name, opIndex, state, observed);
    print ""scenario "";
    print name;
    print "" passed: events="";
    print summary.eventsProcessed;
    print "", matches="";
    print summary.matchEvents;
    print "", evictions="";
    print summary.evictions;
    print "", retrievalBatches="";
    print summary.retrievalBatches;
    print "", retrievalDocs="";
    print summary.retrievalDocs;
    print ""\n"";
  }

  method Main(_noArgsParameter: seq<seq<char>>)
  {
    RunScenario(""whole-stack-small"", 42, 200, 30, 20, 10, 2, 2, 12, 8, 1);
    RunScenario(""whole-stack-benchmark-like"", 123, 800, 120, 30, 35, 8, 8, 25, 10, 100);
  }

  import opened DocsIndexModel

  import opened ThunderDbStack

  datatype ObservedQuery = ObservedQuery(id: QueryId, spec: QuerySpec, docs: seq<StoredDoc>)
}

module ThunderDbStack {
  function RefInsertEntry(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    decreases es, score, id
  {
    if |es| == 0 then
      [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then
      es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      [Entry(score, id)] + es
    else
      [es[0]] + RefInsertEntry(es[1..], score, id)
  }

  function RefRemoveEntry(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    decreases es, score, id
  {
    if |es| == 0 then
      es
    else if es[0].score == score && es[0].id == id then
      es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      es
    else
      [es[0]] + RefRemoveEntry(es[1..], score, id)
  }

  function RefCollectRangeIds(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    decreases es, minScore, maxScore, limit
  {
    if |es| == 0 || limit == 0 then
      []
    else if es[0].score < minScore then
      RefCollectRangeIds(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then
      []
    else
      [es[0].id] + RefCollectRangeIds(es[1..], minScore, maxScore, limit - 1)
  }

  function GetScore(state: DocState): Score
    decreases state
  {
    state.scoreValue
  }

  function FindStoredDocIndex(store: seq<StoredDoc>, id: DocId): int
    decreases store, id
  {
    if |store| == 0 then
      -1
    else if store[0].id == id then
      0
    else
      var idx: int := FindStoredDocIndex(store[1..], id); if idx < 0 then -1 else idx + 1
  }

  function HasDoc(store: seq<StoredDoc>, id: DocId): bool
    decreases store, id
  {
    FindStoredDocIndex(store, id) >= 0
  }

  function LookupState(store: seq<StoredDoc>, id: DocId): MaybeDocState
    decreases store, id
  {
    if |store| == 0 then
      NoState
    else if store[0].id == id then
      HasState(store[0].state)
    else
      LookupState(store[1..], id)
  }

  function PutStoredDoc(store: seq<StoredDoc>, id: DocId, state: DocState): seq<StoredDoc>
    decreases store, id, state
  {
    if |store| == 0 then
      [StoredDoc(id, state)]
    else if store[0].id == id then
      [StoredDoc(id, state)] + store[1..]
    else
      [store[0]] + PutStoredDoc(store[1..], id, state)
  }

  function RemoveStoredDoc(store: seq<StoredDoc>, id: DocId): seq<StoredDoc>
    decreases store, id
  {
    if |store| == 0 then
      []
    else if store[0].id == id then
      store[1..]
    else
      [store[0]] + RemoveStoredDoc(store[1..], id)
  }

  function ContainsId(ids: seq<DocId>, id: DocId): bool
    decreases ids, id
  {
    if |ids| == 0 then
      false
    else
      ids[0] == id || ContainsId(ids[1..], id)
  }

  function ContainsQueryId(ids: seq<QueryId>, id: QueryId): bool
    decreases ids, id
  {
    if |ids| == 0 then
      false
    else
      ids[0] == id || ContainsQueryId(ids[1..], id)
  }

  function AppendQueryIdUnique(ids: seq<QueryId>, id: QueryId): seq<QueryId>
    decreases ids, id
  {
    if ContainsQueryId(ids, id) then
      ids
    else
      ids + [id]
  }

  function AppendDocIdUnique(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if ContainsId(ids, id) then
      ids
    else
      ids + [id]
  }

  function BuildEntriesFromStore(store: seq<StoredDoc>): seq<Entry>
    decreases store
  {
    if |store| == 0 then
      []
    else
      RefInsertEntry(BuildEntriesFromStore(store[1..]), GetScore(store[0].state), store[0].id)
  }

  function VisibleForSpec(entries: seq<Entry>, spec: QuerySpec): seq<DocId>
    decreases entries, spec
  {
    RefCollectRangeIds(entries, spec.minScore, spec.maxScore, spec.limit)
  }

  function ScoreMatchesSpec(score: Score, spec: QuerySpec): bool
    decreases score, spec
  {
    spec.minScore <= score <= spec.maxScore
  }

  function EntryBefore(score1: Score, id1: DocId, score2: Score, id2: DocId): bool
    decreases score1, id1, score2, id2
  {
    score1 < score2 || (score1 == score2 && id1 < id2)
  }

  function StateMatchesSpec(state: MaybeDocState, spec: QuerySpec): bool
    decreases state, spec
  {
    match state
    case NoState() =>
      false
    case HasState(docState) =>
      ScoreMatchesSpec(GetScore(docState), spec)
  }

  function DocWouldEnterVisible(visible: seq<DocId>, limit: nat, docState: DocState, docId: DocId, store: seq<StoredDoc>): bool
    decreases visible, limit, docState, docId, store
  {
    if limit == 0 then
      false
    else if |visible| < limit then
      true
    else
      match LookupState(store, visible[|visible| - 1]) case NoState() => false case HasState(lastState) => EntryBefore(GetScore(docState), docId, GetScore(lastState), visible[|visible| - 1])
  }

  function QueryNeedsRecompute(query: QueryRuntime, store: seq<StoredDoc>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): bool
    decreases query, store, id, oldState, newState
  {
    if ContainsId(query.visible, id) then
      true
    else
      match newState case NoState() => false case HasState(docState) => ScoreMatchesSpec(GetScore(docState), query.spec) && DocWouldEnterVisible(query.visible, query.spec.limit, docState, id, store)
  }

  function RecomputeQuery(query: QueryRuntime, entries: seq<Entry>): QueryRuntime
    decreases query, entries
  {
    QueryRuntime(query.id, query.spec, VisibleForSpec(entries, query.spec))
  }

  function RecomputeQueries(queries: seq<QueryRuntime>, entries: seq<Entry>): seq<QueryRuntime>
    decreases queries, entries
  {
    if |queries| == 0 then
      []
    else
      [RecomputeQuery(queries[0], entries)] + RecomputeQueries(queries[1..], entries)
  }

  function RemoveQueryRuntime(queries: seq<QueryRuntime>, id: QueryId): seq<QueryRuntime>
    decreases queries, id
  {
    if |queries| == 0 then
      []
    else if queries[0].id == id then
      queries[1..]
    else
      [queries[0]] + RemoveQueryRuntime(queries[1..], id)
  }

  function UpdateQueriesForDocChange(queries: seq<QueryRuntime>, entries: seq<Entry>, store: seq<StoredDoc>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): seq<QueryRuntime>
    decreases queries, entries, store, id, oldState, newState
  {
    if |queries| == 0 then
      []
    else if QueryNeedsRecompute(queries[0], store, id, oldState, newState) then
      [RecomputeQuery(queries[0], entries)] + UpdateQueriesForDocChange(queries[1..], entries, store, id, oldState, newState)
    else
      [queries[0]] + UpdateQueriesForDocChange(queries[1..], entries, store, id, oldState, newState)
  }

  function QueryVisible(queries: seq<QueryRuntime>, id: QueryId): seq<DocId>
    decreases queries, id
  {
    if |queries| == 0 then
      []
    else if queries[0].id == id then
      queries[0].visible
    else
      QueryVisible(queries[1..], id)
  }

  function UniqueStoreIds(store: seq<StoredDoc>): bool
    decreases store
  {
    if |store| == 0 then
      true
    else
      !HasDoc(store[1..], store[0].id) && UniqueStoreIds(store[1..])
  }

  predicate QuerysConsistent(queries: seq<QueryRuntime>, entries: seq<Entry>)
    decreases queries, entries
  {
    if |queries| == 0 then
      true
    else
      queries[0].visible == VisibleForSpec(entries, queries[0].spec) && QuerysConsistent(queries[1..], entries)
  }

  predicate ValidState(state: EngineState)
    decreases state
  {
    UniqueStoreIds(state.store) &&
    state.entries == BuildEntriesFromStore(state.store) &&
    QuerysConsistent(state.queries, state.entries)
  }

  function EmptyState(): EngineState
  {
    EngineState([], [], [], 1)
  }

  function AddRetrievalQuery(plans: seq<RetrievalDoc>, docId: DocId, state: DocState, queryId: QueryId): seq<RetrievalDoc>
    decreases plans, docId, state, queryId
  {
    if |plans| == 0 then
      [RetrievalDoc(docId, state, [queryId])]
    else if plans[0].docId == docId then
      [RetrievalDoc(docId, state, AppendQueryIdUnique(plans[0].queries, queryId))] + plans[1..]
    else
      [plans[0]] + AddRetrievalQuery(plans[1..], docId, state, queryId)
  }

  function FirstEvicted(oldVisible: seq<DocId>, newVisible: seq<DocId>, changedId: DocId): seq<DocId>
    decreases oldVisible, newVisible, changedId
  {
    if |oldVisible| == 0 then
      []
    else if oldVisible[0] != changedId && !ContainsId(newVisible, oldVisible[0]) then
      [oldVisible[0]]
    else
      FirstEvicted(oldVisible[1..], newVisible, changedId)
  }

  function BuildRetrievalsFromQueryDiff(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, store: seq<StoredDoc>, changedId: DocId): seq<RetrievalDoc>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else
      BuildRetrievalsForQuery(newQueries[0], oldQueries[0].visible, store, changedId) + BuildRetrievalsFromQueryDiff(oldQueries[1..], newQueries[1..], store, changedId)
  }

  function BuildRetrievalsForQuery(query: QueryRuntime, oldVisible: seq<DocId>, store: seq<StoredDoc>, changedId: DocId): seq<RetrievalDoc>
    decreases |query.visible|
  {
    if |query.visible| == 0 then
      []
    else if query.visible[0] == changedId || ContainsId(oldVisible, query.visible[0]) then
      BuildRetrievalsForQuery(QueryRuntime(query.id, query.spec, query.visible[1..]), oldVisible, store, changedId)
    else
      match LookupState(store, query.visible[0]) case NoState() => BuildRetrievalsForQuery(QueryRuntime(query.id, query.spec, query.visible[1..]), oldVisible, store, changedId) case HasState(state) => AddRetrievalQuery(BuildRetrievalsForQuery(QueryRuntime(query.id, query.spec, query.visible[1..]), oldVisible, store, changedId), query.visible[0], state, query.id)
  }

  function BuildAddQueryRetrievals(visible: seq<DocId>, store: seq<StoredDoc>, queryId: QueryId): seq<RetrievalDoc>
    decreases |visible|
  {
    if |visible| == 0 then
      []
    else
      match LookupState(store, visible[0]) case NoState() => BuildAddQueryRetrievals(visible[1..], store, queryId) case HasState(docState) => AddRetrievalQuery(BuildAddQueryRetrievals(visible[1..], store, queryId), visible[0], docState, queryId)
  }

  function BuildMatchPayload(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): MatchPayload
    decreases oldQueries, newQueries, id, oldState, newState
  {
    MatchPayload(id, oldState, newState, CollectMatchesOld(oldQueries, newQueries, id), CollectMatchesNew(oldQueries, newQueries, id), CollectEvictions(oldQueries, newQueries, id))
  }

  function CollectMatchesOld(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<QueryId>
    decreases |oldQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else if ContainsId(oldQueries[0].visible, id) then
      [oldQueries[0].id] + CollectMatchesOld(oldQueries[1..], newQueries[1..], id)
    else
      CollectMatchesOld(oldQueries[1..], newQueries[1..], id)
  }

  function CollectMatchesNew(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<QueryId>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else if ContainsId(newQueries[0].visible, id) then
      [newQueries[0].id] + CollectMatchesNew(oldQueries[1..], newQueries[1..], id)
    else
      CollectMatchesNew(oldQueries[1..], newQueries[1..], id)
  }

  function CollectEvictions(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<Eviction>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else
      var oldVisible: seq<DocId> := oldQueries[0].visible; if !ContainsId(oldVisible, id) && ContainsId(newQueries[0].visible, id) && |FirstEvicted(oldVisible, newQueries[0].visible, id)| > 0 then [Eviction(newQueries[0].id, FirstEvicted(oldVisible, newQueries[0].visible, id)[0])] + CollectEvictions(oldQueries[1..], newQueries[1..], id) else CollectEvictions(oldQueries[1..], newQueries[1..], id)
  }

  function HasAnyMatchChange(payload: MatchPayload): bool
    decreases payload
  {
    |payload.matchesOld| > 0 || |payload.matchesNew| > 0 || |payload.evictions| > 0
  }

  method SeedDocs(state: EngineState, docs: seq<SeedDoc>) returns (next: EngineState)
    decreases state, docs
  {
    var store := state.store;
    var i := 0;
    while i < |docs|
      invariant 0 <= i <= |docs|
      decreases |docs| - i
    {
      store := PutStoredDoc(store, docs[i].id, docs[i].state);
      i := i + 1;
    }
    var entries := BuildEntriesFromStore(store);
    next := EngineState(store, entries, RecomputeQueries(state.queries, entries), state.nextQueryId);
  }

  method AddQuery(state: EngineState, spec: QuerySpec)
      returns (next: EngineState, events: seq<DownstreamEvent>, queryId: QueryId)
    ensures queryId == state.nextQueryId
    decreases state, spec
  {
    queryId := state.nextQueryId;
    var visible := VisibleForSpec(state.entries, spec);
    var query := QueryRuntime(queryId, spec, visible);
    next := EngineState(state.store, state.entries, state.queries + [query], state.nextQueryId + 1);
    var retrievals := BuildAddQueryRetrievals(visible, state.store, queryId);
    if |retrievals| == 0 {
      events := [];
    } else {
      events := [RetrievalEvent(retrievals)];
    }
  }

  method RemoveQuery(state: EngineState, id: QueryId)
      returns (next: EngineState, events: seq<DownstreamEvent>)
    decreases state, id
  {
    next := EngineState(state.store, state.entries, RemoveQueryRuntime(state.queries, id), state.nextQueryId);
    events := [];
  }

  method ApplyDocChange(state: EngineState, id: DocId, oldState: MaybeDocState, newState: MaybeDocState)
      returns (next: EngineState, events: seq<DownstreamEvent>)
    decreases state, id, oldState, newState
  {
    next := state;
    events := [];
    var store := state.store;
    var entries := state.entries;
    match oldState
    case {:split false} NoState() =>
      {
      }
    case {:split false} HasState(oldDoc) =>
      {
        store := RemoveStoredDoc(store, id);
        entries := RefRemoveEntry(entries, GetScore(oldDoc), id);
      }
      match newState
      case {:split false} NoState() =>
        {
        }
      case {:split false} HasState(newDoc) =>
        {
          store := PutStoredDoc(store, id, newDoc);
          entries := RefInsertEntry(entries, GetScore(newDoc), id);
        }
        var newQueries := UpdateQueriesForDocChange(state.queries, entries, store, id, oldState, newState);
        next := EngineState(store, entries, newQueries, state.nextQueryId);
        var payload := BuildMatchPayload(state.queries, newQueries, id, oldState, newState);
        var retrievals := BuildRetrievalsFromQueryDiff(state.queries, newQueries, store, id);
        if HasAnyMatchChange(payload) && |retrievals| > 0 {
          events := [MatchEvent(payload), RetrievalEvent(retrievals)];
        } else if HasAnyMatchChange(payload) {
          events := [MatchEvent(payload)];
        } else if |retrievals| > 0 {
          events := [RetrievalEvent(retrievals)];
        } else {
          events := [];
        }
  }

  method ProcessItem(state: EngineState, item: StreamItem)
      returns (next: EngineState, events: seq<DownstreamEvent>, queryId: QueryId)
    decreases state, item
  {
    next := state;
    events := [];
    queryId := 0;
    match item
    case {:split false} SeedDocsItem(docs) =>
      {
        next := SeedDocs(state, docs);
        events := [];
      }
    case {:split false} QueryAddItem(spec) =>
      {
        next, events, queryId := AddQuery(state, spec);
      }
    case {:split false} QueryRemoveItem(id) =>
      {
        next, events := RemoveQuery(state, id);
      }
    case {:split false} DocChangeItem(id, oldState, newState) =>
      {
        next, events := ApplyDocChange(state, id, oldState, newState);
      }
  }

  function SummaryZero(): WorkerRunSummary
  {
    WorkerRunSummary(0, 0, 0, 0, 0)
  }

  function CountEvictions(evictions: seq<Eviction>): nat
    decreases evictions
  {
    |evictions|
  }

  function UpdateSummary(summary: WorkerRunSummary, events: seq<DownstreamEvent>): WorkerRunSummary
    decreases summary, events
  {
    if |events| == 0 then
      WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed + 1)
    else
      UpdateSummaryOne(WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed + 1), events)
  }

  function UpdateSummaryOne(summary: WorkerRunSummary, events: seq<DownstreamEvent>): WorkerRunSummary
    decreases |events|
  {
    if |events| == 0 then
      summary
    else
      match events[0] case MatchEvent(payload) => UpdateSummaryOne(WorkerRunSummary(summary.matchEvents + 1, summary.evictions + CountEvictions(payload.evictions), summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed), events[1..]) case RetrievalEvent(docs) => UpdateSummaryOne(WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches + 1, summary.retrievalDocs + |docs|, summary.eventsProcessed), events[1..])
  }

  import opened DocsIndexModel

  type QueryId = int

  datatype DocState = DocState(scoreValue: Score)

  datatype MaybeDocState = NoState | HasState(state: DocState)

  datatype StoredDoc = StoredDoc(id: DocId, state: DocState)

  datatype SeedDoc = SeedDoc(id: DocId, state: DocState)

  datatype QuerySpec = QuerySpec(minScore: Score, maxScore: Score, limit: nat)

  datatype QueryRuntime = QueryRuntime(id: QueryId, spec: QuerySpec, visible: seq<DocId>)

  datatype Eviction = Eviction(queryId: QueryId, docId: DocId)

  datatype MatchPayload = MatchPayload(docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, matchesOld: seq<QueryId>, matchesNew: seq<QueryId>, evictions: seq<Eviction>)

  datatype RetrievalDoc = RetrievalDoc(docId: DocId, state: DocState, queries: seq<QueryId>)

  datatype DownstreamEvent = MatchEvent(payload: MatchPayload) | RetrievalEvent(docs: seq<RetrievalDoc>)

  datatype StreamItem = DocChangeItem(id: DocId, oldState: MaybeDocState, newState: MaybeDocState) | QueryAddItem(spec: QuerySpec) | QueryRemoveItem(id: QueryId) | SeedDocsItem(docs: seq<SeedDoc>)

  datatype WorkerRunSummary = WorkerRunSummary(matchEvents: nat, evictions: nat, retrievalBatches: nat, retrievalDocs: nat, eventsProcessed: nat)

  datatype EngineState = EngineState(store: seq<StoredDoc>, entries: seq<Entry>, queries: seq<QueryRuntime>, nextQueryId: QueryId)
}

module DocsIndexModel {
  function LexLt(a: Entry, b: Entry): bool
    decreases a, b
  {
    a.score < b.score || (a.score == b.score && a.id < b.id)
  }

  predicate SortedEntries(es: seq<Entry>)
    decreases es
  {
    forall i: int, j: int {:trigger es[j], es[i]} :: 
      0 <= i < j < |es| ==>
        LexLt(es[i], es[j])
  }

  function CountStrictLessScore(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score < score then 1 else 0) + CountStrictLessScore(es[1..], score)
  }

  function CountAtMost(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score <= score then 1 else 0) + CountAtMost(es[1..], score)
  }

  function RankWithId(es: seq<Entry>, score: Score, id: DocId): nat
    decreases es, score, id
  {
    if |es| == 0 then
      0
    else if es[0].score < score || (es[0].score == score && es[0].id < id) then
      1 + RankWithId(es[1..], score, id)
    else
      0
  }

  function Rank(es: seq<Entry>, score: Score, id: MaybeDocId): nat
    decreases es, score, id
  {
    match id
    case NoDoc() =>
      CountStrictLessScore(es, score)
    case SomeDoc(doc) =>
      RankWithId(es, score, doc)
  }

  function InsertUnique(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    decreases es, score, id
  {
    if |es| == 0 then
      [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then
      es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      [Entry(score, id)] + es
    else
      [es[0]] + InsertUnique(es[1..], score, id)
  }

  function RemoveOne(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    decreases es, score, id
  {
    if |es| == 0 then
      es
    else if es[0].score == score && es[0].id == id then
      es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      es
    else
      [es[0]] + RemoveOne(es[1..], score, id)
  }

  function PositionAt(es: seq<Entry>, idx: nat): nat
    requires SortedEntries(es)
    requires idx < |es|
    decreases es, idx
  {
    if idx == 0 then
      0
    else if es[idx - 1].score == es[idx].score then
      1 + PositionAt(es, idx - 1)
    else
      0
  }

  function GetAtRank(es: seq<Entry>, rank: nat): AtRank
    requires SortedEntries(es)
    decreases es, rank
  {
    if rank >= |es| then
      Missing
    else
      Found(es[rank].score, es[rank].id, PositionAt(es, rank))
  }

  function CollectRange(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SortedEntries(es)
    decreases es, minScore, maxScore, limit
  {
    if |es| == 0 || limit == 0 then
      []
    else if es[0].score < minScore then
      CollectRange(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then
      []
    else
      [es[0].id] + CollectRange(es[1..], minScore, maxScore, limit - 1)
  }

  lemma /*{:_inductionTrigger CountStrictLessScore(es, score)}*/ /*{:_inductionTrigger Rank(es, score, MaybeDocId.NoDoc)}*/ /*{:_induction es, score}*/ RankNoDocMatchesPrefix(es: seq<Entry>, score: Score)
    ensures Rank(es, score, NoDoc) == CountStrictLessScore(es, score)
    decreases es, score
  {
  }

  lemma RankWithinBounds(es: seq<Entry>, score: Score, id: MaybeDocId)
    ensures Rank(es, score, id) <= |es|
    decreases es, score, id
  {
    match id
    case {:split false} NoDoc() =>
      CountStrictLessWithinBounds(es, score);
    case {:split false} SomeDoc(doc) =>
      RankWithIdWithinBounds(es, score, doc);
  }

  lemma /*{:_inductionTrigger CountStrictLessScore(es, score)}*/ /*{:_induction es, score}*/ CountStrictLessWithinBounds(es: seq<Entry>, score: Score)
    ensures CountStrictLessScore(es, score) <= |es|
    decreases es, score
  {
    if |es| == 0 {
    } else {
      CountStrictLessWithinBounds(es[1..], score);
      if es[0].score < score {
        assert CountStrictLessScore(es, score) == 1 + CountStrictLessScore(es[1..], score);
        assert |es| == 1 + |es[1..]|;
      }
    }
  }

  lemma /*{:_inductionTrigger RankWithId(es, score, id)}*/ /*{:_induction es, score, id}*/ RankWithIdWithinBounds(es: seq<Entry>, score: Score, id: DocId)
    ensures RankWithId(es, score, id) <= |es|
    decreases es, score, id
  {
    if |es| == 0 {
    } else if es[0].score < score || (es[0].score == score && es[0].id < id) {
      RankWithIdWithinBounds(es[1..], score, id);
      assert RankWithId(es, score, id) == 1 + RankWithId(es[1..], score, id);
      assert |es| == 1 + |es[1..]|;
    }
  }

  lemma /*{:_inductionTrigger CountAtMost(es, hi), CountAtMost(es, lo)}*/ /*{:_induction es, lo, hi}*/ CountAtMostMonotone(es: seq<Entry>, lo: Score, hi: Score)
    requires lo <= hi
    ensures CountAtMost(es, lo) <= CountAtMost(es, hi)
    decreases es, lo, hi
  {
    if |es| == 0 {
    } else {
      CountAtMostMonotone(es[1..], lo, hi);
      if es[0].score <= lo {
        assert es[0].score <= hi;
      }
    }
  }

  type Score = int

  type DocId = int

  datatype MaybeDocId = NoDoc | SomeDoc(doc: DocId)

  datatype AtRank = Missing | Found(score: Score, id: DocId, position: nat)

  datatype Entry = Entry(score: Score, id: DocId)
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      // Be sure to use ElementCount to avoid casting into 32 bits
      // integers that could lead to overflows (see https://github.com/dafny-lang/dafny/issues/5554)
      return th.ElementCount < other.ElementCount && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    internal volatile ISequence<T> left, right;
    internal ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    internal ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
// end of class FuncExtensions
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
}
// end of class FuncExtensions
namespace DocsIndexModel {

  public partial class __default {
    public static bool LexLt(DocsIndexModel._IEntry a, DocsIndexModel._IEntry b)
    {
      return (((a).dtor_score) < ((b).dtor_score)) || ((((a).dtor_score) == ((b).dtor_score)) && (((a).dtor_id) < ((b).dtor_id)));
    }
    public static bool SortedEntries(Dafny.ISequence<DocsIndexModel._IEntry> es) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DocsIndexModel._IEntry>, bool>>((_0_es) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_0_es).Count)), true, (((_forall_var_0) => {
        BigInteger _1_i = (BigInteger)_forall_var_0;
        return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_1_i) + (BigInteger.One), new BigInteger((_0_es).Count)), true, (((_forall_var_1) => {
          BigInteger _2_j = (BigInteger)_forall_var_1;
          return !((((_1_i).Sign != -1) && ((_1_i) < (_2_j))) && ((_2_j) < (new BigInteger((_0_es).Count)))) || (DocsIndexModel.__default.LexLt((_0_es).Select(_1_i), (_0_es).Select(_2_j)));
        })));
      }))))(es);
    }
    public static BigInteger CountStrictLessScore(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) < (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger CountAtMost(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) <= (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger RankWithId(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) < (score)) || (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) < (id)))) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static BigInteger Rank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, DocsIndexModel._IMaybeDocId id)
    {
      DocsIndexModel._IMaybeDocId _source0 = id;
      {
        if (_source0.is_NoDoc) {
          return DocsIndexModel.__default.CountStrictLessScore(es, score);
        }
      }
      {
        BigInteger _0_doc = _source0.dtor_doc;
        return DocsIndexModel.__default.RankWithId(es, score, _0_doc);
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> InsertUnique(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)));
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.Concat(Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)), es));
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> RemoveOne(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, (es).Drop(BigInteger.One));
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger PositionAt(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger idx)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((idx).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if ((((es).Select((idx) - (BigInteger.One))).dtor_score) == (((es).Select(idx)).dtor_score)) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = es;
        BigInteger _in1 = (idx) - (BigInteger.One);
        es = _in0;
        idx = _in1;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static DocsIndexModel._IAtRank GetAtRank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger rank)
    {
      if ((rank) >= (new BigInteger((es).Count))) {
        return DocsIndexModel.AtRank.create_Missing();
      } else {
        return DocsIndexModel.AtRank.create_Found(((es).Select(rank)).dtor_score, ((es).Select(rank)).dtor_id, DocsIndexModel.__default.PositionAt(es, rank));
      }
    }
    public static Dafny.ISequence<BigInteger> CollectRange(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((es).Count)).Sign == 0) || ((limit).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) < (minScore)) {
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = minScore;
        BigInteger _in2 = maxScore;
        BigInteger _in3 = limit;
        es = _in0;
        minScore = _in1;
        maxScore = _in2;
        limit = _in3;
        goto TAIL_CALL_START;
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) > (maxScore)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((es).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<DocsIndexModel._IEntry> _in4 = (es).Drop(BigInteger.One);
        BigInteger _in5 = minScore;
        BigInteger _in6 = maxScore;
        BigInteger _in7 = (limit) - (BigInteger.One);
        es = _in4;
        minScore = _in5;
        maxScore = _in6;
        limit = _in7;
        goto TAIL_CALL_START;
      }
    }
  }

  public interface _IMaybeDocId {
    bool is_NoDoc { get; }
    bool is_SomeDoc { get; }
    BigInteger dtor_doc { get; }
    _IMaybeDocId DowncastClone();
  }
  public abstract class MaybeDocId : _IMaybeDocId {
    public MaybeDocId() {
    }
    private static readonly DocsIndexModel._IMaybeDocId theDefault = create_NoDoc();
    public static DocsIndexModel._IMaybeDocId Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId>(DocsIndexModel.MaybeDocId.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaybeDocId create_NoDoc() {
      return new MaybeDocId_NoDoc();
    }
    public static _IMaybeDocId create_SomeDoc(BigInteger doc) {
      return new MaybeDocId_SomeDoc(doc);
    }
    public bool is_NoDoc { get { return this is MaybeDocId_NoDoc; } }
    public bool is_SomeDoc { get { return this is MaybeDocId_SomeDoc; } }
    public BigInteger dtor_doc {
      get {
        var d = this;
        return ((MaybeDocId_SomeDoc)d)._doc;
      }
    }
    public abstract _IMaybeDocId DowncastClone();
  }
  public class MaybeDocId_NoDoc : MaybeDocId {
    public MaybeDocId_NoDoc() : base() {
    }
    public override _IMaybeDocId DowncastClone() {
      if (this is _IMaybeDocId dt) { return dt; }
      return new MaybeDocId_NoDoc();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.MaybeDocId_NoDoc;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.MaybeDocId.NoDoc";
      return s;
    }
  }
  public class MaybeDocId_SomeDoc : MaybeDocId {
    public readonly BigInteger _doc;
    public MaybeDocId_SomeDoc(BigInteger doc) : base() {
      this._doc = doc;
    }
    public override _IMaybeDocId DowncastClone() {
      if (this is _IMaybeDocId dt) { return dt; }
      return new MaybeDocId_SomeDoc(_doc);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.MaybeDocId_SomeDoc;
      return oth != null && this._doc == oth._doc;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._doc));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.MaybeDocId.SomeDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._doc);
      s += ")";
      return s;
    }
  }

  public interface _IAtRank {
    bool is_Missing { get; }
    bool is_Found { get; }
    BigInteger dtor_score { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_position { get; }
    _IAtRank DowncastClone();
  }
  public abstract class AtRank : _IAtRank {
    public AtRank() {
    }
    private static readonly DocsIndexModel._IAtRank theDefault = create_Missing();
    public static DocsIndexModel._IAtRank Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IAtRank> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IAtRank>(DocsIndexModel.AtRank.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IAtRank> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAtRank create_Missing() {
      return new AtRank_Missing();
    }
    public static _IAtRank create_Found(BigInteger score, BigInteger id, BigInteger position) {
      return new AtRank_Found(score, id, position);
    }
    public bool is_Missing { get { return this is AtRank_Missing; } }
    public bool is_Found { get { return this is AtRank_Found; } }
    public BigInteger dtor_score {
      get {
        var d = this;
        return ((AtRank_Found)d)._score;
      }
    }
    public BigInteger dtor_id {
      get {
        var d = this;
        return ((AtRank_Found)d)._id;
      }
    }
    public BigInteger dtor_position {
      get {
        var d = this;
        return ((AtRank_Found)d)._position;
      }
    }
    public abstract _IAtRank DowncastClone();
  }
  public class AtRank_Missing : AtRank {
    public AtRank_Missing() : base() {
    }
    public override _IAtRank DowncastClone() {
      if (this is _IAtRank dt) { return dt; }
      return new AtRank_Missing();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.AtRank_Missing;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.AtRank.Missing";
      return s;
    }
  }
  public class AtRank_Found : AtRank {
    public readonly BigInteger _score;
    public readonly BigInteger _id;
    public readonly BigInteger _position;
    public AtRank_Found(BigInteger score, BigInteger id, BigInteger position) : base() {
      this._score = score;
      this._id = id;
      this._position = position;
    }
    public override _IAtRank DowncastClone() {
      if (this is _IAtRank dt) { return dt; }
      return new AtRank_Found(_score, _id, _position);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.AtRank_Found;
      return oth != null && this._score == oth._score && this._id == oth._id && this._position == oth._position;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._score));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._position));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.AtRank.Found";
      s += "(";
      s += Dafny.Helpers.ToString(this._score);
      s += ", ";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._position);
      s += ")";
      return s;
    }
  }

  public interface _IEntry {
    bool is_Entry { get; }
    BigInteger dtor_score { get; }
    BigInteger dtor_id { get; }
    _IEntry DowncastClone();
  }
  public class Entry : _IEntry {
    public readonly BigInteger _score;
    public readonly BigInteger _id;
    public Entry(BigInteger score, BigInteger id) {
      this._score = score;
      this._id = id;
    }
    public _IEntry DowncastClone() {
      if (this is _IEntry dt) { return dt; }
      return new Entry(_score, _id);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.Entry;
      return oth != null && this._score == oth._score && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._score));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.Entry.Entry";
      s += "(";
      s += Dafny.Helpers.ToString(this._score);
      s += ", ";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
    private static readonly DocsIndexModel._IEntry theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static DocsIndexModel._IEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IEntry> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IEntry>(DocsIndexModel.Entry.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEntry create(BigInteger score, BigInteger id) {
      return new Entry(score, id);
    }
    public static _IEntry create_Entry(BigInteger score, BigInteger id) {
      return create(score, id);
    }
    public bool is_Entry { get { return true; } }
    public BigInteger dtor_score {
      get {
        return this._score;
      }
    }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
  }
} // end of namespace DocsIndexModel
namespace ThunderDbStack {

  public partial class __default {
    public static Dafny.ISequence<DocsIndexModel._IEntry> RefInsertEntry(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)));
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.Concat(Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)), es));
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> RefRemoveEntry(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, (es).Drop(BigInteger.One));
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> RefCollectRangeIds(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((es).Count)).Sign == 0) || ((limit).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) < (minScore)) {
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = minScore;
        BigInteger _in2 = maxScore;
        BigInteger _in3 = limit;
        es = _in0;
        minScore = _in1;
        maxScore = _in2;
        limit = _in3;
        goto TAIL_CALL_START;
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) > (maxScore)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((es).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<DocsIndexModel._IEntry> _in4 = (es).Drop(BigInteger.One);
        BigInteger _in5 = minScore;
        BigInteger _in6 = maxScore;
        BigInteger _in7 = (limit) - (BigInteger.One);
        es = _in4;
        minScore = _in5;
        maxScore = _in6;
        limit = _in7;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger GetScore(BigInteger state) {
      return (state);
    }
    public static BigInteger FindStoredDocIndex(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger id)
    {
      if ((new BigInteger((store).Count)).Sign == 0) {
        return new BigInteger(-1);
      } else if ((((store).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return BigInteger.Zero;
      } else {
        BigInteger _0_idx = ThunderDbStack.__default.FindStoredDocIndex((store).Drop(BigInteger.One), id);
        if ((_0_idx).Sign == -1) {
          return new BigInteger(-1);
        } else {
          return (_0_idx) + (BigInteger.One);
        }
      }
    }
    public static bool HasDoc(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger id)
    {
      return (ThunderDbStack.__default.FindStoredDocIndex(store, id)).Sign != -1;
    }
    public static ThunderDbStack._IMaybeDocState LookupState(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger id)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((store).Count)).Sign == 0) {
        return ThunderDbStack.MaybeDocState.create_NoState();
      } else if ((((store).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return ThunderDbStack.MaybeDocState.create_HasState(((store).Select(BigInteger.Zero)).dtor_state);
      } else {
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in0 = (store).Drop(BigInteger.One);
        BigInteger _in1 = id;
        store = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IStoredDoc> PutStoredDoc(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger id, BigInteger state)
    {
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((store).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements(ThunderDbStack.StoredDoc.create(id, state)));
      } else if ((((store).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements(ThunderDbStack.StoredDoc.create(id, state)), (store).Drop(BigInteger.One)));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements((store).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in0 = (store).Drop(BigInteger.One);
        BigInteger _in1 = id;
        BigInteger _in2 = state;
        store = _in0;
        id = _in1;
        state = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IStoredDoc> RemoveStoredDoc(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((store).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements());
      } else if ((((store).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, (store).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements((store).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in0 = (store).Drop(BigInteger.One);
        BigInteger _in1 = id;
        store = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool ContainsId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return false;
      } else {
        return (((ids).Select(BigInteger.Zero)) == (id)) || (ThunderDbStack.__default.ContainsId((ids).Drop(BigInteger.One), id));
      }
    }
    public static bool ContainsQueryId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return false;
      } else {
        return (((ids).Select(BigInteger.Zero)) == (id)) || (ThunderDbStack.__default.ContainsQueryId((ids).Drop(BigInteger.One), id));
      }
    }
    public static Dafny.ISequence<BigInteger> AppendQueryIdUnique(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if (ThunderDbStack.__default.ContainsQueryId(ids, id)) {
        return ids;
      } else {
        return Dafny.Sequence<BigInteger>.Concat(ids, Dafny.Sequence<BigInteger>.FromElements(id));
      }
    }
    public static Dafny.ISequence<BigInteger> AppendDocIdUnique(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if (ThunderDbStack.__default.ContainsId(ids, id)) {
        return ids;
      } else {
        return Dafny.Sequence<BigInteger>.Concat(ids, Dafny.Sequence<BigInteger>.FromElements(id));
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> BuildEntriesFromStore(Dafny.ISequence<ThunderDbStack._IStoredDoc> store) {
      if ((new BigInteger((store).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
      } else {
        return ThunderDbStack.__default.RefInsertEntry(ThunderDbStack.__default.BuildEntriesFromStore((store).Drop(BigInteger.One)), ThunderDbStack.__default.GetScore(((store).Select(BigInteger.Zero)).dtor_state), ((store).Select(BigInteger.Zero)).dtor_id);
      }
    }
    public static Dafny.ISequence<BigInteger> VisibleForSpec(Dafny.ISequence<DocsIndexModel._IEntry> entries, ThunderDbStack._IQuerySpec spec)
    {
      return ThunderDbStack.__default.RefCollectRangeIds(entries, (spec).dtor_minScore, (spec).dtor_maxScore, (spec).dtor_limit);
    }
    public static bool ScoreMatchesSpec(BigInteger score, ThunderDbStack._IQuerySpec spec)
    {
      return (((spec).dtor_minScore) <= (score)) && ((score) <= ((spec).dtor_maxScore));
    }
    public static bool EntryBefore(BigInteger score1, BigInteger id1, BigInteger score2, BigInteger id2)
    {
      return ((score1) < (score2)) || (((score1) == (score2)) && ((id1) < (id2)));
    }
    public static bool StateMatchesSpec(ThunderDbStack._IMaybeDocState state, ThunderDbStack._IQuerySpec spec)
    {
      ThunderDbStack._IMaybeDocState _source0 = state;
      {
        if (_source0.is_NoState) {
          return false;
        }
      }
      {
        BigInteger _0_docState = _source0.dtor_state;
        return ThunderDbStack.__default.ScoreMatchesSpec(ThunderDbStack.__default.GetScore(_0_docState), spec);
      }
    }
    public static bool DocWouldEnterVisible(Dafny.ISequence<BigInteger> visible, BigInteger limit, BigInteger docState, BigInteger docId, Dafny.ISequence<ThunderDbStack._IStoredDoc> store)
    {
      if ((limit).Sign == 0) {
        return false;
      } else if ((new BigInteger((visible).Count)) < (limit)) {
        return true;
      } else {
        ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(store, (visible).Select((new BigInteger((visible).Count)) - (BigInteger.One)));
        {
          if (_source0.is_NoState) {
            return false;
          }
        }
        {
          BigInteger _0_lastState = _source0.dtor_state;
          return ThunderDbStack.__default.EntryBefore(ThunderDbStack.__default.GetScore(docState), docId, ThunderDbStack.__default.GetScore(_0_lastState), (visible).Select((new BigInteger((visible).Count)) - (BigInteger.One)));
        }
      }
    }
    public static bool QueryNeedsRecompute(ThunderDbStack._IQueryRuntime query, Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      if (ThunderDbStack.__default.ContainsId((query).dtor_visible, id)) {
        return true;
      } else {
        ThunderDbStack._IMaybeDocState _source0 = newState;
        {
          if (_source0.is_NoState) {
            return false;
          }
        }
        {
          BigInteger _0_docState = _source0.dtor_state;
          return (ThunderDbStack.__default.ScoreMatchesSpec(ThunderDbStack.__default.GetScore(_0_docState), (query).dtor_spec)) && (ThunderDbStack.__default.DocWouldEnterVisible((query).dtor_visible, ((query).dtor_spec).dtor_limit, _0_docState, id, store));
        }
      }
    }
    public static ThunderDbStack._IQueryRuntime RecomputeQuery(ThunderDbStack._IQueryRuntime query, Dafny.ISequence<DocsIndexModel._IEntry> entries)
    {
      return ThunderDbStack.QueryRuntime.create((query).dtor_id, (query).dtor_spec, ThunderDbStack.__default.VisibleForSpec(entries, (query).dtor_spec));
    }
    public static Dafny.ISequence<ThunderDbStack._IQueryRuntime> RecomputeQueries(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, Dafny.ISequence<DocsIndexModel._IEntry> entries)
    {
      Dafny.ISequence<ThunderDbStack._IQueryRuntime> _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(ThunderDbStack.__default.RecomputeQuery((queries).Select(BigInteger.Zero), entries)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in1 = entries;
        queries = _in0;
        entries = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IQueryRuntime> RemoveQueryRuntime(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IQueryRuntime> _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements());
      } else if ((((queries).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, (queries).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements((queries).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        BigInteger _in1 = id;
        queries = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IQueryRuntime> UpdateQueriesForDocChange(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, Dafny.ISequence<DocsIndexModel._IEntry> entries, Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      Dafny.ISequence<ThunderDbStack._IQueryRuntime> _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements());
      } else if (ThunderDbStack.__default.QueryNeedsRecompute((queries).Select(BigInteger.Zero), store, id, oldState, newState)) {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(ThunderDbStack.__default.RecomputeQuery((queries).Select(BigInteger.Zero), entries)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in1 = entries;
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in2 = store;
        BigInteger _in3 = id;
        ThunderDbStack._IMaybeDocState _in4 = oldState;
        ThunderDbStack._IMaybeDocState _in5 = newState;
        queries = _in0;
        entries = _in1;
        store = _in2;
        id = _in3;
        oldState = _in4;
        newState = _in5;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements((queries).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in6 = (queries).Drop(BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in7 = entries;
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in8 = store;
        BigInteger _in9 = id;
        ThunderDbStack._IMaybeDocState _in10 = oldState;
        ThunderDbStack._IMaybeDocState _in11 = newState;
        queries = _in6;
        entries = _in7;
        store = _in8;
        id = _in9;
        oldState = _in10;
        newState = _in11;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> QueryVisible(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger id)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else if ((((queries).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return ((queries).Select(BigInteger.Zero)).dtor_visible;
      } else {
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        BigInteger _in1 = id;
        queries = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool UniqueStoreIds(Dafny.ISequence<ThunderDbStack._IStoredDoc> store) {
      if ((new BigInteger((store).Count)).Sign == 0) {
        return true;
      } else {
        return (!(ThunderDbStack.__default.HasDoc((store).Drop(BigInteger.One), ((store).Select(BigInteger.Zero)).dtor_id))) && (ThunderDbStack.__default.UniqueStoreIds((store).Drop(BigInteger.One)));
      }
    }
    public static bool QuerysConsistent(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, Dafny.ISequence<DocsIndexModel._IEntry> entries)
    {
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return true;
      } else {
        return ((((queries).Select(BigInteger.Zero)).dtor_visible).Equals(ThunderDbStack.__default.VisibleForSpec(entries, ((queries).Select(BigInteger.Zero)).dtor_spec))) && (ThunderDbStack.__default.QuerysConsistent((queries).Drop(BigInteger.One), entries));
      }
    }
    public static bool ValidState(ThunderDbStack._IEngineState state) {
      return ((ThunderDbStack.__default.UniqueStoreIds((state).dtor_store)) && (((state).dtor_entries).Equals(ThunderDbStack.__default.BuildEntriesFromStore((state).dtor_store)))) && (ThunderDbStack.__default.QuerysConsistent((state).dtor_queries, (state).dtor_entries));
    }
    public static ThunderDbStack._IEngineState EmptyState() {
      return ThunderDbStack.EngineState.create(Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements(), Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(), Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(), BigInteger.One);
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> AddRetrievalQuery(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> plans, BigInteger docId, BigInteger state, BigInteger queryId)
    {
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((plans).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(docId, state, Dafny.Sequence<BigInteger>.FromElements(queryId))));
      } else if ((((plans).Select(BigInteger.Zero)).dtor_docId) == (docId)) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(docId, state, ThunderDbStack.__default.AppendQueryIdUnique(((plans).Select(BigInteger.Zero)).dtor_queries, queryId))), (plans).Drop(BigInteger.One)));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements((plans).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _in0 = (plans).Drop(BigInteger.One);
        BigInteger _in1 = docId;
        BigInteger _in2 = state;
        BigInteger _in3 = queryId;
        plans = _in0;
        docId = _in1;
        state = _in2;
        queryId = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FirstEvicted(Dafny.ISequence<BigInteger> oldVisible, Dafny.ISequence<BigInteger> newVisible, BigInteger changedId)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((oldVisible).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else if ((((oldVisible).Select(BigInteger.Zero)) != (changedId)) && (!(ThunderDbStack.__default.ContainsId(newVisible, (oldVisible).Select(BigInteger.Zero))))) {
        return Dafny.Sequence<BigInteger>.FromElements((oldVisible).Select(BigInteger.Zero));
      } else {
        Dafny.ISequence<BigInteger> _in0 = (oldVisible).Drop(BigInteger.One);
        Dafny.ISequence<BigInteger> _in1 = newVisible;
        BigInteger _in2 = changedId;
        oldVisible = _in0;
        newVisible = _in1;
        changedId = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildRetrievalsFromQueryDiff(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger changedId)
    {
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, ThunderDbStack.__default.BuildRetrievalsForQuery((newQueries).Select(BigInteger.Zero), ((oldQueries).Select(BigInteger.Zero)).dtor_visible, store, changedId));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in2 = store;
        BigInteger _in3 = changedId;
        oldQueries = _in0;
        newQueries = _in1;
        store = _in2;
        changedId = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildRetrievalsForQuery(ThunderDbStack._IQueryRuntime query, Dafny.ISequence<BigInteger> oldVisible, Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger changedId)
    {
      if ((new BigInteger(((query).dtor_visible).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      } else if (((((query).dtor_visible).Select(BigInteger.Zero)) == (changedId)) || (ThunderDbStack.__default.ContainsId(oldVisible, ((query).dtor_visible).Select(BigInteger.Zero)))) {
        return ThunderDbStack.__default.BuildRetrievalsForQuery(ThunderDbStack.QueryRuntime.create((query).dtor_id, (query).dtor_spec, ((query).dtor_visible).Drop(BigInteger.One)), oldVisible, store, changedId);
      } else {
        ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(store, ((query).dtor_visible).Select(BigInteger.Zero));
        {
          if (_source0.is_NoState) {
            return ThunderDbStack.__default.BuildRetrievalsForQuery(ThunderDbStack.QueryRuntime.create((query).dtor_id, (query).dtor_spec, ((query).dtor_visible).Drop(BigInteger.One)), oldVisible, store, changedId);
          }
        }
        {
          BigInteger _0_state = _source0.dtor_state;
          return ThunderDbStack.__default.AddRetrievalQuery(ThunderDbStack.__default.BuildRetrievalsForQuery(ThunderDbStack.QueryRuntime.create((query).dtor_id, (query).dtor_spec, ((query).dtor_visible).Drop(BigInteger.One)), oldVisible, store, changedId), ((query).dtor_visible).Select(BigInteger.Zero), _0_state, (query).dtor_id);
        }
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildAddQueryRetrievals(Dafny.ISequence<BigInteger> visible, Dafny.ISequence<ThunderDbStack._IStoredDoc> store, BigInteger queryId)
    {
      if ((new BigInteger((visible).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      } else {
        ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(store, (visible).Select(BigInteger.Zero));
        {
          if (_source0.is_NoState) {
            return ThunderDbStack.__default.BuildAddQueryRetrievals((visible).Drop(BigInteger.One), store, queryId);
          }
        }
        {
          BigInteger _0_docState = _source0.dtor_state;
          return ThunderDbStack.__default.AddRetrievalQuery(ThunderDbStack.__default.BuildAddQueryRetrievals((visible).Drop(BigInteger.One), store, queryId), (visible).Select(BigInteger.Zero), _0_docState, queryId);
        }
      }
    }
    public static ThunderDbStack._IMatchPayload BuildMatchPayload(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      return ThunderDbStack.MatchPayload.create(id, oldState, newState, ThunderDbStack.__default.CollectMatchesOld(oldQueries, newQueries, id), ThunderDbStack.__default.CollectMatchesNew(oldQueries, newQueries, id), ThunderDbStack.__default.CollectEvictions(oldQueries, newQueries, id));
    }
    public static Dafny.ISequence<BigInteger> CollectMatchesOld(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (ThunderDbStack.__default.ContainsId(((oldQueries).Select(BigInteger.Zero)).dtor_visible, id)) {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((oldQueries).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
        BigInteger _in2 = id;
        oldQueries = _in0;
        newQueries = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in3 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in4 = (newQueries).Drop(BigInteger.One);
        BigInteger _in5 = id;
        oldQueries = _in3;
        newQueries = _in4;
        id = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> CollectMatchesNew(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (ThunderDbStack.__default.ContainsId(((newQueries).Select(BigInteger.Zero)).dtor_visible, id)) {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((newQueries).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
        BigInteger _in2 = id;
        oldQueries = _in0;
        newQueries = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in3 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in4 = (newQueries).Drop(BigInteger.One);
        BigInteger _in5 = id;
        oldQueries = _in3;
        newQueries = _in4;
        id = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IEviction> CollectEvictions(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IEviction> _0___accumulator = Dafny.Sequence<ThunderDbStack._IEviction>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<ThunderDbStack._IEviction>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements());
      } else {
        Dafny.ISequence<BigInteger> _1_oldVisible = ((oldQueries).Select(BigInteger.Zero)).dtor_visible;
        if (((!(ThunderDbStack.__default.ContainsId(_1_oldVisible, id))) && (ThunderDbStack.__default.ContainsId(((newQueries).Select(BigInteger.Zero)).dtor_visible, id))) && ((new BigInteger((ThunderDbStack.__default.FirstEvicted(_1_oldVisible, ((newQueries).Select(BigInteger.Zero)).dtor_visible, id)).Count)).Sign == 1)) {
          _0___accumulator = Dafny.Sequence<ThunderDbStack._IEviction>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements(ThunderDbStack.Eviction.create(((newQueries).Select(BigInteger.Zero)).dtor_id, (ThunderDbStack.__default.FirstEvicted(_1_oldVisible, ((newQueries).Select(BigInteger.Zero)).dtor_visible, id)).Select(BigInteger.Zero))));
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
          BigInteger _in2 = id;
          oldQueries = _in0;
          newQueries = _in1;
          id = _in2;
          goto TAIL_CALL_START;
        } else {
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in3 = (oldQueries).Drop(BigInteger.One);
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in4 = (newQueries).Drop(BigInteger.One);
          BigInteger _in5 = id;
          oldQueries = _in3;
          newQueries = _in4;
          id = _in5;
          goto TAIL_CALL_START;
        }
      }
    }
    public static bool HasAnyMatchChange(ThunderDbStack._IMatchPayload payload) {
      return (((new BigInteger(((payload).dtor_matchesOld).Count)).Sign == 1) || ((new BigInteger(((payload).dtor_matchesNew).Count)).Sign == 1)) || ((new BigInteger(((payload).dtor_evictions).Count)).Sign == 1);
    }
    public static ThunderDbStack._IEngineState SeedDocs(ThunderDbStack._IEngineState state, Dafny.ISequence<ThunderDbStack._ISeedDoc> docs)
    {
      ThunderDbStack._IEngineState next = ThunderDbStack.EngineState.Default();
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _0_store;
      _0_store = (state).dtor_store;
      BigInteger _1_i;
      _1_i = BigInteger.Zero;
      while ((_1_i) < (new BigInteger((docs).Count))) {
        _0_store = ThunderDbStack.__default.PutStoredDoc(_0_store, ((docs).Select(_1_i)).dtor_id, ((docs).Select(_1_i)).dtor_state);
        _1_i = (_1_i) + (BigInteger.One);
      }
      Dafny.ISequence<DocsIndexModel._IEntry> _2_entries;
      _2_entries = ThunderDbStack.__default.BuildEntriesFromStore(_0_store);
      next = ThunderDbStack.EngineState.create(_0_store, _2_entries, ThunderDbStack.__default.RecomputeQueries((state).dtor_queries, _2_entries), (state).dtor_nextQueryId);
      return next;
    }
    public static void AddQuery(ThunderDbStack._IEngineState state, ThunderDbStack._IQuerySpec spec, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events, out BigInteger queryId)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      queryId = BigInteger.Zero;
      queryId = (state).dtor_nextQueryId;
      Dafny.ISequence<BigInteger> _0_visible;
      _0_visible = ThunderDbStack.__default.VisibleForSpec((state).dtor_entries, spec);
      ThunderDbStack._IQueryRuntime _1_query;
      _1_query = ThunderDbStack.QueryRuntime.create(queryId, spec, _0_visible);
      next = ThunderDbStack.EngineState.create((state).dtor_store, (state).dtor_entries, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat((state).dtor_queries, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(_1_query)), ((state).dtor_nextQueryId) + (BigInteger.One));
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _2_retrievals;
      _2_retrievals = ThunderDbStack.__default.BuildAddQueryRetrievals(_0_visible, (state).dtor_store, queryId);
      if ((new BigInteger((_2_retrievals).Count)).Sign == 0) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      } else {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_2_retrievals));
      }
    }
    public static void RemoveQuery(ThunderDbStack._IEngineState state, BigInteger id, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      next = ThunderDbStack.EngineState.create((state).dtor_store, (state).dtor_entries, ThunderDbStack.__default.RemoveQueryRuntime((state).dtor_queries, id), (state).dtor_nextQueryId);
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
    }
    public static void ApplyDocChange(ThunderDbStack._IEngineState state, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      next = state;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _0_store;
      _0_store = (state).dtor_store;
      Dafny.ISequence<DocsIndexModel._IEntry> _1_entries;
      _1_entries = (state).dtor_entries;
      ThunderDbStack._IMaybeDocState _source0 = oldState;
      {
        if (_source0.is_NoState) {
          goto after_match0;
        }
      }
      {
        BigInteger _2_oldDoc = _source0.dtor_state;
        {
          _0_store = ThunderDbStack.__default.RemoveStoredDoc(_0_store, id);
          _1_entries = ThunderDbStack.__default.RefRemoveEntry(_1_entries, ThunderDbStack.__default.GetScore(_2_oldDoc), id);
        }
        ThunderDbStack._IMaybeDocState _source1 = newState;
        {
          if (_source1.is_NoState) {
            goto after_match1;
          }
        }
        {
          BigInteger _3_newDoc = _source1.dtor_state;
          {
            _0_store = ThunderDbStack.__default.PutStoredDoc(_0_store, id, _3_newDoc);
            _1_entries = ThunderDbStack.__default.RefInsertEntry(_1_entries, ThunderDbStack.__default.GetScore(_3_newDoc), id);
          }
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _4_newQueries;
          _4_newQueries = ThunderDbStack.__default.UpdateQueriesForDocChange((state).dtor_queries, _1_entries, _0_store, id, oldState, newState);
          next = ThunderDbStack.EngineState.create(_0_store, _1_entries, _4_newQueries, (state).dtor_nextQueryId);
          ThunderDbStack._IMatchPayload _5_payload;
          _5_payload = ThunderDbStack.__default.BuildMatchPayload((state).dtor_queries, _4_newQueries, id, oldState, newState);
          Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _6_retrievals;
          _6_retrievals = ThunderDbStack.__default.BuildRetrievalsFromQueryDiff((state).dtor_queries, _4_newQueries, _0_store, id);
          if ((ThunderDbStack.__default.HasAnyMatchChange(_5_payload)) && ((new BigInteger((_6_retrievals).Count)).Sign == 1)) {
            events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(_5_payload), ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_6_retrievals));
          } else if (ThunderDbStack.__default.HasAnyMatchChange(_5_payload)) {
            events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(_5_payload));
          } else if ((new BigInteger((_6_retrievals).Count)).Sign == 1) {
            events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_6_retrievals));
          } else {
            events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
          }
        }
      after_match1: ;
      }
    after_match0: ;
    }
    public static void ProcessItem(ThunderDbStack._IEngineState state, ThunderDbStack._IStreamItem item, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events, out BigInteger queryId)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      queryId = BigInteger.Zero;
      next = state;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      queryId = BigInteger.Zero;
      ThunderDbStack._IStreamItem _source0 = item;
      {
        if (_source0.is_SeedDocsItem) {
          Dafny.ISequence<ThunderDbStack._ISeedDoc> _0_docs = _source0.dtor_docs;
          {
            ThunderDbStack._IEngineState _out0;
            _out0 = ThunderDbStack.__default.SeedDocs(state, _0_docs);
            next = _out0;
            events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_QueryAddItem) {
          ThunderDbStack._IQuerySpec _1_spec = _source0.dtor_spec;
          {
            ThunderDbStack._IEngineState _out1;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out2;
            BigInteger _out3;
            ThunderDbStack.__default.AddQuery(state, _1_spec, out _out1, out _out2, out _out3);
            next = _out1;
            events = _out2;
            queryId = _out3;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_QueryRemoveItem) {
          BigInteger _2_id = _source0.dtor_id;
          {
            ThunderDbStack._IEngineState _out4;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out5;
            ThunderDbStack.__default.RemoveQuery(state, _2_id, out _out4, out _out5);
            next = _out4;
            events = _out5;
          }
          goto after_match0;
        }
      }
      {
        BigInteger _3_id = _source0.dtor_id;
        ThunderDbStack._IMaybeDocState _4_oldState = _source0.dtor_oldState;
        ThunderDbStack._IMaybeDocState _5_newState = _source0.dtor_newState;
        {
          ThunderDbStack._IEngineState _out6;
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out7;
          ThunderDbStack.__default.ApplyDocChange(state, _3_id, _4_oldState, _5_newState, out _out6, out _out7);
          next = _out6;
          events = _out7;
        }
      }
    after_match0: ;
    }
    public static ThunderDbStack._IWorkerRunSummary SummaryZero() {
      return ThunderDbStack.WorkerRunSummary.create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    }
    public static BigInteger CountEvictions(Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return new BigInteger((evictions).Count);
    }
    public static ThunderDbStack._IWorkerRunSummary UpdateSummary(ThunderDbStack._IWorkerRunSummary summary, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      if ((new BigInteger((events).Count)).Sign == 0) {
        return ThunderDbStack.WorkerRunSummary.create((summary).dtor_matchEvents, (summary).dtor_evictions, (summary).dtor_retrievalBatches, (summary).dtor_retrievalDocs, ((summary).dtor_eventsProcessed) + (BigInteger.One));
      } else {
        return ThunderDbStack.__default.UpdateSummaryOne(ThunderDbStack.WorkerRunSummary.create((summary).dtor_matchEvents, (summary).dtor_evictions, (summary).dtor_retrievalBatches, (summary).dtor_retrievalDocs, ((summary).dtor_eventsProcessed) + (BigInteger.One)), events);
      }
    }
    public static ThunderDbStack._IWorkerRunSummary UpdateSummaryOne(ThunderDbStack._IWorkerRunSummary summary, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((events).Count)).Sign == 0) {
        return summary;
      } else {
        ThunderDbStack._IDownstreamEvent _source0 = (events).Select(BigInteger.Zero);
        {
          if (_source0.is_MatchEvent) {
            ThunderDbStack._IMatchPayload _0_payload = _source0.dtor_payload;
            ThunderDbStack._IWorkerRunSummary _in0 = ThunderDbStack.WorkerRunSummary.create(((summary).dtor_matchEvents) + (BigInteger.One), ((summary).dtor_evictions) + (ThunderDbStack.__default.CountEvictions((_0_payload).dtor_evictions)), (summary).dtor_retrievalBatches, (summary).dtor_retrievalDocs, (summary).dtor_eventsProcessed);
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _in1 = (events).Drop(BigInteger.One);
            summary = _in0;
            events = _in1;
            goto TAIL_CALL_START;
          }
        }
        {
          Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _1_docs = _source0.dtor_docs;
          ThunderDbStack._IWorkerRunSummary _in2 = ThunderDbStack.WorkerRunSummary.create((summary).dtor_matchEvents, (summary).dtor_evictions, ((summary).dtor_retrievalBatches) + (BigInteger.One), ((summary).dtor_retrievalDocs) + (new BigInteger((_1_docs).Count)), (summary).dtor_eventsProcessed);
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _in3 = (events).Drop(BigInteger.One);
          summary = _in2;
          events = _in3;
          goto TAIL_CALL_START;
        }
      }
    }
  }

  public interface _IDocState {
    bool is_DocState { get; }
    BigInteger dtor_scoreValue { get; }
  }
  public class DocState : _IDocState {
    public readonly BigInteger _scoreValue;
    public DocState(BigInteger scoreValue) {
      this._scoreValue = scoreValue;
    }
    public static BigInteger DowncastClone(BigInteger _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DocState;
      return oth != null && this._scoreValue == oth._scoreValue;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._scoreValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DocState.DocState";
      s += "(";
      s += Dafny.Helpers.ToString(this._scoreValue);
      s += ")";
      return s;
    }
    private static readonly BigInteger theDefault = BigInteger.Zero;
    public static BigInteger Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDocState create(BigInteger scoreValue) {
      return new DocState(scoreValue);
    }
    public static _IDocState create_DocState(BigInteger scoreValue) {
      return create(scoreValue);
    }
    public bool is_DocState { get { return true; } }
    public BigInteger dtor_scoreValue {
      get {
        return this._scoreValue;
      }
    }
  }

  public interface _IMaybeDocState {
    bool is_NoState { get; }
    bool is_HasState { get; }
    BigInteger dtor_state { get; }
    _IMaybeDocState DowncastClone();
  }
  public abstract class MaybeDocState : _IMaybeDocState {
    public MaybeDocState() {
    }
    private static readonly ThunderDbStack._IMaybeDocState theDefault = create_NoState();
    public static ThunderDbStack._IMaybeDocState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState>(ThunderDbStack.MaybeDocState.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaybeDocState create_NoState() {
      return new MaybeDocState_NoState();
    }
    public static _IMaybeDocState create_HasState(BigInteger state) {
      return new MaybeDocState_HasState(state);
    }
    public bool is_NoState { get { return this is MaybeDocState_NoState; } }
    public bool is_HasState { get { return this is MaybeDocState_HasState; } }
    public BigInteger dtor_state {
      get {
        var d = this;
        return ((MaybeDocState_HasState)d)._state;
      }
    }
    public abstract _IMaybeDocState DowncastClone();
  }
  public class MaybeDocState_NoState : MaybeDocState {
    public MaybeDocState_NoState() : base() {
    }
    public override _IMaybeDocState DowncastClone() {
      if (this is _IMaybeDocState dt) { return dt; }
      return new MaybeDocState_NoState();
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MaybeDocState_NoState;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MaybeDocState.NoState";
      return s;
    }
  }
  public class MaybeDocState_HasState : MaybeDocState {
    public readonly BigInteger _state;
    public MaybeDocState_HasState(BigInteger state) : base() {
      this._state = state;
    }
    public override _IMaybeDocState DowncastClone() {
      if (this is _IMaybeDocState dt) { return dt; }
      return new MaybeDocState_HasState(_state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MaybeDocState_HasState;
      return oth != null && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MaybeDocState.HasState";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
  }

  public interface _IStoredDoc {
    bool is_StoredDoc { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_state { get; }
    _IStoredDoc DowncastClone();
  }
  public class StoredDoc : _IStoredDoc {
    public readonly BigInteger _id;
    public readonly BigInteger _state;
    public StoredDoc(BigInteger id, BigInteger state) {
      this._id = id;
      this._state = state;
    }
    public _IStoredDoc DowncastClone() {
      if (this is _IStoredDoc dt) { return dt; }
      return new StoredDoc(_id, _state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StoredDoc;
      return oth != null && this._id == oth._id && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StoredDoc.StoredDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IStoredDoc theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IStoredDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IStoredDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IStoredDoc>(ThunderDbStack.StoredDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IStoredDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStoredDoc create(BigInteger id, BigInteger state) {
      return new StoredDoc(id, state);
    }
    public static _IStoredDoc create_StoredDoc(BigInteger id, BigInteger state) {
      return create(id, state);
    }
    public bool is_StoredDoc { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
  }

  public interface _ISeedDoc {
    bool is_SeedDoc { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_state { get; }
    _ISeedDoc DowncastClone();
  }
  public class SeedDoc : _ISeedDoc {
    public readonly BigInteger _id;
    public readonly BigInteger _state;
    public SeedDoc(BigInteger id, BigInteger state) {
      this._id = id;
      this._state = state;
    }
    public _ISeedDoc DowncastClone() {
      if (this is _ISeedDoc dt) { return dt; }
      return new SeedDoc(_id, _state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.SeedDoc;
      return oth != null && this._id == oth._id && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.SeedDoc.SeedDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._ISeedDoc theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._ISeedDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc>(ThunderDbStack.SeedDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISeedDoc create(BigInteger id, BigInteger state) {
      return new SeedDoc(id, state);
    }
    public static _ISeedDoc create_SeedDoc(BigInteger id, BigInteger state) {
      return create(id, state);
    }
    public bool is_SeedDoc { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
  }

  public interface _IQuerySpec {
    bool is_QuerySpec { get; }
    BigInteger dtor_minScore { get; }
    BigInteger dtor_maxScore { get; }
    BigInteger dtor_limit { get; }
    _IQuerySpec DowncastClone();
  }
  public class QuerySpec : _IQuerySpec {
    public readonly BigInteger _minScore;
    public readonly BigInteger _maxScore;
    public readonly BigInteger _limit;
    public QuerySpec(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      this._minScore = minScore;
      this._maxScore = maxScore;
      this._limit = limit;
    }
    public _IQuerySpec DowncastClone() {
      if (this is _IQuerySpec dt) { return dt; }
      return new QuerySpec(_minScore, _maxScore, _limit);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.QuerySpec;
      return oth != null && this._minScore == oth._minScore && this._maxScore == oth._maxScore && this._limit == oth._limit;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._minScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maxScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._limit));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.QuerySpec.QuerySpec";
      s += "(";
      s += Dafny.Helpers.ToString(this._minScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maxScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._limit);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IQuerySpec theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IQuerySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec>(ThunderDbStack.QuerySpec.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQuerySpec create(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      return new QuerySpec(minScore, maxScore, limit);
    }
    public static _IQuerySpec create_QuerySpec(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      return create(minScore, maxScore, limit);
    }
    public bool is_QuerySpec { get { return true; } }
    public BigInteger dtor_minScore {
      get {
        return this._minScore;
      }
    }
    public BigInteger dtor_maxScore {
      get {
        return this._maxScore;
      }
    }
    public BigInteger dtor_limit {
      get {
        return this._limit;
      }
    }
  }

  public interface _IQueryRuntime {
    bool is_QueryRuntime { get; }
    BigInteger dtor_id { get; }
    ThunderDbStack._IQuerySpec dtor_spec { get; }
    Dafny.ISequence<BigInteger> dtor_visible { get; }
    _IQueryRuntime DowncastClone();
  }
  public class QueryRuntime : _IQueryRuntime {
    public readonly BigInteger _id;
    public readonly ThunderDbStack._IQuerySpec _spec;
    public readonly Dafny.ISequence<BigInteger> _visible;
    public QueryRuntime(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<BigInteger> visible) {
      this._id = id;
      this._spec = spec;
      this._visible = visible;
    }
    public _IQueryRuntime DowncastClone() {
      if (this is _IQueryRuntime dt) { return dt; }
      return new QueryRuntime(_id, _spec, _visible);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.QueryRuntime;
      return oth != null && this._id == oth._id && object.Equals(this._spec, oth._spec) && object.Equals(this._visible, oth._visible);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._spec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visible));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.QueryRuntime.QueryRuntime";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._spec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._visible);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IQueryRuntime theDefault = create(BigInteger.Zero, ThunderDbStack.QuerySpec.Default(), Dafny.Sequence<BigInteger>.Empty);
    public static ThunderDbStack._IQueryRuntime Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IQueryRuntime> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IQueryRuntime>(ThunderDbStack.QueryRuntime.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IQueryRuntime> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryRuntime create(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<BigInteger> visible) {
      return new QueryRuntime(id, spec, visible);
    }
    public static _IQueryRuntime create_QueryRuntime(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<BigInteger> visible) {
      return create(id, spec, visible);
    }
    public bool is_QueryRuntime { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public ThunderDbStack._IQuerySpec dtor_spec {
      get {
        return this._spec;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_visible {
      get {
        return this._visible;
      }
    }
  }

  public interface _IEviction {
    bool is_Eviction { get; }
    BigInteger dtor_queryId { get; }
    BigInteger dtor_docId { get; }
    _IEviction DowncastClone();
  }
  public class Eviction : _IEviction {
    public readonly BigInteger _queryId;
    public readonly BigInteger _docId;
    public Eviction(BigInteger queryId, BigInteger docId) {
      this._queryId = queryId;
      this._docId = docId;
    }
    public _IEviction DowncastClone() {
      if (this is _IEviction dt) { return dt; }
      return new Eviction(_queryId, _docId);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.Eviction;
      return oth != null && this._queryId == oth._queryId && this._docId == oth._docId;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queryId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.Eviction.Eviction";
      s += "(";
      s += Dafny.Helpers.ToString(this._queryId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._docId);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IEviction theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IEviction Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IEviction> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IEviction>(ThunderDbStack.Eviction.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IEviction> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEviction create(BigInteger queryId, BigInteger docId) {
      return new Eviction(queryId, docId);
    }
    public static _IEviction create_Eviction(BigInteger queryId, BigInteger docId) {
      return create(queryId, docId);
    }
    public bool is_Eviction { get { return true; } }
    public BigInteger dtor_queryId {
      get {
        return this._queryId;
      }
    }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
  }

  public interface _IMatchPayload {
    bool is_MatchPayload { get; }
    BigInteger dtor_docId { get; }
    ThunderDbStack._IMaybeDocState dtor_oldState { get; }
    ThunderDbStack._IMaybeDocState dtor_newState { get; }
    Dafny.ISequence<BigInteger> dtor_matchesOld { get; }
    Dafny.ISequence<BigInteger> dtor_matchesNew { get; }
    Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions { get; }
    _IMatchPayload DowncastClone();
  }
  public class MatchPayload : _IMatchPayload {
    public readonly BigInteger _docId;
    public readonly ThunderDbStack._IMaybeDocState _oldState;
    public readonly ThunderDbStack._IMaybeDocState _newState;
    public readonly Dafny.ISequence<BigInteger> _matchesOld;
    public readonly Dafny.ISequence<BigInteger> _matchesNew;
    public readonly Dafny.ISequence<ThunderDbStack._IEviction> _evictions;
    public MatchPayload(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      this._docId = docId;
      this._oldState = oldState;
      this._newState = newState;
      this._matchesOld = matchesOld;
      this._matchesNew = matchesNew;
      this._evictions = evictions;
    }
    public _IMatchPayload DowncastClone() {
      if (this is _IMatchPayload dt) { return dt; }
      return new MatchPayload(_docId, _oldState, _newState, _matchesOld, _matchesNew, _evictions);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MatchPayload;
      return oth != null && this._docId == oth._docId && object.Equals(this._oldState, oth._oldState) && object.Equals(this._newState, oth._newState) && object.Equals(this._matchesOld, oth._matchesOld) && object.Equals(this._matchesNew, oth._matchesNew) && object.Equals(this._evictions, oth._evictions);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._oldState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._newState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchesOld));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchesNew));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._evictions));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MatchPayload.MatchPayload";
      s += "(";
      s += Dafny.Helpers.ToString(this._docId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._oldState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._newState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._matchesOld);
      s += ", ";
      s += Dafny.Helpers.ToString(this._matchesNew);
      s += ", ";
      s += Dafny.Helpers.ToString(this._evictions);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IMatchPayload theDefault = create(BigInteger.Zero, ThunderDbStack.MaybeDocState.Default(), ThunderDbStack.MaybeDocState.Default(), Dafny.Sequence<BigInteger>.Empty, Dafny.Sequence<BigInteger>.Empty, Dafny.Sequence<ThunderDbStack._IEviction>.Empty);
    public static ThunderDbStack._IMatchPayload Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload>(ThunderDbStack.MatchPayload.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMatchPayload create(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return new MatchPayload(docId, oldState, newState, matchesOld, matchesNew, evictions);
    }
    public static _IMatchPayload create_MatchPayload(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return create(docId, oldState, newState, matchesOld, matchesNew, evictions);
    }
    public bool is_MatchPayload { get { return true; } }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_oldState {
      get {
        return this._oldState;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_newState {
      get {
        return this._newState;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_matchesOld {
      get {
        return this._matchesOld;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_matchesNew {
      get {
        return this._matchesNew;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions {
      get {
        return this._evictions;
      }
    }
  }

  public interface _IRetrievalDoc {
    bool is_RetrievalDoc { get; }
    BigInteger dtor_docId { get; }
    BigInteger dtor_state { get; }
    Dafny.ISequence<BigInteger> dtor_queries { get; }
    _IRetrievalDoc DowncastClone();
  }
  public class RetrievalDoc : _IRetrievalDoc {
    public readonly BigInteger _docId;
    public readonly BigInteger _state;
    public readonly Dafny.ISequence<BigInteger> _queries;
    public RetrievalDoc(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      this._docId = docId;
      this._state = state;
      this._queries = queries;
    }
    public _IRetrievalDoc DowncastClone() {
      if (this is _IRetrievalDoc dt) { return dt; }
      return new RetrievalDoc(_docId, _state, _queries);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.RetrievalDoc;
      return oth != null && this._docId == oth._docId && this._state == oth._state && object.Equals(this._queries, oth._queries);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queries));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.RetrievalDoc.RetrievalDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._docId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queries);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IRetrievalDoc theDefault = create(BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<BigInteger>.Empty);
    public static ThunderDbStack._IRetrievalDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc>(ThunderDbStack.RetrievalDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRetrievalDoc create(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      return new RetrievalDoc(docId, state, queries);
    }
    public static _IRetrievalDoc create_RetrievalDoc(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      return create(docId, state, queries);
    }
    public bool is_RetrievalDoc { get { return true; } }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_queries {
      get {
        return this._queries;
      }
    }
  }

  public interface _IDownstreamEvent {
    bool is_MatchEvent { get; }
    bool is_RetrievalEvent { get; }
    ThunderDbStack._IMatchPayload dtor_payload { get; }
    Dafny.ISequence<ThunderDbStack._IRetrievalDoc> dtor_docs { get; }
    _IDownstreamEvent DowncastClone();
  }
  public abstract class DownstreamEvent : _IDownstreamEvent {
    public DownstreamEvent() {
    }
    private static readonly ThunderDbStack._IDownstreamEvent theDefault = create_MatchEvent(ThunderDbStack.MatchPayload.Default());
    public static ThunderDbStack._IDownstreamEvent Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent>(ThunderDbStack.DownstreamEvent.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDownstreamEvent create_MatchEvent(ThunderDbStack._IMatchPayload payload) {
      return new DownstreamEvent_MatchEvent(payload);
    }
    public static _IDownstreamEvent create_RetrievalEvent(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs) {
      return new DownstreamEvent_RetrievalEvent(docs);
    }
    public bool is_MatchEvent { get { return this is DownstreamEvent_MatchEvent; } }
    public bool is_RetrievalEvent { get { return this is DownstreamEvent_RetrievalEvent; } }
    public ThunderDbStack._IMatchPayload dtor_payload {
      get {
        var d = this;
        return ((DownstreamEvent_MatchEvent)d)._payload;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IRetrievalDoc> dtor_docs {
      get {
        var d = this;
        return ((DownstreamEvent_RetrievalEvent)d)._docs;
      }
    }
    public abstract _IDownstreamEvent DowncastClone();
  }
  public class DownstreamEvent_MatchEvent : DownstreamEvent {
    public readonly ThunderDbStack._IMatchPayload _payload;
    public DownstreamEvent_MatchEvent(ThunderDbStack._IMatchPayload payload) : base() {
      this._payload = payload;
    }
    public override _IDownstreamEvent DowncastClone() {
      if (this is _IDownstreamEvent dt) { return dt; }
      return new DownstreamEvent_MatchEvent(_payload);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DownstreamEvent_MatchEvent;
      return oth != null && object.Equals(this._payload, oth._payload);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._payload));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DownstreamEvent.MatchEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._payload);
      s += ")";
      return s;
    }
  }
  public class DownstreamEvent_RetrievalEvent : DownstreamEvent {
    public readonly Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _docs;
    public DownstreamEvent_RetrievalEvent(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs) : base() {
      this._docs = docs;
    }
    public override _IDownstreamEvent DowncastClone() {
      if (this is _IDownstreamEvent dt) { return dt; }
      return new DownstreamEvent_RetrievalEvent(_docs);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DownstreamEvent_RetrievalEvent;
      return oth != null && object.Equals(this._docs, oth._docs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DownstreamEvent.RetrievalEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._docs);
      s += ")";
      return s;
    }
  }

  public interface _IStreamItem {
    bool is_DocChangeItem { get; }
    bool is_QueryAddItem { get; }
    bool is_QueryRemoveItem { get; }
    bool is_SeedDocsItem { get; }
    BigInteger dtor_id { get; }
    ThunderDbStack._IMaybeDocState dtor_oldState { get; }
    ThunderDbStack._IMaybeDocState dtor_newState { get; }
    ThunderDbStack._IQuerySpec dtor_spec { get; }
    Dafny.ISequence<ThunderDbStack._ISeedDoc> dtor_docs { get; }
    _IStreamItem DowncastClone();
  }
  public abstract class StreamItem : _IStreamItem {
    public StreamItem() {
    }
    private static readonly ThunderDbStack._IStreamItem theDefault = create_DocChangeItem(BigInteger.Zero, ThunderDbStack.MaybeDocState.Default(), ThunderDbStack.MaybeDocState.Default());
    public static ThunderDbStack._IStreamItem Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IStreamItem> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IStreamItem>(ThunderDbStack.StreamItem.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IStreamItem> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStreamItem create_DocChangeItem(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState) {
      return new StreamItem_DocChangeItem(id, oldState, newState);
    }
    public static _IStreamItem create_QueryAddItem(ThunderDbStack._IQuerySpec spec) {
      return new StreamItem_QueryAddItem(spec);
    }
    public static _IStreamItem create_QueryRemoveItem(BigInteger id) {
      return new StreamItem_QueryRemoveItem(id);
    }
    public static _IStreamItem create_SeedDocsItem(Dafny.ISequence<ThunderDbStack._ISeedDoc> docs) {
      return new StreamItem_SeedDocsItem(docs);
    }
    public bool is_DocChangeItem { get { return this is StreamItem_DocChangeItem; } }
    public bool is_QueryAddItem { get { return this is StreamItem_QueryAddItem; } }
    public bool is_QueryRemoveItem { get { return this is StreamItem_QueryRemoveItem; } }
    public bool is_SeedDocsItem { get { return this is StreamItem_SeedDocsItem; } }
    public BigInteger dtor_id {
      get {
        var d = this;
        if (d is StreamItem_DocChangeItem) { return ((StreamItem_DocChangeItem)d)._id; }
        return ((StreamItem_QueryRemoveItem)d)._id;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_oldState {
      get {
        var d = this;
        return ((StreamItem_DocChangeItem)d)._oldState;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_newState {
      get {
        var d = this;
        return ((StreamItem_DocChangeItem)d)._newState;
      }
    }
    public ThunderDbStack._IQuerySpec dtor_spec {
      get {
        var d = this;
        return ((StreamItem_QueryAddItem)d)._spec;
      }
    }
    public Dafny.ISequence<ThunderDbStack._ISeedDoc> dtor_docs {
      get {
        var d = this;
        return ((StreamItem_SeedDocsItem)d)._docs;
      }
    }
    public abstract _IStreamItem DowncastClone();
  }
  public class StreamItem_DocChangeItem : StreamItem {
    public readonly BigInteger _id;
    public readonly ThunderDbStack._IMaybeDocState _oldState;
    public readonly ThunderDbStack._IMaybeDocState _newState;
    public StreamItem_DocChangeItem(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState) : base() {
      this._id = id;
      this._oldState = oldState;
      this._newState = newState;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_DocChangeItem(_id, _oldState, _newState);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_DocChangeItem;
      return oth != null && this._id == oth._id && object.Equals(this._oldState, oth._oldState) && object.Equals(this._newState, oth._newState);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._oldState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._newState));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.DocChangeItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._oldState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._newState);
      s += ")";
      return s;
    }
  }
  public class StreamItem_QueryAddItem : StreamItem {
    public readonly ThunderDbStack._IQuerySpec _spec;
    public StreamItem_QueryAddItem(ThunderDbStack._IQuerySpec spec) : base() {
      this._spec = spec;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_QueryAddItem(_spec);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_QueryAddItem;
      return oth != null && object.Equals(this._spec, oth._spec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._spec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.QueryAddItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._spec);
      s += ")";
      return s;
    }
  }
  public class StreamItem_QueryRemoveItem : StreamItem {
    public readonly BigInteger _id;
    public StreamItem_QueryRemoveItem(BigInteger id) : base() {
      this._id = id;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_QueryRemoveItem(_id);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_QueryRemoveItem;
      return oth != null && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.QueryRemoveItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
  }
  public class StreamItem_SeedDocsItem : StreamItem {
    public readonly Dafny.ISequence<ThunderDbStack._ISeedDoc> _docs;
    public StreamItem_SeedDocsItem(Dafny.ISequence<ThunderDbStack._ISeedDoc> docs) : base() {
      this._docs = docs;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_SeedDocsItem(_docs);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_SeedDocsItem;
      return oth != null && object.Equals(this._docs, oth._docs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.SeedDocsItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._docs);
      s += ")";
      return s;
    }
  }

  public interface _IWorkerRunSummary {
    bool is_WorkerRunSummary { get; }
    BigInteger dtor_matchEvents { get; }
    BigInteger dtor_evictions { get; }
    BigInteger dtor_retrievalBatches { get; }
    BigInteger dtor_retrievalDocs { get; }
    BigInteger dtor_eventsProcessed { get; }
    _IWorkerRunSummary DowncastClone();
  }
  public class WorkerRunSummary : _IWorkerRunSummary {
    public readonly BigInteger _matchEvents;
    public readonly BigInteger _evictions;
    public readonly BigInteger _retrievalBatches;
    public readonly BigInteger _retrievalDocs;
    public readonly BigInteger _eventsProcessed;
    public WorkerRunSummary(BigInteger matchEvents, BigInteger evictions, BigInteger retrievalBatches, BigInteger retrievalDocs, BigInteger eventsProcessed) {
      this._matchEvents = matchEvents;
      this._evictions = evictions;
      this._retrievalBatches = retrievalBatches;
      this._retrievalDocs = retrievalDocs;
      this._eventsProcessed = eventsProcessed;
    }
    public _IWorkerRunSummary DowncastClone() {
      if (this is _IWorkerRunSummary dt) { return dt; }
      return new WorkerRunSummary(_matchEvents, _evictions, _retrievalBatches, _retrievalDocs, _eventsProcessed);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.WorkerRunSummary;
      return oth != null && this._matchEvents == oth._matchEvents && this._evictions == oth._evictions && this._retrievalBatches == oth._retrievalBatches && this._retrievalDocs == oth._retrievalDocs && this._eventsProcessed == oth._eventsProcessed;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchEvents));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._evictions));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retrievalBatches));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retrievalDocs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._eventsProcessed));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.WorkerRunSummary.WorkerRunSummary";
      s += "(";
      s += Dafny.Helpers.ToString(this._matchEvents);
      s += ", ";
      s += Dafny.Helpers.ToString(this._evictions);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retrievalBatches);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retrievalDocs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._eventsProcessed);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IWorkerRunSummary theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IWorkerRunSummary Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IWorkerRunSummary> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IWorkerRunSummary>(ThunderDbStack.WorkerRunSummary.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IWorkerRunSummary> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWorkerRunSummary create(BigInteger matchEvents, BigInteger evictions, BigInteger retrievalBatches, BigInteger retrievalDocs, BigInteger eventsProcessed) {
      return new WorkerRunSummary(matchEvents, evictions, retrievalBatches, retrievalDocs, eventsProcessed);
    }
    public static _IWorkerRunSummary create_WorkerRunSummary(BigInteger matchEvents, BigInteger evictions, BigInteger retrievalBatches, BigInteger retrievalDocs, BigInteger eventsProcessed) {
      return create(matchEvents, evictions, retrievalBatches, retrievalDocs, eventsProcessed);
    }
    public bool is_WorkerRunSummary { get { return true; } }
    public BigInteger dtor_matchEvents {
      get {
        return this._matchEvents;
      }
    }
    public BigInteger dtor_evictions {
      get {
        return this._evictions;
      }
    }
    public BigInteger dtor_retrievalBatches {
      get {
        return this._retrievalBatches;
      }
    }
    public BigInteger dtor_retrievalDocs {
      get {
        return this._retrievalDocs;
      }
    }
    public BigInteger dtor_eventsProcessed {
      get {
        return this._eventsProcessed;
      }
    }
  }

  public interface _IEngineState {
    bool is_EngineState { get; }
    Dafny.ISequence<ThunderDbStack._IStoredDoc> dtor_store { get; }
    Dafny.ISequence<DocsIndexModel._IEntry> dtor_entries { get; }
    Dafny.ISequence<ThunderDbStack._IQueryRuntime> dtor_queries { get; }
    BigInteger dtor_nextQueryId { get; }
    _IEngineState DowncastClone();
  }
  public class EngineState : _IEngineState {
    public readonly Dafny.ISequence<ThunderDbStack._IStoredDoc> _store;
    public readonly Dafny.ISequence<DocsIndexModel._IEntry> _entries;
    public readonly Dafny.ISequence<ThunderDbStack._IQueryRuntime> _queries;
    public readonly BigInteger _nextQueryId;
    public EngineState(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, Dafny.ISequence<DocsIndexModel._IEntry> entries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger nextQueryId) {
      this._store = store;
      this._entries = entries;
      this._queries = queries;
      this._nextQueryId = nextQueryId;
    }
    public _IEngineState DowncastClone() {
      if (this is _IEngineState dt) { return dt; }
      return new EngineState(_store, _entries, _queries, _nextQueryId);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.EngineState;
      return oth != null && object.Equals(this._store, oth._store) && object.Equals(this._entries, oth._entries) && object.Equals(this._queries, oth._queries) && this._nextQueryId == oth._nextQueryId;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._store));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._entries));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queries));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nextQueryId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.EngineState.EngineState";
      s += "(";
      s += Dafny.Helpers.ToString(this._store);
      s += ", ";
      s += Dafny.Helpers.ToString(this._entries);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queries);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nextQueryId);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IEngineState theDefault = create(Dafny.Sequence<ThunderDbStack._IStoredDoc>.Empty, Dafny.Sequence<DocsIndexModel._IEntry>.Empty, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Empty, BigInteger.Zero);
    public static ThunderDbStack._IEngineState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IEngineState> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IEngineState>(ThunderDbStack.EngineState.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IEngineState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEngineState create(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, Dafny.ISequence<DocsIndexModel._IEntry> entries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger nextQueryId) {
      return new EngineState(store, entries, queries, nextQueryId);
    }
    public static _IEngineState create_EngineState(Dafny.ISequence<ThunderDbStack._IStoredDoc> store, Dafny.ISequence<DocsIndexModel._IEntry> entries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger nextQueryId) {
      return create(store, entries, queries, nextQueryId);
    }
    public bool is_EngineState { get { return true; } }
    public Dafny.ISequence<ThunderDbStack._IStoredDoc> dtor_store {
      get {
        return this._store;
      }
    }
    public Dafny.ISequence<DocsIndexModel._IEntry> dtor_entries {
      get {
        return this._entries;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IQueryRuntime> dtor_queries {
      get {
        return this._queries;
      }
    }
    public BigInteger dtor_nextQueryId {
      get {
        return this._nextQueryId;
      }
    }
  }
} // end of namespace ThunderDbStack
namespace ThunderDbStackBench {

  public partial class __default {
    public static BigInteger NextState(BigInteger state) {
      BigInteger _0_next = Dafny.Helpers.EuclideanModulus((state) * (ThunderDbStackBench.__default.Multiplier), ThunderDbStackBench.__default.Modulus);
      if ((_0_next).Sign != 1) {
        return (_0_next) + (ThunderDbStackBench.__default.Modulus);
      } else {
        return _0_next;
      }
    }
    public static void NextRand(BigInteger state, out BigInteger nextState, out BigInteger @value)
    {
      nextState = BigInteger.Zero;
      @value = BigInteger.Zero;
      nextState = ThunderDbStackBench.__default.NextState(state);
      @value = nextState;
    }
    public static Dafny.ISequence<BigInteger> EntryIds(Dafny.ISequence<DocsIndexModel._IEntry> entries) {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((entries).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((entries).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (entries).Drop(BigInteger.One);
        entries = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static bool QueryKnown(Dafny.ISequence<ThunderDbStackBench._IObservedQuery> observed, BigInteger id)
    {
      if ((new BigInteger((observed).Count)).Sign == 0) {
        return false;
      } else {
        return ((((observed).Select(BigInteger.Zero)).dtor_id) == (id)) || (ThunderDbStackBench.__default.QueryKnown((observed).Drop(BigInteger.One), id));
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IStoredDoc> PutObservedQueryDoc(Dafny.ISequence<ThunderDbStack._IStoredDoc> docs, BigInteger id, BigInteger state)
    {
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements(ThunderDbStack.StoredDoc.create(id, state)));
      } else if ((((docs).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements(ThunderDbStack.StoredDoc.create(id, state)), (docs).Drop(BigInteger.One)));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements((docs).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in0 = (docs).Drop(BigInteger.One);
        BigInteger _in1 = id;
        BigInteger _in2 = state;
        docs = _in0;
        id = _in1;
        state = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IStoredDoc> RemoveObservedQueryDoc(Dafny.ISequence<ThunderDbStack._IStoredDoc> docs, BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements());
      } else if ((((docs).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, (docs).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IStoredDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements((docs).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IStoredDoc> _in0 = (docs).Drop(BigInteger.One);
        BigInteger _in1 = id;
        docs = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> EvictedDocForQuery(Dafny.ISequence<ThunderDbStack._IEviction> evictions, BigInteger queryId)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((evictions).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else if ((((evictions).Select(BigInteger.Zero)).dtor_queryId) == (queryId)) {
        return Dafny.Sequence<BigInteger>.FromElements(((evictions).Select(BigInteger.Zero)).dtor_docId);
      } else {
        Dafny.ISequence<ThunderDbStack._IEviction> _in0 = (evictions).Drop(BigInteger.One);
        BigInteger _in1 = queryId;
        evictions = _in0;
        queryId = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static ThunderDbStackBench._IObservedQuery ApplyMatchToObservedQuery(ThunderDbStackBench._IObservedQuery query, ThunderDbStack._IMatchPayload payload)
    {
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _0_docs = ((ThunderDbStack.__default.ContainsQueryId((payload).dtor_matchesOld, (query).dtor_id)) ? (ThunderDbStackBench.__default.RemoveObservedQueryDoc((query).dtor_docs, (payload).dtor_docId)) : ((query).dtor_docs));
      Dafny.ISequence<BigInteger> _1_evicted = ThunderDbStackBench.__default.EvictedDocForQuery((payload).dtor_evictions, (query).dtor_id);
      Dafny.ISequence<ThunderDbStack._IStoredDoc> _2_docs2 = (((new BigInteger((_1_evicted).Count)).Sign == 0) ? (_0_docs) : (ThunderDbStackBench.__default.RemoveObservedQueryDoc(_0_docs, (_1_evicted).Select(BigInteger.Zero))));
      if (ThunderDbStack.__default.ContainsQueryId((payload).dtor_matchesNew, (query).dtor_id)) {
        ThunderDbStack._IMaybeDocState _source0 = (payload).dtor_newState;
        {
          if (_source0.is_NoState) {
            return ThunderDbStackBench.ObservedQuery.create((query).dtor_id, (query).dtor_spec, ThunderDbStackBench.__default.RemoveObservedQueryDoc(_2_docs2, (payload).dtor_docId));
          }
        }
        {
          BigInteger _3_state = _source0.dtor_state;
          return ThunderDbStackBench.ObservedQuery.create((query).dtor_id, (query).dtor_spec, ThunderDbStackBench.__default.PutObservedQueryDoc(_2_docs2, (payload).dtor_docId, _3_state));
        }
      } else {
        return ThunderDbStackBench.ObservedQuery.create((query).dtor_id, (query).dtor_spec, _2_docs2);
      }
    }
    public static Dafny.ISequence<ThunderDbStackBench._IObservedQuery> ApplyMatchToObservedQueries(Dafny.ISequence<ThunderDbStackBench._IObservedQuery> observed, ThunderDbStack._IMatchPayload payload)
    {
      Dafny.ISequence<ThunderDbStackBench._IObservedQuery> _0___accumulator = Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((observed).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements(ThunderDbStackBench.__default.ApplyMatchToObservedQuery((observed).Select(BigInteger.Zero), payload)));
        Dafny.ISequence<ThunderDbStackBench._IObservedQuery> _in0 = (observed).Drop(BigInteger.One);
        ThunderDbStack._IMatchPayload _in1 = payload;
        observed = _in0;
        payload = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static ThunderDbStackBench._IObservedQuery ApplyRetrievalDocToObservedQuery(ThunderDbStackBench._IObservedQuery query, ThunderDbStack._IRetrievalDoc retrieval)
    {
      if (ThunderDbStack.__default.ContainsQueryId((retrieval).dtor_queries, (query).dtor_id)) {
        return ThunderDbStackBench.ObservedQuery.create((query).dtor_id, (query).dtor_spec, ThunderDbStackBench.__default.PutObservedQueryDoc((query).dtor_docs, (retrieval).dtor_docId, (retrieval).dtor_state));
      } else {
        return query;
      }
    }
    public static ThunderDbStackBench._IObservedQuery ApplyRetrievalDocsToObservedQuery(ThunderDbStackBench._IObservedQuery query, Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((docs).Count)).Sign == 0) {
        return query;
      } else {
        ThunderDbStackBench._IObservedQuery _in0 = ThunderDbStackBench.__default.ApplyRetrievalDocToObservedQuery(query, (docs).Select(BigInteger.Zero));
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _in1 = (docs).Drop(BigInteger.One);
        query = _in0;
        docs = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStackBench._IObservedQuery> ApplyRetrievalToObservedQueries(Dafny.ISequence<ThunderDbStackBench._IObservedQuery> observed, Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs)
    {
      Dafny.ISequence<ThunderDbStackBench._IObservedQuery> _0___accumulator = Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((observed).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements(ThunderDbStackBench.__default.ApplyRetrievalDocsToObservedQuery((observed).Select(BigInteger.Zero), docs)));
        Dafny.ISequence<ThunderDbStackBench._IObservedQuery> _in0 = (observed).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _in1 = docs;
        observed = _in0;
        docs = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStackBench._IObservedQuery> ApplyEventsToObserved(Dafny.ISequence<ThunderDbStackBench._IObservedQuery> observed, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((events).Count)).Sign == 0) {
        return observed;
      } else {
        ThunderDbStack._IDownstreamEvent _source0 = (events).Select(BigInteger.Zero);
        {
          if (_source0.is_MatchEvent) {
            ThunderDbStack._IMatchPayload _0_payload = _source0.dtor_payload;
            Dafny.ISequence<ThunderDbStackBench._IObservedQuery> _in0 = ThunderDbStackBench.__default.ApplyMatchToObservedQueries(observed, _0_payload);
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _in1 = (events).Drop(BigInteger.One);
            observed = _in0;
            events = _in1;
            goto TAIL_CALL_START;
          }
        }
        {
          Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _1_docs = _source0.dtor_docs;
          Dafny.ISequence<ThunderDbStackBench._IObservedQuery> _in2 = ThunderDbStackBench.__default.ApplyRetrievalToObservedQueries(observed, _1_docs);
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _in3 = (events).Drop(BigInteger.One);
          observed = _in2;
          events = _in3;
          goto TAIL_CALL_START;
        }
      }
    }
    public static void CheckObservedState(Dafny.ISequence<Dafny.Rune> name, BigInteger opIndex, ThunderDbStack._IEngineState state, Dafny.ISequence<ThunderDbStackBench._IObservedQuery> observed)
    {
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger((observed).Count))) {
        Dafny.ISequence<BigInteger> _1_expectedIds;
        _1_expectedIds = ThunderDbStack.__default.QueryVisible((state).dtor_queries, ((observed).Select(_0_i)).dtor_id);
        Dafny.ISequence<BigInteger> _2_actualIds;
        _2_actualIds = ThunderDbStackBench.__default.EntryIds(ThunderDbStack.__default.BuildEntriesFromStore(((observed).Select(_0_i)).dtor_docs));
        if (!(_1_expectedIds).Equals(_2_actualIds)) {
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("scenario ")).ToVerbatimString(false));
          Dafny.Helpers.Print((name).ToVerbatimString(false));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" mismatch at op ")).ToVerbatimString(false));
          Dafny.Helpers.Print((opIndex));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" query ")).ToVerbatimString(false));
          Dafny.Helpers.Print((((observed).Select(_0_i)).dtor_id));
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
          if (!((_1_expectedIds).Equals(_2_actualIds))) {
            throw new Dafny.HaltException("specs/dafny/ThunderDbStackBench.dfy(119,8): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
        }
        BigInteger _3_j;
        _3_j = BigInteger.Zero;
        while ((_3_j) < (new BigInteger((((observed).Select(_0_i)).dtor_docs).Count))) {
          ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState((state).dtor_store, ((((observed).Select(_0_i)).dtor_docs).Select(_3_j)).dtor_id);
          {
            if (_source0.is_NoState) {
              {
                if (!(false)) {
                  throw new Dafny.HaltException("specs/dafny/ThunderDbStackBench.dfy(128,10): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
              }
              goto after_match0;
            }
          }
          {
            BigInteger _4_docState = _source0.dtor_state;
            {
              if (!((_4_docState) == (((((observed).Select(_0_i)).dtor_docs).Select(_3_j)).dtor_state))) {
                throw new Dafny.HaltException("specs/dafny/ThunderDbStackBench.dfy(131,10): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
            }
            _3_j = (_3_j) + (BigInteger.One);
          }
        after_match0: ;
        }
        _0_i = (_0_i) + (BigInteger.One);
      }
    }
    public static void RunScenario(Dafny.ISequence<Dafny.Rune> name, BigInteger seed, BigInteger documents, BigInteger customers, BigInteger ticks, BigInteger updatesPerTick, BigInteger insertsPerTick, BigInteger deletesPerTick, BigInteger queryLimit, BigInteger density, BigInteger checksEveryOps)
    {
      ThunderDbStack._IEngineState _0_state;
      _0_state = ThunderDbStack.__default.EmptyState();
      Dafny.ISequence<ThunderDbStackBench._IObservedQuery> _1_observed;
      _1_observed = Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements();
      ThunderDbStack._IWorkerRunSummary _2_summary;
      _2_summary = ThunderDbStack.__default.SummaryZero();
      BigInteger _3_rng;
      if ((seed).Sign != 1) {
        _3_rng = BigInteger.One;
      } else {
        _3_rng = seed;
      }
      Dafny.ISequence<ThunderDbStack._ISeedDoc> _4_seedDocs;
      _4_seedDocs = Dafny.Sequence<ThunderDbStack._ISeedDoc>.FromElements();
      BigInteger _5_nextDocId;
      _5_nextDocId = documents;
      BigInteger _6_range;
      if ((density).Sign == 0) {
        _6_range = BigInteger.One;
      } else {
        _6_range = (Dafny.Helpers.EuclideanDivision(documents, density)) + (BigInteger.One);
      }
      BigInteger _7_i;
      _7_i = BigInteger.Zero;
      while ((_7_i) < (documents)) {
        BigInteger _8_nextRng;
        BigInteger _9_scoreSeed;
        BigInteger _out0;
        BigInteger _out1;
        ThunderDbStackBench.__default.NextRand(_3_rng, out _out0, out _out1);
        _8_nextRng = _out0;
        _9_scoreSeed = _out1;
        _3_rng = _8_nextRng;
        _4_seedDocs = Dafny.Sequence<ThunderDbStack._ISeedDoc>.Concat(_4_seedDocs, Dafny.Sequence<ThunderDbStack._ISeedDoc>.FromElements(ThunderDbStack.SeedDoc.create(_7_i, Dafny.Helpers.EuclideanModulus(_9_scoreSeed, _6_range))));
        _7_i = (_7_i) + (BigInteger.One);
      }
      ThunderDbStack._IEngineState _10_nextState;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _11_seedEvents;
      BigInteger _12_ignoredQueryId;
      ThunderDbStack._IEngineState _out2;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out3;
      BigInteger _out4;
      ThunderDbStack.__default.ProcessItem(_0_state, ThunderDbStack.StreamItem.create_SeedDocsItem(_4_seedDocs), out _out2, out _out3, out _out4);
      _10_nextState = _out2;
      _11_seedEvents = _out3;
      _12_ignoredQueryId = _out4;
      _0_state = _10_nextState;
      _1_observed = ThunderDbStackBench.__default.ApplyEventsToObserved(_1_observed, _11_seedEvents);
      _2_summary = ThunderDbStack.__default.UpdateSummary(_2_summary, _11_seedEvents);
      ThunderDbStackBench.__default.CheckObservedState(name, BigInteger.Zero, _0_state, _1_observed);
      _7_i = BigInteger.Zero;
      while ((_7_i) < (customers)) {
        BigInteger _13_nextRng1;
        BigInteger _14_widthSeed;
        BigInteger _out5;
        BigInteger _out6;
        ThunderDbStackBench.__default.NextRand(_3_rng, out _out5, out _out6);
        _13_nextRng1 = _out5;
        _14_widthSeed = _out6;
        _3_rng = _13_nextRng1;
        BigInteger _15_nextRng2;
        BigInteger _16_minSeed;
        BigInteger _out7;
        BigInteger _out8;
        ThunderDbStackBench.__default.NextRand(_3_rng, out _out7, out _out8);
        _15_nextRng2 = _out7;
        _16_minSeed = _out8;
        _3_rng = _15_nextRng2;
        BigInteger _17_width;
        _17_width = (BigInteger.One) + (Dafny.Helpers.EuclideanModulus(_14_widthSeed, (Dafny.Helpers.EuclideanDivision(_6_range, new BigInteger(2))) + (BigInteger.One)));
        BigInteger _18_minScore;
        _18_minScore = Dafny.Helpers.EuclideanModulus(_16_minSeed, _6_range);
        BigInteger _19_maxScore;
        _19_maxScore = (_18_minScore) + (_17_width);
        ThunderDbStack._IQuerySpec _20_spec;
        _20_spec = ThunderDbStack.QuerySpec.create(_18_minScore, _19_maxScore, queryLimit);
        ThunderDbStack._IEngineState _21_stateAfterAdd;
        Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _22_events;
        BigInteger _23_queryId;
        ThunderDbStack._IEngineState _out9;
        Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out10;
        BigInteger _out11;
        ThunderDbStack.__default.ProcessItem(_0_state, ThunderDbStack.StreamItem.create_QueryAddItem(_20_spec), out _out9, out _out10, out _out11);
        _21_stateAfterAdd = _out9;
        _22_events = _out10;
        _23_queryId = _out11;
        _0_state = _21_stateAfterAdd;
        _1_observed = Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.Concat(_1_observed, Dafny.Sequence<ThunderDbStackBench._IObservedQuery>.FromElements(ThunderDbStackBench.ObservedQuery.create(_23_queryId, _20_spec, Dafny.Sequence<ThunderDbStack._IStoredDoc>.FromElements())));
        _1_observed = ThunderDbStackBench.__default.ApplyEventsToObserved(_1_observed, _22_events);
        _2_summary = ThunderDbStack.__default.UpdateSummary(_2_summary, _22_events);
        _7_i = (_7_i) + (BigInteger.One);
      }
      ThunderDbStackBench.__default.CheckObservedState(name, customers, _0_state, _1_observed);
      BigInteger _24_opIndex;
      _24_opIndex = customers;
      BigInteger _25_tick;
      _25_tick = BigInteger.Zero;
      while ((_25_tick) < (ticks)) {
        BigInteger _26_update;
        _26_update = BigInteger.Zero;
        while ((_26_update) < (updatesPerTick)) {
          if ((new BigInteger(((_0_state).dtor_store).Count)).Sign == 1) {
            BigInteger _27_nextRng3;
            BigInteger _28_pickSeed;
            BigInteger _out12;
            BigInteger _out13;
            ThunderDbStackBench.__default.NextRand(_3_rng, out _out12, out _out13);
            _27_nextRng3 = _out12;
            _28_pickSeed = _out13;
            _3_rng = _27_nextRng3;
            BigInteger _29_nextRng4;
            BigInteger _30_scoreSeed;
            BigInteger _out14;
            BigInteger _out15;
            ThunderDbStackBench.__default.NextRand(_3_rng, out _out14, out _out15);
            _29_nextRng4 = _out14;
            _30_scoreSeed = _out15;
            _3_rng = _29_nextRng4;
            BigInteger _31_picked;
            _31_picked = Dafny.Helpers.EuclideanModulus(_28_pickSeed, new BigInteger(((_0_state).dtor_store).Count));
            ThunderDbStack._IStoredDoc _32_doc;
            _32_doc = ((_0_state).dtor_store).Select(_31_picked);
            BigInteger _33_updatedDocState;
            _33_updatedDocState = Dafny.Helpers.EuclideanModulus(_30_scoreSeed, _6_range);
            ThunderDbStack._IEngineState _34_stateAfterUpdate;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _35_events;
            BigInteger _36_ignoredQueryId2;
            ThunderDbStack._IEngineState _out16;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out17;
            BigInteger _out18;
            ThunderDbStack.__default.ProcessItem(_0_state, ThunderDbStack.StreamItem.create_DocChangeItem((_32_doc).dtor_id, ThunderDbStack.MaybeDocState.create_HasState((_32_doc).dtor_state), ThunderDbStack.MaybeDocState.create_HasState(_33_updatedDocState)), out _out16, out _out17, out _out18);
            _34_stateAfterUpdate = _out16;
            _35_events = _out17;
            _36_ignoredQueryId2 = _out18;
            _0_state = _34_stateAfterUpdate;
            _1_observed = ThunderDbStackBench.__default.ApplyEventsToObserved(_1_observed, _35_events);
            _2_summary = ThunderDbStack.__default.UpdateSummary(_2_summary, _35_events);
            _24_opIndex = (_24_opIndex) + (BigInteger.One);
            if (((checksEveryOps).Sign == 1) && ((Dafny.Helpers.EuclideanModulus(_24_opIndex, checksEveryOps)).Sign == 0)) {
              ThunderDbStackBench.__default.CheckObservedState(name, _24_opIndex, _0_state, _1_observed);
            }
          }
          _26_update = (_26_update) + (BigInteger.One);
        }
        BigInteger _37_insert;
        _37_insert = BigInteger.Zero;
        while ((_37_insert) < (insertsPerTick)) {
          BigInteger _38_nextRng5;
          BigInteger _39_scoreSeed;
          BigInteger _out19;
          BigInteger _out20;
          ThunderDbStackBench.__default.NextRand(_3_rng, out _out19, out _out20);
          _38_nextRng5 = _out19;
          _39_scoreSeed = _out20;
          _3_rng = _38_nextRng5;
          BigInteger _40_newDoc;
          _40_newDoc = Dafny.Helpers.EuclideanModulus(_39_scoreSeed, _6_range);
          ThunderDbStack._IEngineState _41_stateAfterInsert;
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _42_events;
          BigInteger _43_ignoredQueryId3;
          ThunderDbStack._IEngineState _out21;
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out22;
          BigInteger _out23;
          ThunderDbStack.__default.ProcessItem(_0_state, ThunderDbStack.StreamItem.create_DocChangeItem(_5_nextDocId, ThunderDbStack.MaybeDocState.create_NoState(), ThunderDbStack.MaybeDocState.create_HasState(_40_newDoc)), out _out21, out _out22, out _out23);
          _41_stateAfterInsert = _out21;
          _42_events = _out22;
          _43_ignoredQueryId3 = _out23;
          _0_state = _41_stateAfterInsert;
          _1_observed = ThunderDbStackBench.__default.ApplyEventsToObserved(_1_observed, _42_events);
          _2_summary = ThunderDbStack.__default.UpdateSummary(_2_summary, _42_events);
          _5_nextDocId = (_5_nextDocId) + (BigInteger.One);
          _24_opIndex = (_24_opIndex) + (BigInteger.One);
          if (((checksEveryOps).Sign == 1) && ((Dafny.Helpers.EuclideanModulus(_24_opIndex, checksEveryOps)).Sign == 0)) {
            ThunderDbStackBench.__default.CheckObservedState(name, _24_opIndex, _0_state, _1_observed);
          }
          _37_insert = (_37_insert) + (BigInteger.One);
        }
        BigInteger _44_delete;
        _44_delete = BigInteger.Zero;
        while ((_44_delete) < (deletesPerTick)) {
          if ((new BigInteger(((_0_state).dtor_store).Count)).Sign == 1) {
            BigInteger _45_nextRng6;
            BigInteger _46_pickSeed;
            BigInteger _out24;
            BigInteger _out25;
            ThunderDbStackBench.__default.NextRand(_3_rng, out _out24, out _out25);
            _45_nextRng6 = _out24;
            _46_pickSeed = _out25;
            _3_rng = _45_nextRng6;
            BigInteger _47_picked;
            _47_picked = Dafny.Helpers.EuclideanModulus(_46_pickSeed, new BigInteger(((_0_state).dtor_store).Count));
            ThunderDbStack._IStoredDoc _48_doc;
            _48_doc = ((_0_state).dtor_store).Select(_47_picked);
            ThunderDbStack._IEngineState _49_stateAfterDelete;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _50_events;
            BigInteger _51_ignoredQueryId4;
            ThunderDbStack._IEngineState _out26;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out27;
            BigInteger _out28;
            ThunderDbStack.__default.ProcessItem(_0_state, ThunderDbStack.StreamItem.create_DocChangeItem((_48_doc).dtor_id, ThunderDbStack.MaybeDocState.create_HasState((_48_doc).dtor_state), ThunderDbStack.MaybeDocState.create_NoState()), out _out26, out _out27, out _out28);
            _49_stateAfterDelete = _out26;
            _50_events = _out27;
            _51_ignoredQueryId4 = _out28;
            _0_state = _49_stateAfterDelete;
            _1_observed = ThunderDbStackBench.__default.ApplyEventsToObserved(_1_observed, _50_events);
            _2_summary = ThunderDbStack.__default.UpdateSummary(_2_summary, _50_events);
            _24_opIndex = (_24_opIndex) + (BigInteger.One);
            if (((checksEveryOps).Sign == 1) && ((Dafny.Helpers.EuclideanModulus(_24_opIndex, checksEveryOps)).Sign == 0)) {
              ThunderDbStackBench.__default.CheckObservedState(name, _24_opIndex, _0_state, _1_observed);
            }
          }
          _44_delete = (_44_delete) + (BigInteger.One);
        }
        _25_tick = (_25_tick) + (BigInteger.One);
      }
      ThunderDbStackBench.__default.CheckObservedState(name, _24_opIndex, _0_state, _1_observed);
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("scenario ")).ToVerbatimString(false));
      Dafny.Helpers.Print((name).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" passed: events=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_2_summary).dtor_eventsProcessed));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", matches=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_2_summary).dtor_matchEvents));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", evictions=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_2_summary).dtor_evictions));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", retrievalBatches=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_2_summary).dtor_retrievalBatches));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", retrievalDocs=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_2_summary).dtor_retrievalDocs));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
    }
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      ThunderDbStackBench.__default.RunScenario(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("whole-stack-small"), new BigInteger(42), new BigInteger(200), new BigInteger(30), new BigInteger(20), new BigInteger(10), new BigInteger(2), new BigInteger(2), new BigInteger(12), new BigInteger(8), BigInteger.One);
      ThunderDbStackBench.__default.RunScenario(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("whole-stack-benchmark-like"), new BigInteger(123), new BigInteger(800), new BigInteger(120), new BigInteger(30), new BigInteger(35), new BigInteger(8), new BigInteger(8), new BigInteger(25), new BigInteger(10), new BigInteger(100));
    }
    public static BigInteger Multiplier { get {
      return new BigInteger(48271);
    } }
    public static BigInteger Modulus { get {
      return new BigInteger(2147483647);
    } }
  }

  public interface _IObservedQuery {
    bool is_ObservedQuery { get; }
    BigInteger dtor_id { get; }
    ThunderDbStack._IQuerySpec dtor_spec { get; }
    Dafny.ISequence<ThunderDbStack._IStoredDoc> dtor_docs { get; }
    _IObservedQuery DowncastClone();
  }
  public class ObservedQuery : _IObservedQuery {
    public readonly BigInteger _id;
    public readonly ThunderDbStack._IQuerySpec _spec;
    public readonly Dafny.ISequence<ThunderDbStack._IStoredDoc> _docs;
    public ObservedQuery(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<ThunderDbStack._IStoredDoc> docs) {
      this._id = id;
      this._spec = spec;
      this._docs = docs;
    }
    public _IObservedQuery DowncastClone() {
      if (this is _IObservedQuery dt) { return dt; }
      return new ObservedQuery(_id, _spec, _docs);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStackBench.ObservedQuery;
      return oth != null && this._id == oth._id && object.Equals(this._spec, oth._spec) && object.Equals(this._docs, oth._docs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._spec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStackBench.ObservedQuery.ObservedQuery";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._spec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._docs);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStackBench._IObservedQuery theDefault = create(BigInteger.Zero, ThunderDbStack.QuerySpec.Default(), Dafny.Sequence<ThunderDbStack._IStoredDoc>.Empty);
    public static ThunderDbStackBench._IObservedQuery Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStackBench._IObservedQuery> _TYPE = new Dafny.TypeDescriptor<ThunderDbStackBench._IObservedQuery>(ThunderDbStackBench.ObservedQuery.Default());
    public static Dafny.TypeDescriptor<ThunderDbStackBench._IObservedQuery> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IObservedQuery create(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<ThunderDbStack._IStoredDoc> docs) {
      return new ObservedQuery(id, spec, docs);
    }
    public static _IObservedQuery create_ObservedQuery(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<ThunderDbStack._IStoredDoc> docs) {
      return create(id, spec, docs);
    }
    public bool is_ObservedQuery { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public ThunderDbStack._IQuerySpec dtor_spec {
      get {
        return this._spec;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IStoredDoc> dtor_docs {
      get {
        return this._docs;
      }
    }
  }
} // end of namespace ThunderDbStackBench
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => ThunderDbStackBench.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
