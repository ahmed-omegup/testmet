include "DocsIndexModel.dfy"
include "DocsIndexTreap.dfy"

module ThunderDbStack {
  import opened DocsIndexModel
  import opened DocsIndexTreap

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
  datatype StreamItem =
    | DocChangeItem(id: DocId, oldState: MaybeDocState, newState: MaybeDocState)
    | QueryAddItem(spec: QuerySpec)
    | QueryRemoveItem(id: QueryId)
    | SeedDocsItem(docs: seq<SeedDoc>)
  datatype WorkerRunSummary = WorkerRunSummary(matchEvents: nat, evictions: nat, retrievalBatches: nat, retrievalDocs: nat, eventsProcessed: nat)
  datatype EngineState = EngineState(store: map<DocId, DocState>, docIds: seq<DocId>, treap: Treap, queries: seq<QueryRuntime>, nextQueryId: QueryId)

  function RefInsertEntry(es: seq<Entry>, score: Score, id: DocId): seq<Entry> {
    if |es| == 0 then [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then [Entry(score, id)] + es
    else [es[0]] + RefInsertEntry(es[1..], score, id)
  }

  function RefRemoveEntry(es: seq<Entry>, score: Score, id: DocId): seq<Entry> {
    if |es| == 0 then es
    else if es[0].score == score && es[0].id == id then es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then es
    else [es[0]] + RefRemoveEntry(es[1..], score, id)
  }

  function RefCollectRangeIds(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId> {
    if |es| == 0 || limit == 0 then []
    else if es[0].score < minScore then RefCollectRangeIds(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then []
    else [es[0].id] + RefCollectRangeIds(es[1..], minScore, maxScore, limit - 1)
  }

  function GetScore(state: DocState): Score {
    state.scoreValue
  }

  function HasDoc(store: map<DocId, DocState>, id: DocId): bool {
    id in store
  }

  function LookupState(store: map<DocId, DocState>, id: DocId): MaybeDocState {
    if id in store then HasState(store[id]) else NoState
  }

  function PutStoredDoc(store: map<DocId, DocState>, id: DocId, state: DocState): map<DocId, DocState> {
    store[id := state]
  }

  function RemoveStoredDoc(store: map<DocId, DocState>, id: DocId): map<DocId, DocState> {
    map key | key in store && key != id :: store[key]
  }

  function ContainsId(ids: seq<DocId>, id: DocId): bool {
    if |ids| == 0 then false
    else ids[0] == id || ContainsId(ids[1..], id)
  }

  function ContainsQueryId(ids: seq<QueryId>, id: QueryId): bool {
    if |ids| == 0 then false
    else ids[0] == id || ContainsQueryId(ids[1..], id)
  }

  function AppendQueryIdUnique(ids: seq<QueryId>, id: QueryId): seq<QueryId> {
    if ContainsQueryId(ids, id) then ids else ids + [id]
  }

  function AppendDocIdUnique(ids: seq<DocId>, id: DocId): seq<DocId> {
    if ContainsId(ids, id) then ids else ids + [id]
  }

  function BuildEntriesFromStore(store: seq<StoredDoc>): seq<Entry> {
    if |store| == 0 then []
    else RefInsertEntry(BuildEntriesFromStore(store[1..]), GetScore(store[0].state), store[0].id)
  }

  function VisibleForSpec(entries: seq<Entry>, spec: QuerySpec): seq<DocId> {
    RefCollectRangeIds(entries, spec.minScore, spec.maxScore, spec.limit)
  }

  function PriorityFor(score: Score, id: DocId): Priority {
    ((score + 1) * 1103515245 + (id + 1) * 12345) % 2147483647
  }

  function VisibleForSpecInTreap(treap: Treap, spec: QuerySpec): seq<DocId>
    requires SumConsistent(treap)
  {
    TreapCollectRange(treap, spec.minScore, spec.maxScore, spec.limit)
  }

  function ScoreMatchesSpec(score: Score, spec: QuerySpec): bool {
    spec.minScore <= score <= spec.maxScore
  }

  function EntryBefore(score1: Score, id1: DocId, score2: Score, id2: DocId): bool {
    score1 < score2 || (score1 == score2 && id1 < id2)
  }

  function StateMatchesSpec(state: MaybeDocState, spec: QuerySpec): bool {
    match state
    case NoState => false
    case HasState(docState) => ScoreMatchesSpec(GetScore(docState), spec)
  }

  function DocWouldEnterVisible(visible: seq<DocId>, limit: nat, docState: DocState, docId: DocId, store: map<DocId, DocState>): bool {
    if limit == 0 then false
    else if |visible| < limit then true
    else
      match LookupState(store, visible[|visible| - 1])
      case NoState => false
      case HasState(lastState) => EntryBefore(GetScore(docState), docId, GetScore(lastState), visible[|visible| - 1])
  }

  function QueryNeedsRecompute(query: QueryRuntime, store: map<DocId, DocState>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): bool {
    if ContainsId(query.visible, id) then true
    else
      match newState
      case NoState => false
      case HasState(docState) => ScoreMatchesSpec(GetScore(docState), query.spec) && DocWouldEnterVisible(query.visible, query.spec.limit, docState, id, store)
  }

  function RecomputeQuery(query: QueryRuntime, treap: Treap): QueryRuntime
    requires SumConsistent(treap)
  {
    QueryRuntime(query.id, query.spec, VisibleForSpecInTreap(treap, query.spec))
  }

  function RecomputeQueries(queries: seq<QueryRuntime>, treap: Treap): seq<QueryRuntime>
    requires SumConsistent(treap)
  {
    if |queries| == 0 then []
    else [RecomputeQuery(queries[0], treap)] + RecomputeQueries(queries[1..], treap)
  }

  function RemoveQueryRuntime(queries: seq<QueryRuntime>, id: QueryId): seq<QueryRuntime> {
    if |queries| == 0 then []
    else if queries[0].id == id then queries[1..]
    else [queries[0]] + RemoveQueryRuntime(queries[1..], id)
  }

  function UpdateQueriesForDocChange(queries: seq<QueryRuntime>, treap: Treap, store: map<DocId, DocState>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): seq<QueryRuntime>
    requires SumConsistent(treap)
  {
    if |queries| == 0 then []
    else if QueryNeedsRecompute(queries[0], store, id, oldState, newState)
      then [RecomputeQuery(queries[0], treap)] + UpdateQueriesForDocChange(queries[1..], treap, store, id, oldState, newState)
      else [queries[0]] + UpdateQueriesForDocChange(queries[1..], treap, store, id, oldState, newState)
  }

  function QueryVisible(queries: seq<QueryRuntime>, id: QueryId): seq<DocId> {
    if |queries| == 0 then []
    else if queries[0].id == id then queries[0].visible
    else QueryVisible(queries[1..], id)
  }

  function UniqueDocIds(ids: seq<DocId>): bool {
    if |ids| == 0 then true
    else !ContainsId(ids[1..], ids[0]) && UniqueDocIds(ids[1..])
  }

  function BuildEntriesFromStateStore(store: map<DocId, DocState>, docIds: seq<DocId>): seq<Entry> {
    if |docIds| == 0 then []
    else if docIds[0] in store then RefInsertEntry(BuildEntriesFromStateStore(store, docIds[1..]), GetScore(store[docIds[0]]), docIds[0])
    else BuildEntriesFromStateStore(store, docIds[1..])
  }

  function AppendDocIdIfMissing(ids: seq<DocId>, id: DocId): seq<DocId> {
    if ContainsId(ids, id) then ids else ids + [id]
  }

  function RemoveDocId(ids: seq<DocId>, id: DocId): seq<DocId> {
    if |ids| == 0 then []
    else if ids[0] == id then ids[1..]
    else [ids[0]] + RemoveDocId(ids[1..], id)
  }

  predicate QuerysConsistent(queries: seq<QueryRuntime>, entries: seq<Entry>) {
    if |queries| == 0 then true
    else queries[0].visible == VisibleForSpec(entries, queries[0].spec) && QuerysConsistent(queries[1..], entries)
  }

  predicate ValidState(state: EngineState) {
    UniqueDocIds(state.docIds) &&
    SumConsistent(state.treap) &&
    Entries(state.treap) == BuildEntriesFromStateStore(state.store, state.docIds) &&
    QuerysConsistent(state.queries, Entries(state.treap))
  }

  function EmptyState(): EngineState {
    EngineState(map[], [], Empty, [], 1)
  }

  function AddRetrievalQuery(plans: seq<RetrievalDoc>, docId: DocId, state: DocState, queryId: QueryId): seq<RetrievalDoc> {
    if |plans| == 0 then [RetrievalDoc(docId, state, [queryId])]
    else if plans[0].docId == docId then [RetrievalDoc(docId, state, AppendQueryIdUnique(plans[0].queries, queryId))] + plans[1..]
    else [plans[0]] + AddRetrievalQuery(plans[1..], docId, state, queryId)
  }

  function FirstEvicted(oldVisible: seq<DocId>, newVisible: seq<DocId>, changedId: DocId): seq<DocId> {
    if |oldVisible| == 0 then []
    else if oldVisible[0] != changedId && !ContainsId(newVisible, oldVisible[0]) then [oldVisible[0]]
    else FirstEvicted(oldVisible[1..], newVisible, changedId)
  }

  function FirstAddedDoc(newVisible: seq<DocId>, oldVisible: seq<DocId>, changedId: DocId): seq<DocId>
    decreases |newVisible|
  {
    if |newVisible| == 0 then []
    else if newVisible[0] != changedId && !ContainsId(oldVisible, newVisible[0]) then [newVisible[0]]
    else FirstAddedDoc(newVisible[1..], oldVisible, changedId)
  }

  function BuildGapRetrievalForQuery(oldQuery: QueryRuntime, newQuery: QueryRuntime, store: map<DocId, DocState>, changedId: DocId): seq<RetrievalDoc> {
    var replacement := FirstAddedDoc(newQuery.visible, oldQuery.visible, changedId);
    if ContainsId(oldQuery.visible, changedId) && !ContainsId(newQuery.visible, changedId) && |replacement| > 0 then
      match LookupState(store, replacement[0])
      case NoState => []
      case HasState(state) => [RetrievalDoc(replacement[0], state, [newQuery.id])]
    else
      []
  }

  function BuildRetrievalsFromQueryDiff(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, store: map<DocId, DocState>, changedId: DocId): seq<RetrievalDoc>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then []
    else BuildGapRetrievalForQuery(oldQueries[0], newQueries[0], store, changedId) + BuildRetrievalsFromQueryDiff(oldQueries[1..], newQueries[1..], store, changedId)
  }

  function BuildAddQueryRetrievals(visible: seq<DocId>, store: map<DocId, DocState>, queryId: QueryId): seq<RetrievalDoc>
    decreases |visible|
  {
    if |visible| == 0 then []
    else
      match LookupState(store, visible[0])
      case NoState => BuildAddQueryRetrievals(visible[1..], store, queryId)
      case HasState(docState) => AddRetrievalQuery(BuildAddQueryRetrievals(visible[1..], store, queryId), visible[0], docState, queryId)
  }

  function BuildMatchPayload(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): MatchPayload {
    MatchPayload(id, oldState, newState,
      CollectMatchesOld(oldQueries, newQueries, id),
      CollectMatchesNew(oldQueries, newQueries, id),
      CollectEvictions(oldQueries, newQueries, id))
  }

  function CollectMatchesOld(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<QueryId>
    decreases |oldQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then []
    else if ContainsId(oldQueries[0].visible, id) then [oldQueries[0].id] + CollectMatchesOld(oldQueries[1..], newQueries[1..], id)
    else CollectMatchesOld(oldQueries[1..], newQueries[1..], id)
  }

  function CollectMatchesNew(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<QueryId>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then []
    else if ContainsId(newQueries[0].visible, id) then [newQueries[0].id] + CollectMatchesNew(oldQueries[1..], newQueries[1..], id)
    else CollectMatchesNew(oldQueries[1..], newQueries[1..], id)
  }

  function CollectEvictions(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<Eviction>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then []
    else
      var oldVisible := oldQueries[0].visible;
      if !ContainsId(oldVisible, id) && ContainsId(newQueries[0].visible, id) && |FirstEvicted(oldVisible, newQueries[0].visible, id)| > 0
        then [Eviction(newQueries[0].id, FirstEvicted(oldVisible, newQueries[0].visible, id)[0])] + CollectEvictions(oldQueries[1..], newQueries[1..], id)
        else CollectEvictions(oldQueries[1..], newQueries[1..], id)
  }

  function HasAnyMatchChange(payload: MatchPayload): bool {
    |payload.matchesOld| > 0 || |payload.matchesNew| > 0 || |payload.evictions| > 0
  }

  method SeedDocs(state: EngineState, docs: seq<SeedDoc>) returns (next: EngineState)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
  {
    var store := state.store;
    var docIds := state.docIds;
    var treap := state.treap;
    var i := 0;
    while i < |docs|
      invariant 0 <= i <= |docs|
      invariant SumConsistent(treap)
      decreases |docs| - i
    {
      store := PutStoredDoc(store, docs[i].id, docs[i].state);
      docIds := AppendDocIdIfMissing(docIds, docs[i].id);
      treap := Add(treap, docs[i].state.scoreValue, docs[i].id, PriorityFor(docs[i].state.scoreValue, docs[i].id));
      i := i + 1;
    }
    next := EngineState(store, docIds, treap, RecomputeQueries(state.queries, treap), state.nextQueryId);
  }

  method AddQuery(state: EngineState, spec: QuerySpec) returns (next: EngineState, events: seq<DownstreamEvent>, queryId: QueryId)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
    ensures queryId == state.nextQueryId
  {
    queryId := state.nextQueryId;
    var visible := VisibleForSpecInTreap(state.treap, spec);
    var query := QueryRuntime(queryId, spec, visible);
    next := EngineState(state.store, state.docIds, state.treap, state.queries + [query], state.nextQueryId + 1);
    var retrievals := BuildAddQueryRetrievals(visible, state.store, queryId);
    if |retrievals| == 0 {
      events := [];
    } else {
      events := [RetrievalEvent(retrievals)];
    }
  }

  method RemoveQuery(state: EngineState, id: QueryId) returns (next: EngineState, events: seq<DownstreamEvent>)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
  {
    next := EngineState(state.store, state.docIds, state.treap, RemoveQueryRuntime(state.queries, id), state.nextQueryId);
    events := [];
  }

  method ApplyDocChange(state: EngineState, id: DocId, oldState: MaybeDocState, newState: MaybeDocState) returns (next: EngineState, events: seq<DownstreamEvent>)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
  {
    next := state;
    events := [];
    var store := state.store;
    var docIds := state.docIds;
    var treap := state.treap;
    match oldState
    case NoState => {
    }
    case HasState(oldDoc) => {
      if newState.NoState? {
        store := RemoveStoredDoc(store, id);
        docIds := RemoveDocId(docIds, id);
      }
      treap := Remove(treap, GetScore(oldDoc), id);
    }

    match newState
    case NoState => {
    }
    case HasState(newDoc) => {
      store := PutStoredDoc(store, id, newDoc);
      docIds := AppendDocIdIfMissing(docIds, id);
      treap := Add(treap, GetScore(newDoc), id, PriorityFor(GetScore(newDoc), id));
    }

    var newQueries := UpdateQueriesForDocChange(state.queries, treap, store, id, oldState, newState);
    next := EngineState(store, docIds, treap, newQueries, state.nextQueryId);

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

  method ProcessItem(state: EngineState, item: StreamItem) returns (next: EngineState, events: seq<DownstreamEvent>, queryId: QueryId)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
  {
    next := state;
    events := [];
    queryId := 0;
    match item
    case SeedDocsItem(docs) => {
      next := SeedDocs(state, docs);
      events := [];
    }
    case QueryAddItem(spec) => {
      next, events, queryId := AddQuery(state, spec);
    }
    case QueryRemoveItem(id) => {
      next, events := RemoveQuery(state, id);
    }
    case DocChangeItem(id, oldState, newState) => {
      next, events := ApplyDocChange(state, id, oldState, newState);
    }
  }

  function SummaryZero(): WorkerRunSummary {
    WorkerRunSummary(0, 0, 0, 0, 0)
  }

  function CountEvictions(evictions: seq<Eviction>): nat {
    |evictions|
  }

  function UpdateSummary(summary: WorkerRunSummary, events: seq<DownstreamEvent>): WorkerRunSummary {
    if |events| == 0 then WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed + 1)
    else UpdateSummaryOne(WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed + 1), events)
  }

  function UpdateSummaryOne(summary: WorkerRunSummary, events: seq<DownstreamEvent>): WorkerRunSummary
    decreases |events|
  {
    if |events| == 0 then summary
    else match events[0]
      case MatchEvent(payload) => UpdateSummaryOne(WorkerRunSummary(summary.matchEvents + 1, summary.evictions + CountEvictions(payload.evictions), summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed), events[1..])
      case RetrievalEvent(docs) => UpdateSummaryOne(WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches + 1, summary.retrievalDocs + |docs|, summary.eventsProcessed), events[1..])
  }
}