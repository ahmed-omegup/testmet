include "TsDocsRuntime.dfy"
include "TsQueriesRuntime.dfy"

module TsLimitQueriesRuntime {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsDocsRuntime
  import opened TsQueriesRuntime

  datatype QueryInfo = QueryInfo(id: QueryId, a: Score, k: nat, max: Score, currentMatches: nat)
  datatype LimitQueriesState = LimitQueriesState(
    docs: DocsState,
    queries: QueriesState,
    nextId: QueryId,
    infos: map<QueryId, QueryInfo>,
    baseScores: map<QueryId, int>)

  datatype StateChange = StateChange(state: LimitQueriesState, changed: bool)
  datatype QueryAddResult = QueryAddResult(state: LimitQueriesState, queryId: QueryId)
  datatype AddDocumentResult = AddDocumentResult(state: LimitQueriesState, matched: seq<QueryId>, blocked: seq<QueryId>)
  datatype RemoveDocumentResult = RemoveDocumentResult(state: LimitQueriesState, removed: seq<QueryId>)
  datatype GapFillResult = GapFillResult(state: LimitQueriesState, doc: MaybeDocId)

  function EmptyLimitQueriesState(): LimitQueriesState {
    LimitQueriesState(EmptyDocsState(), EmptyQueriesState(), 1, map[], map[])
  }

  predicate LimitQueriesConsistent(state: LimitQueriesState) {
    DocsConsistent(state.docs) &&
    QueriesConsistent(state.queries) &&
    1 <= state.nextId &&
    EntryIdsBelow(state.queries.entries, state.nextId) &&
    (forall id :: id in state.infos ==> id in state.baseScores && state.infos[id].id == id)
  }

  function NatMin(a: nat, b: nat): nat {
    if a < b then a else b
  }

  function RemoveQueryId(ids: seq<QueryId>, id: QueryId): seq<QueryId> {
    if |ids| == 0 then []
    else if ids[0] == id then ids[1..]
    else [ids[0]] + RemoveQueryId(ids[1..], id)
  }

  function SetCurrentMatches(state: LimitQueriesState, queryId: QueryId, currentMatches: nat): LimitQueriesState
    requires queryId in state.infos
    ensures LimitQueriesConsistent(state) ==> LimitQueriesConsistent(SetCurrentMatches(state, queryId, currentMatches))
  {
    var info := state.infos[queryId];
    LimitQueriesState(state.docs, state.queries, state.nextId, state.infos[queryId := QueryInfo(info.id, info.a, info.k, info.max, currentMatches)], state.baseScores)
  }

  function CountDocsInRange(state: LimitQueriesState, minScore: Score, maxScore: Score): nat
    requires LimitQueriesConsistent(state)
  {
    var upper := CountAtMostDoc(state.docs, maxScore);
    var lower := RankDoc(state.docs, minScore, NoDoc);
    if lower <= upper then upper - lower else 0
  }

  function AddQuery(state: LimitQueriesState, a: Score, k: nat, max: Score): QueryAddResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(AddQuery(state, a, k, max).state)
  {
    var queryId := state.nextId;
    var effectiveScore := RankDoc(state.docs, a, NoDoc) + k;
    var nextQueries := Insert(state.queries, a, state.nextId, effectiveScore, max);
    var baseScore := effectiveScore - AccumulatedAddAtKey(state.queries, a);
    var currentMatches := NatMin(CountDocsInRange(state, a, max), k);
    QueryAddResult(
      LimitQueriesState(state.docs, nextQueries, queryId + 1, state.infos[queryId := QueryInfo(queryId, a, k, max, currentMatches)], state.baseScores[queryId := baseScore]),
      queryId)
  }

  function RemoveQuery(state: LimitQueriesState, queryId: QueryId): StateChange
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(RemoveQuery(state, queryId).state)
  {
    if !(queryId in state.infos) || !(queryId in state.baseScores) then StateChange(state, false)
    else
      var info := state.infos[queryId];
      var baseScore := state.baseScores[queryId];
      var state1 := LimitQueriesState(state.docs, Remove(state.queries, info.a, queryId, baseScore, info.max), state.nextId,
        map key | key in state.infos && key != queryId :: state.infos[key],
        map key | key in state.baseScores && key != queryId :: state.baseScores[key]);
      StateChange(state1, true)
  }

  function GetQueriesCovering(state: LimitQueriesState, value: Score, docId: MaybeDocId): seq<QueryId>
    requires LimitQueriesConsistent(state)
  {
    CollectForValue(state.queries, value, RankDoc(state.docs, value, docId))
  }

  function GetDocsForQuery(state: LimitQueriesState, queryId: QueryId): seq<DocId>
    requires LimitQueriesConsistent(state)
  {
    if !(queryId in state.infos) then []
    else
      var info := state.infos[queryId];
      CollectRangeDocs(state.docs, info.a, info.max, info.k)
  }

  function DecrementCurrentMatchesFor(state: LimitQueriesState, affected: seq<QueryId>): LimitQueriesState
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(DecrementCurrentMatchesFor(state, affected))
    decreases |affected|
  {
    if |affected| == 0 then state
    else if !(affected[0] in state.infos) then DecrementCurrentMatchesFor(state, affected[1..])
    else
      var info := state.infos[affected[0]];
      var nextState := if info.currentMatches == 0 then state else SetCurrentMatches(state, affected[0], info.currentMatches - 1);
      DecrementCurrentMatchesFor(nextState, affected[1..])
  }

  function RemoveDocument(state: LimitQueriesState, score: Score, docId: DocId): RemoveDocumentResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(RemoveDocument(state, score, docId).state)
  {
    var affected := GetQueriesCovering(state, score, SomeDoc(docId));
    var nextDocs := RemoveDoc(state.docs, score, docId);
    var nextQueries := RangeAddKeysGreaterThan(state.queries, score, -1);
    var nextState := LimitQueriesState(nextDocs, nextQueries, state.nextId, state.infos, state.baseScores);
    RemoveDocumentResult(DecrementCurrentMatchesFor(nextState, affected), affected)
  }

  function ProcessAddedQueries(state: LimitQueriesState, affected: seq<QueryId>, docId: DocId): AddDocumentResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(ProcessAddedQueries(state, affected, docId).state)
    decreases |affected|
  {
    if |affected| == 0 then AddDocumentResult(state, [], [])
    else
      var queryId := affected[0];
      var rest := affected[1..];
      if !(queryId in state.infos) then
        var next := ProcessAddedQueries(state, rest, docId);
        AddDocumentResult(next.state, [queryId] + next.matched, next.blocked)
      else
        var info := state.infos[queryId];
        if info.currentMatches < info.k then
          var next := ProcessAddedQueries(SetCurrentMatches(state, queryId, info.currentMatches + 1), rest, docId);
          AddDocumentResult(next.state, [queryId] + next.matched, next.blocked)
        else
          var next := ProcessAddedQueries(state, rest, docId);
          AddDocumentResult(next.state, [queryId] + next.matched, [queryId] + next.blocked)
  }

  function AddDocument(state: LimitQueriesState, score: Score, docId: DocId): AddDocumentResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(AddDocument(state, score, docId).state)
  {
    var affected := GetQueriesCovering(state, score, SomeDoc(docId));
    var nextDocs := AddDoc(state.docs, score, docId);
    var nextQueries := RangeAddKeysGreaterThan(state.queries, score, 1);
    ProcessAddedQueries(LimitQueriesState(nextDocs, nextQueries, state.nextId, state.infos, state.baseScores), affected, docId)
  }

  function DocForQueryAt(state: LimitQueriesState, info: QueryInfo, offset: nat): MaybeDocId
    requires LimitQueriesConsistent(state)
  {
    var startRank := RankDoc(state.docs, info.a, NoDoc);
    match GetAtRankDoc(state.docs, startRank + offset)
    case Missing => NoDoc
    case Found(score, id, pos) => if score <= info.max then SomeDoc(id) else NoDoc
  }

  function PickOverflowDoc(state: LimitQueriesState, queryId: QueryId): MaybeDocId
    requires LimitQueriesConsistent(state)
  {
    if !(queryId in state.infos) then NoDoc
    else
      var info := state.infos[queryId];
      if info.currentMatches < info.k then NoDoc else DocForQueryAt(state, info, info.k)
  }

  function FillGapFrom(state: LimitQueriesState, queryId: QueryId, offset: nat): GapFillResult
    requires LimitQueriesConsistent(state)
    requires queryId in state.infos
    ensures LimitQueriesConsistent(FillGapFrom(state, queryId, offset).state)
    decreases |state.docs.entries| + 1, |state.docs.entries| - offset
  {
    var candidate := DocForQueryAt(state, state.infos[queryId], offset);
    match candidate
    case NoDoc => GapFillResult(state, NoDoc)
    case SomeDoc(docId) =>
      var info := state.infos[queryId];
      var state1 := SetCurrentMatches(state, queryId, info.currentMatches + 1);
      GapFillResult(state1, SomeDoc(docId))
  }

  function FillGap(state: LimitQueriesState, queryId: QueryId): GapFillResult
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(FillGap(state, queryId).state)
  {
    if !(queryId in state.infos) then GapFillResult(state, NoDoc)
    else
      var info := state.infos[queryId];
      if info.currentMatches >= info.k then GapFillResult(state, NoDoc)
      else FillGapFrom(state, queryId, info.currentMatches)
  }

  function CancelPendingForQuery(state: LimitQueriesState, docId: DocId, queryId: QueryId): StateChange
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(CancelPendingForQuery(state, docId, queryId).state)
  {
    StateChange(state, false)
  }

  function ResolvePendingForDoc(state: LimitQueriesState, docId: DocId): LimitQueriesState
    requires LimitQueriesConsistent(state)
    ensures LimitQueriesConsistent(ResolvePendingForDoc(state, docId))
  {
    state
  }
}