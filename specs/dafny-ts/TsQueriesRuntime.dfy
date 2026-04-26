include "../dafny/ThunderDbStack.dfy"

module TsQueriesRuntime {
  import opened DocsIndexModel
  import opened ThunderDbStack

  datatype RangeAddOp = RangeAddOp(threshold: Score, delta: int)
  datatype QueryEntry = QueryEntry(id: QueryId, key: Score, baseScore: int, maxCap: Score)
  datatype QueriesState = QueriesState(entries: seq<QueryEntry>, rangeAdds: seq<RangeAddOp>)

  function EmptyQueriesState(): QueriesState {
    QueriesState([], [])
  }

  function UniqueQueryEntries(entries: seq<QueryEntry>): bool {
    if |entries| == 0 then true
    else !ContainsQueryEntryId(entries[1..], entries[0].id) && UniqueQueryEntries(entries[1..])
  }

  function ContainsQueryEntryId(entries: seq<QueryEntry>, id: QueryId): bool {
    if |entries| == 0 then false
    else entries[0].id == id || ContainsQueryEntryId(entries[1..], id)
  }

  predicate OrderedEntries(entries: seq<QueryEntry>) {
    forall i, j :: 0 <= i < j < |entries| ==>
      entries[i].key < entries[j].key ||
      (entries[i].key == entries[j].key &&
        (entries[i].baseScore < entries[j].baseScore ||
         (entries[i].baseScore == entries[j].baseScore && entries[i].id < entries[j].id)))
  }

  predicate QueriesConsistent(state: QueriesState) {
    UniqueQueryEntries(state.entries) && OrderedEntries(state.entries)
  }

  function SumRangeAddsAtKey(ops: seq<RangeAddOp>, key: Score): int
    decreases |ops|
  {
    if |ops| == 0 then 0
    else (if ops[0].threshold < key then ops[0].delta else 0) + SumRangeAddsAtKey(ops[1..], key)
  }

  function AccumulatedAddAtKey(state: QueriesState, key: Score): int {
    SumRangeAddsAtKey(state.rangeAdds, key)
  }

  function EffectiveScore(state: QueriesState, entry: QueryEntry): int {
    entry.baseScore + AccumulatedAddAtKey(state, entry.key)
  }

  function RangeAddKeysGreaterThan(state: QueriesState, threshold: Score, delta: int): QueriesState {
    QueriesState(state.entries, state.rangeAdds + [RangeAddOp(threshold, delta)])
  }

  function CompareEntries(left: QueryEntry, right: QueryEntry): bool {
    left.key < right.key ||
    (left.key == right.key &&
      (left.baseScore < right.baseScore ||
       (left.baseScore == right.baseScore && left.id < right.id)))
  }

  function InsertEntrySorted(entries: seq<QueryEntry>, entry: QueryEntry): seq<QueryEntry>
    decreases |entries|
  {
    if |entries| == 0 then [entry]
    else if CompareEntries(entry, entries[0]) then [entry] + entries
    else [entries[0]] + InsertEntrySorted(entries[1..], entry)
  }

  function Insert(state: QueriesState, key: Score, id: QueryId, effectiveScore: int, maxCap: Score): QueriesState {
    var baseScore := effectiveScore - AccumulatedAddAtKey(state, key);
    QueriesState(InsertEntrySorted(state.entries, QueryEntry(id, key, baseScore, maxCap)), state.rangeAdds)
  }

  function RemoveEntries(entries: seq<QueryEntry>, key: Score, id: QueryId, baseScore: int, maxCap: Score): seq<QueryEntry>
    decreases |entries|
  {
    if |entries| == 0 then []
    else if entries[0] == QueryEntry(id, key, baseScore, maxCap) then entries[1..]
    else [entries[0]] + RemoveEntries(entries[1..], key, id, baseScore, maxCap)
  }

  function Remove(state: QueriesState, key: Score, id: QueryId, baseScore: int, maxCap: Score): QueriesState {
    QueriesState(RemoveEntries(state.entries, key, id, baseScore, maxCap), state.rangeAdds)
  }

  function CollectForValue(state: QueriesState, value: Score, cutoff: int): seq<QueryId>
    decreases |state.entries|
  {
    CollectMatchingEntries(state, state.entries, value, cutoff)
  }

  function CollectMatchingEntries(state: QueriesState, entries: seq<QueryEntry>, value: Score, cutoff: int): seq<QueryId>
    decreases |entries|
  {
    if |entries| == 0 then []
    else if entries[0].key <= value && value <= entries[0].maxCap && cutoff < EffectiveScore(state, entries[0]) then
      [entries[0].id] + CollectMatchingEntries(state, entries[1..], value, cutoff)
    else
      CollectMatchingEntries(state, entries[1..], value, cutoff)
  }
}