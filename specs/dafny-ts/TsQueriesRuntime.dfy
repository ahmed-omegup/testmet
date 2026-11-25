include "ThunderDbStack.dfy"

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

  predicate EntryIdsBelow(entries: seq<QueryEntry>, bound: QueryId) {
    if |entries| == 0 then true
    else entries[0].id < bound && EntryIdsBelow(entries[1..], bound)
  }

  function ContainsQueryEntryId(entries: seq<QueryEntry>, id: QueryId): bool {
    if |entries| == 0 then false
    else entries[0].id == id || ContainsQueryEntryId(entries[1..], id)
  }

  predicate OrderedEntries(entries: seq<QueryEntry>) {
    if |entries| < 2 then true
    else CompareEntries(entries[0], entries[1]) && OrderedEntries(entries[1..])
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

  function RangeAddKeysGreaterThan(state: QueriesState, threshold: Score, delta: int): QueriesState
    requires QueriesConsistent(state)
      ensures QueriesConsistent(state) ==> QueriesConsistent(RangeAddKeysGreaterThan(state, threshold, delta))
  {
    QueriesState(state.entries, state.rangeAdds + [RangeAddOp(threshold, delta)])
  }

  function CompareEntries(left: QueryEntry, right: QueryEntry): bool {
    left.key < right.key ||
    (left.key == right.key &&
      (left.baseScore < right.baseScore ||
       (left.baseScore == right.baseScore && left.id < right.id)))
  }

  lemma EntryIdsBelowEntailsNotContained(entries: seq<QueryEntry>, bound: QueryId)
    requires EntryIdsBelow(entries, bound)
    ensures !ContainsQueryEntryId(entries, bound)
    decreases |entries|
  {
  }

  lemma BelowBoundImpliesBelowPlusOne(entries: seq<QueryEntry>, bound: QueryId)
    requires EntryIdsBelow(entries, bound)
    ensures EntryIdsBelow(entries, bound + 1)
    decreases |entries|
  {
    if |entries| > 0{
      BelowBoundImpliesBelowPlusOne(entries[1..], bound);
    }
  }

  function InsertEntrySorted(entries: seq<QueryEntry>, entry: QueryEntry): seq<QueryEntry>
    requires OrderedEntries(entries)
    requires UniqueQueryEntries(entries)
    requires EntryIdsBelow(entries, entry.id)
      ensures OrderedEntries(InsertEntrySorted(entries, entry))
      ensures UniqueQueryEntries(InsertEntrySorted(entries, entry))
      ensures forall id :: ContainsQueryEntryId(InsertEntrySorted(entries, entry), id) ==> id == entry.id || ContainsQueryEntryId(entries, id)
      ensures forall bound :: EntryIdsBelow(entries, bound) && entry.id < bound ==> EntryIdsBelow(InsertEntrySorted(entries, entry), bound)
      ensures EntryIdsBelow(InsertEntrySorted(entries, entry), entry.id + 1)
    decreases |entries|
  {
    if |entries| == 0 then [entry]
    else if CompareEntries(entry, entries[0]) then 
    EntryIdsBelowEntailsNotContained(entries, entry.id);
    BelowBoundImpliesBelowPlusOne(entries, entry.id);
     [entry] + entries
    else [entries[0]] + InsertEntrySorted(entries[1..], entry)
  }

  function Insert(state: QueriesState, key: Score, id: QueryId, effectiveScore: int, maxCap: Score): QueriesState
    requires QueriesConsistent(state)
    requires EntryIdsBelow(state.entries, id)
    ensures QueriesConsistent(Insert(state, key, id, effectiveScore, maxCap))
    ensures forall bound :: EntryIdsBelow(state.entries, bound) && id < bound ==> EntryIdsBelow(Insert(state, key, id, effectiveScore, maxCap).entries, bound)
    ensures EntryIdsBelow(Insert(state, key, id, effectiveScore, maxCap).entries, id + 1)
  {
    var baseScore := effectiveScore - AccumulatedAddAtKey(state, key);
    var entries := InsertEntrySorted(state.entries, QueryEntry(id, key, baseScore, maxCap));
    assert OrderedEntries(entries);
    assert UniqueQueryEntries(entries);
    assert EntryIdsBelow(entries, id + 1);
    QueriesState(entries, state.rangeAdds)
  }

  function RemoveEntries(entries: seq<QueryEntry>, key: Score, id: QueryId, baseScore: int, maxCap: Score): seq<QueryEntry>
    requires OrderedEntries(entries)
    requires UniqueQueryEntries(entries)
      ensures OrderedEntries(entries) ==> OrderedEntries(RemoveEntries(entries, key, id, baseScore, maxCap))
      ensures UniqueQueryEntries(entries) ==> UniqueQueryEntries(RemoveEntries(entries, key, id, baseScore, maxCap))
      ensures forall id2 :: ContainsQueryEntryId(RemoveEntries(entries, key, id, baseScore, maxCap), id2) ==> ContainsQueryEntryId(entries, id2)
      ensures forall bound :: EntryIdsBelow(entries, bound) ==> EntryIdsBelow(RemoveEntries(entries, key, id, baseScore, maxCap), bound)
    decreases |entries|
  {
    if |entries| == 0 then []
    else if entries[0] == QueryEntry(id, key, baseScore, maxCap) then entries[1..]
    else [entries[0]] + RemoveEntries(entries[1..], key, id, baseScore, maxCap)
  }

  function Remove(state: QueriesState, key: Score, id: QueryId, baseScore: int, maxCap: Score): QueriesState
    requires QueriesConsistent(state)
      ensures QueriesConsistent(state) ==> QueriesConsistent(Remove(state, key, id, baseScore, maxCap))
      ensures forall bound :: EntryIdsBelow(state.entries, bound) ==> EntryIdsBelow(Remove(state, key, id, baseScore, maxCap).entries, bound)
  {
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