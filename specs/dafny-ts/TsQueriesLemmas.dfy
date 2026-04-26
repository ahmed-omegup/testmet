include "TsQueriesRuntime.dfy"

module TsQueriesLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsQueriesRuntime

  lemma InsertKeepsRangeAddLog(state: QueriesState, key: Score, id: QueryId, effectiveScore: int, maxCap: Score)
    ensures Insert(state, key, id, effectiveScore, maxCap).rangeAdds == state.rangeAdds
  {
  }

  lemma InsertRecoversEffectiveScore(state: QueriesState, key: Score, id: QueryId, effectiveScore: int, maxCap: Score)
    requires !ContainsQueryEntryId(state.entries, id)
    ensures EffectiveScore(Insert(state, key, id, effectiveScore, maxCap), QueryEntry(id, key, effectiveScore - AccumulatedAddAtKey(state, key), maxCap)) == effectiveScore
  {
  }

  lemma RangeAddAppendsOperation(state: QueriesState, threshold: Score, delta: int)
    ensures RangeAddKeysGreaterThan(state, threshold, delta).rangeAdds == state.rangeAdds + [RangeAddOp(threshold, delta)]
  {
  }
}