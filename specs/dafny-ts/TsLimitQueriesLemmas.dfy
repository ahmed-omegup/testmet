include "TsLimitQueriesRuntime.dfy"

module TsLimitQueriesLemmas {
  import opened DocsIndexModel
  import opened TsLimitQueriesRuntime

  lemma AddQueryAdvancesNextId(state: LimitQueriesState, a: Score, k: nat, max: Score)
    requires LimitQueriesConsistent(state)
    ensures TsLimitQueriesRuntime.AddQuery(state, a, k, max).state.nextId == state.nextId + 1
  {
  }

  lemma ResolvePendingWithoutDocIsStable(state: LimitQueriesState, docId: DocId)
    requires LimitQueriesConsistent(state)
    ensures ResolvePendingForDoc(state, docId) == state
  {
  }
}