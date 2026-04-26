include "TsLimitStreamRuntime.dfy"

module TsLimitStreamLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsLimitStreamRuntime
  import opened TsRetrievalRuntime

  lemma EmptyStreamIsConsistent()
    ensures LimitStreamConsistent(EmptyLimitStreamState())
  {
  }

  lemma DrainWithoutPendingIsStable(state: LimitStreamState)
    requires LimitStreamConsistent(state)
    requires !HasPendingWork(state.retrieval)
    ensures DrainRetrievalCycle(state) == StreamStep(state, [])
  {
  }
}