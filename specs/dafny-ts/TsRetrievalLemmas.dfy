include "TsRetrievalRuntime.dfy"

module TsRetrievalLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsRetrievalRuntime

  lemma RegisterAddsPendingDoc(state: RetrievalWorkerState, docId: DocId, queryId: QueryId)
    requires CanRegister(state, docId, queryId)
    ensures docId in Register(state, docId, queryId).pendingBatch
  {
  }

  lemma BeginCycleMovesPending(state: RetrievalWorkerState)
    ensures BeginCycle(state).processingBatch == state.pendingBatch
    ensures BeginCycle(state).processingOrder == state.pendingOrder
    ensures BeginCycle(state).pendingBatch == map[]
    ensures BeginCycle(state).pendingOrder == []
  {
  }

  lemma ResolveDocDropsDoc(state: RetrievalWorkerState, docId: DocId)
    ensures !(docId in ResolveDoc(state, docId).state.pendingBatch)
    ensures !(docId in ResolveDoc(state, docId).state.processingBatch)
  {
  }
}