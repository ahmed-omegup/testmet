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
    ensures BeginCycle(state).processingBatchNumber == state.pendingBatchNumber
    ensures BeginCycle(state).pendingBatchNumber == state.pendingBatchNumber + 1
  {
  }

  lemma ResolveDocDropsDoc(state: RetrievalWorkerState, docId: DocId, batchHint: BatchNumber)
    ensures !(docId in ResolveDoc(state, docId, batchHint).state.pendingBatch)
    ensures !(docId in ResolveDoc(state, docId, batchHint).state.processingBatch)
  {
  }
}