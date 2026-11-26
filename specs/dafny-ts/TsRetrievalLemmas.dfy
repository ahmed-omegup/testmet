include "TsRetrievalRuntime.dfy"

module TsRetrievalLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsRetrievalRuntime

  lemma LoadFailurePreservesWorker(state: LoadRetryState)
    requires !state.exhausted && state.failures <= 3
    ensures LoadFailed(state).worker == state.worker
    ensures LoadFailed(state).failures <= 3
    ensures |state.worker.processingBatch| == 0 ==> !LoadFailed(state).exhausted
    ensures |state.worker.processingBatch| > 0 && state.failures == 3 ==> LoadFailed(state).exhausted
  {
  }

  lemma FourFailedLoadsExhaustRetries(worker: RetrievalWorkerState)
    requires |worker.processingBatch| > 0
    ensures var first := LoadFailed(LoadRetryState(worker, 0, false));
      var second := LoadFailed(first);
      var third := LoadFailed(second);
      var fourth := LoadFailed(third);
      fourth.exhausted && fourth.worker == worker
  {
  }

  lemma RestartPreservesWorker(state: LoadRetryState)
    requires state.exhausted
    ensures RestartFailedLoad(state).worker == state.worker
    ensures RestartFailedLoad(state).failures == 0 && !RestartFailedLoad(state).exhausted
  {
  }

  lemma PayloadOnlyContainsStoredDocs(order: seq<DocId>, batch: map<DocId, seq<QueryId>>, store: map<DocId, DocState>)
    ensures forall index :: 0 <= index < |BuildPayloadFrom(order, batch, store)| ==>
      BuildPayloadFrom(order, batch, store)[index].docId in store
    decreases |order|
  {
    if |order| > 0 {
      PayloadOnlyContainsStoredDocs(order[1..], batch, store);
    }
  }

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

  lemma CancelRespectsBatch(state: RetrievalWorkerState, docId: DocId, queryId: QueryId, batchNumber: BatchNumber)
    ensures batchNumber != state.pendingBatchNumber ==> Cancel(state, docId, queryId, batchNumber) == StateChange(state, false)
    ensures Cancel(state, docId, queryId, batchNumber).state.processingBatch == state.processingBatch
    ensures Cancel(state, docId, queryId, batchNumber).state.processingOrder == state.processingOrder
    ensures forall other :: other != docId ==>
      (other in Cancel(state, docId, queryId, batchNumber).state.pendingBatch <==> other in state.pendingBatch)
  {
  }

  lemma ResolveDocRemovesAtMostOneBatch(state: RetrievalWorkerState, docId: DocId, batchHint: BatchNumber)
    ensures !ResolveDoc(state, docId, batchHint).changed ==> ResolveDoc(state, docId, batchHint).state == state
    ensures ResolveDoc(state, docId, batchHint).state.pendingBatch == state.pendingBatch ||
      ResolveDoc(state, docId, batchHint).state.processingBatch == state.processingBatch
    ensures ResolveDoc(state, docId, batchHint).changed ==>
      (!(docId in ResolveDoc(state, docId, batchHint).state.pendingBatch) ||
       !(docId in ResolveDoc(state, docId, batchHint).state.processingBatch))
  {
  }

  lemma ResolveDocCanLeaveAnotherBatch()
    ensures var state := RetrievalWorkerState(map[5 := [2]], [5], 2, map[5 := [1]], [5], 1, false);
      5 in ResolveDoc(state, 5, 1).state.pendingBatch &&
      !(5 in ResolveDoc(state, 5, 1).state.processingBatch)
  {
  }

  lemma StaleHintCanResolveAnotherBatch()
    ensures var state := RetrievalWorkerState(map[], [], 2, map[5 := [1]], [5], 1, false);
      ResolveDoc(state, 5, 99).changed && !(5 in ResolveDoc(state, 5, 99).state.processingBatch)
  {
  }
}