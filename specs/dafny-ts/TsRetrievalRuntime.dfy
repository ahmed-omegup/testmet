include "ThunderDbStack.dfy"

module TsRetrievalRuntime {
  import opened DocsIndexModel
  import opened ThunderDbStack

  datatype RetrievalWorkerState = RetrievalWorkerState(
    pendingBatch: map<DocId, seq<QueryId>>,
    pendingOrder: seq<DocId>,
    processingBatch: map<DocId, seq<QueryId>>,
    processingOrder: seq<DocId>,
    stopped: bool)

  datatype StateChange = StateChange(state: RetrievalWorkerState, changed: bool)

  function EmptyWorkerState(): RetrievalWorkerState {
    RetrievalWorkerState(map[], [], map[], [], false)
  }

  function RemoveQueryId(ids: seq<QueryId>, id: QueryId): seq<QueryId> {
    if |ids| == 0 then []
    else if ids[0] == id then ids[1..]
    else [ids[0]] + RemoveQueryId(ids[1..], id)
  }

  function UniqueQueryIds(ids: seq<QueryId>): bool {
    if |ids| == 0 then true
    else !ContainsQueryId(ids[1..], ids[0]) && UniqueQueryIds(ids[1..])
  }

  predicate RegistryConsistent(batch: map<DocId, seq<QueryId>>, order: seq<DocId>) {
    UniqueDocIds(order) &&
    (forall docId :: docId in batch ==> ContainsId(order, docId)) &&
    (forall docId :: docId in batch ==> UniqueQueryIds(batch[docId]))
  }

  predicate WorkerConsistent(state: RetrievalWorkerState) {
    RegistryConsistent(state.pendingBatch, state.pendingOrder) &&
    RegistryConsistent(state.processingBatch, state.processingOrder)
  }

  function CanRegister(state: RetrievalWorkerState, docId: DocId, queryId: QueryId): bool {
    !(docId in state.processingBatch && ContainsQueryId(state.processingBatch[docId], queryId))
  }

  function Register(state: RetrievalWorkerState, docId: DocId, queryId: QueryId): RetrievalWorkerState
    requires CanRegister(state, docId, queryId)
  {
    var nextQueries := if docId in state.pendingBatch then AppendQueryIdUnique(state.pendingBatch[docId], queryId) else [queryId];
    var nextOrder := if docId in state.pendingBatch then state.pendingOrder else AppendDocIdIfMissing(state.pendingOrder, docId);
    RetrievalWorkerState(state.pendingBatch[docId := nextQueries], nextOrder, state.processingBatch, state.processingOrder, state.stopped)
  }

  function Cancel(state: RetrievalWorkerState, docId: DocId, queryId: QueryId): StateChange {
    if docId in state.pendingBatch then
      var removed := ContainsQueryId(state.pendingBatch[docId], queryId);
      var nextQueries := RemoveQueryId(state.pendingBatch[docId], queryId);
      var nextBatch := if removed && |nextQueries| == 0 then map key | key in state.pendingBatch && key != docId :: state.pendingBatch[key]
                       else if removed then state.pendingBatch[docId := nextQueries]
                       else state.pendingBatch;
      var nextOrder := if removed && !(docId in nextBatch) then RemoveDocId(state.pendingOrder, docId) else state.pendingOrder;
      StateChange(RetrievalWorkerState(nextBatch, nextOrder, state.processingBatch, state.processingOrder, state.stopped), removed)
    else if docId in state.processingBatch then
      var removed := ContainsQueryId(state.processingBatch[docId], queryId);
      var nextQueries := RemoveQueryId(state.processingBatch[docId], queryId);
      var nextBatch := if removed && |nextQueries| == 0 then map key | key in state.processingBatch && key != docId :: state.processingBatch[key]
                       else if removed then state.processingBatch[docId := nextQueries]
                       else state.processingBatch;
      var nextOrder := if removed && !(docId in nextBatch) then RemoveDocId(state.processingOrder, docId) else state.processingOrder;
      StateChange(RetrievalWorkerState(state.pendingBatch, state.pendingOrder, nextBatch, nextOrder, state.stopped), removed)
    else
      StateChange(state, false)
  }

  function ResolveDoc(state: RetrievalWorkerState, docId: DocId): StateChange {
    var removedPending := docId in state.pendingBatch;
    var removedProcessing := docId in state.processingBatch;
    var nextPending := map key | key in state.pendingBatch && key != docId :: state.pendingBatch[key];
    var nextProcessing := map key | key in state.processingBatch && key != docId :: state.processingBatch[key];
    StateChange(
      RetrievalWorkerState(nextPending, RemoveDocId(state.pendingOrder, docId), nextProcessing, RemoveDocId(state.processingOrder, docId), state.stopped),
      removedPending || removedProcessing)
  }

  function BeginCycle(state: RetrievalWorkerState): RetrievalWorkerState {
    RetrievalWorkerState(map[], [], state.pendingBatch, state.pendingOrder, state.stopped)
  }

  function FinishCycle(state: RetrievalWorkerState): RetrievalWorkerState {
    RetrievalWorkerState(state.pendingBatch, state.pendingOrder, map[], [], state.stopped)
  }

  function Stop(state: RetrievalWorkerState): RetrievalWorkerState {
    RetrievalWorkerState(state.pendingBatch, state.pendingOrder, state.processingBatch, state.processingOrder, true)
  }

  function HasPendingWork(state: RetrievalWorkerState): bool {
    |state.pendingOrder| > 0
  }

  function ShouldExit(state: RetrievalWorkerState): bool {
    state.stopped && !HasPendingWork(state)
  }

  function BuildPayload(state: RetrievalWorkerState, store: map<DocId, DocState>): seq<RetrievalDoc>
    decreases |state.processingOrder|
  {
    BuildPayloadFrom(state.processingOrder, state.processingBatch, store)
  }

  function BuildPayloadFrom(order: seq<DocId>, batch: map<DocId, seq<QueryId>>, store: map<DocId, DocState>): seq<RetrievalDoc>
    decreases |order|
  {
    if |order| == 0 then []
    else if !(order[0] in batch) then BuildPayloadFrom(order[1..], batch, store)
    else
      match LookupState(store, order[0])
      case NoState => BuildPayloadFrom(order[1..], batch, store)
      case HasState(state) => [RetrievalDoc(order[0], state, batch[order[0]])] + BuildPayloadFrom(order[1..], batch, store)
  }
}