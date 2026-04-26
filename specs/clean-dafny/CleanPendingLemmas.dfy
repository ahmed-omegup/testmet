include "CleanPendingRuntime.dfy"

module CleanPendingLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened CleanPendingRuntime

  lemma RemoveQueryIdDoesNotGrow(ids: seq<QueryId>, id: QueryId)
    ensures |RemoveQueryId(ids, id)| <= |ids|
    decreases |ids|
  {
    if |ids| == 0 {
    } else if ids[0] == id {
    } else {
      RemoveQueryIdDoesNotGrow(ids[1..], id);
    }
  }

  lemma ResolvePendingDropsDoc(state: PendingState, docId: DocId)
    ensures !(docId in ResolvePendingForDoc(state, docId).byDoc)
  {
  }
}