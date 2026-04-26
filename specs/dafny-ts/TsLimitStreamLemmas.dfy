include "TsLimitStreamRuntime.dfy"

module TsLimitStreamLemmas {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsLimitQueriesRuntime
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

  lemma SetQueriesKeepsStreamConsistency(state: LimitStreamState, queries: LimitQueriesState)
    requires WorkerConsistent(state.retrieval)
    requires LimitQueriesConsistent(queries)
    ensures LimitStreamConsistent(SetQueries(state, queries))
  {
  }

  lemma NotifyRetrievalResolvedKeepsQueryConsistency(state: LimitStreamState, docId: DocId)
    requires LimitStreamConsistent(state)
    ensures LimitQueriesConsistent(NotifyRetrievalResolved(state, docId).queries)
  {
  }

  lemma SeedDocsQueriesKeepsConsistency(queries: LimitQueriesState, docs: seq<SeedDoc>)
    requires LimitQueriesConsistent(queries)
    ensures LimitQueriesConsistent(SeedDocsQueries(queries, docs))
  {
  }

  lemma HandleLostQueriesKeepsQueryConsistency(state: LimitStreamState, queries: seq<QueryId>)
    requires LimitQueriesConsistent(state.queries)
    ensures LimitQueriesConsistent(HandleLostQueries(state, queries).queries)
  {
  }

  lemma HandleOverflowQueriesKeepsQueryConsistency(state: LimitStreamState, queries: seq<QueryId>)
    requires LimitQueriesConsistent(state.queries)
    ensures LimitQueriesConsistent(HandleOverflowQueries(state, queries).state.queries)
  {
  }

  lemma ResolveDeliveredDocsKeepsConsistency(queries: LimitQueriesState, docs: seq<RetrievalDoc>)
    requires LimitQueriesConsistent(queries)
    ensures LimitQueriesConsistent(ResolveDeliveredDocs(queries, docs))
  {
  }
}