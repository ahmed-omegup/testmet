include "../dafny/DocsIndexModel.dfy"

module TsDocsRuntime {
  import opened DocsIndexModel

  datatype DocsState = DocsState(entries: seq<Entry>)

  function EmptyDocsState(): DocsState {
    DocsState([])
  }

  predicate DocsConsistent(state: DocsState) {
    SortedEntries(state.entries)
  }

  function AddDoc(state: DocsState, score: Score, id: DocId): DocsState
    requires DocsConsistent(state)
  {
    DocsState(InsertUnique(state.entries, score, id))
  }

  function RemoveDoc(state: DocsState, score: Score, id: DocId): DocsState
    requires DocsConsistent(state)
  {
    DocsState(RemoveOne(state.entries, score, id))
  }

  function RankDoc(state: DocsState, score: Score, id: MaybeDocId): nat
    requires DocsConsistent(state)
  {
    Rank(state.entries, score, id)
  }

  function CountAtMostDoc(state: DocsState, score: Score): nat
    requires DocsConsistent(state)
  {
    CountAtMost(state.entries, score)
  }

  function GetAtRankDoc(state: DocsState, rank: nat): AtRank
    requires DocsConsistent(state)
  {
    GetAtRank(state.entries, rank)
  }

  function CollectRangeDocs(state: DocsState, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires DocsConsistent(state)
  {
    CollectRange(state.entries, minScore, maxScore, limit)
  }
}