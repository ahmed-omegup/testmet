include "TsDocsRuntime.dfy"

module TsDocsLemmas {
  import opened DocsIndexModel
  import opened TsDocsRuntime

  lemma AddDocChangesOnlyEntries(state: DocsState, score: Score, id: DocId)
    requires DocsConsistent(state)
    ensures AddDoc(state, score, id).entries == InsertUnique(state.entries, score, id)
  {
  }

  lemma RemoveDocChangesOnlyEntries(state: DocsState, score: Score, id: DocId)
    requires DocsConsistent(state)
    ensures RemoveDoc(state, score, id).entries == RemoveOne(state.entries, score, id)
  {
  }

  lemma EmptyRankIsZero(score: Score)
    ensures RankDoc(EmptyDocsState(), score, NoDoc) == 0
  {
  }
}