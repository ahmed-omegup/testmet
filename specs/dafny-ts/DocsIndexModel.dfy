module DocsIndexModel {
  type Score = int
  type DocId = int

  datatype MaybeDocId =
    | NoDoc
    | SomeDoc(doc: DocId)

  datatype AtRank =
    | Missing
    | Found(score: Score, id: DocId, position: nat)

  datatype Entry = Entry(score: Score, id: DocId)

  function LexLt(a: Entry, b: Entry): bool {
    a.score < b.score || (a.score == b.score && a.id < b.id)
  }

  predicate SortedEntries(es: seq<Entry>) {
    if |es| < 2 then true
    else LexLt(es[0], es[1]) && SortedEntries(es[1..])
  }

  function CountStrictLessScore(es: seq<Entry>, score: Score): nat {
    if |es| == 0 then 0
    else (if es[0].score < score then 1 else 0) + CountStrictLessScore(es[1..], score)
  }

  function CountAtMost(es: seq<Entry>, score: Score): nat {
    if |es| == 0 then 0
    else (if es[0].score <= score then 1 else 0) + CountAtMost(es[1..], score)
  }

  function RankWithId(es: seq<Entry>, score: Score, id: DocId): nat {
    if |es| == 0 then 0
    else if es[0].score < score || (es[0].score == score && es[0].id < id)
      then 1 + RankWithId(es[1..], score, id)
      else 0
  }

  function Rank(es: seq<Entry>, score: Score, id: MaybeDocId): nat {
    match id
    case NoDoc => CountStrictLessScore(es, score)
    case SomeDoc(doc) => RankWithId(es, score, doc)
  }

  function InsertUnique(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    ensures SortedEntries(InsertUnique(es, score, id))
  {
    if |es| == 0 then [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then [Entry(score, id)] + es
    else [es[0]] + InsertUnique(es[1..], score, id)
  }

  function RemoveOne(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    ensures SortedEntries(RemoveOne(es, score, id))
  {
    if |es| == 0 then es
    else if es[0].score == score && es[0].id == id then es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then es
    else [es[0]] + RemoveOne(es[1..], score, id)
  }

  function PositionAt(es: seq<Entry>, idx: nat): nat
    requires SortedEntries(es)
    requires idx < |es|
  {
    if idx == 0 then 0
    else if es[idx - 1].score == es[idx].score then 1 + PositionAt(es, idx - 1) else 0
  }

  function GetAtRank(es: seq<Entry>, rank: nat): AtRank
    requires SortedEntries(es)
  {
    if rank >= |es| then Missing
    else Found(es[rank].score, es[rank].id, PositionAt(es, rank))
  }

  function CollectRange(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SortedEntries(es)
  {
    if |es| == 0 || limit == 0 then []
    else if es[0].score < minScore then CollectRange(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then []
    else [es[0].id] + CollectRange(es[1..], minScore, maxScore, limit - 1)
  }
}