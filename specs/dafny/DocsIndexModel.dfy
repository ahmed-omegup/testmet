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
    forall i, j :: 0 <= i < j < |es| ==> LexLt(es[i], es[j])
  }

  lemma SortedEntriesWithSameMembersAreEqual(left: seq<Entry>, right: seq<Entry>)
    requires SortedEntries(left) && SortedEntries(right)
    requires forall entry: Entry :: entry in left <==> entry in right
    ensures left == right
    decreases |left| + |right|
  {
    if |left| == 0 {
      if |right| > 0 {
        assert right[0] in right;
        assert right[0] in left;
        assert false;
      }
      assert right == [];
    } else if |right| == 0 {
      assert left[0] in left;
      assert left[0] in right;
      assert false;
      assert left == [];
    } else {
      assert left[0] in right;
      assert right[0] in left;
      var leftHeadInRight :| 0 <= leftHeadInRight < |right| && right[leftHeadInRight] == left[0];
      var rightHeadInLeft :| 0 <= rightHeadInLeft < |left| && left[rightHeadInLeft] == right[0];
      assert left[0] == right[0];
      assert left[0] !in left[1..];
      assert right[0] !in right[1..];
      forall entry: Entry
        ensures entry in left[1..] <==> entry in right[1..]
      {
        assert entry in left <==> entry in right;
        if entry != left[0] {
          assert entry in left <==> entry in left[1..];
          assert entry in right <==> entry in right[1..];
        }
      }
      SortedEntriesWithSameMembersAreEqual(left[1..], right[1..]);
    }
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

  lemma RankWithIdFindsEntry(es: seq<Entry>, index: nat)
    requires SortedEntries(es)
    requires index < |es|
    ensures RankWithId(es, es[index].score, es[index].id) == index
    decreases index
  {
    if index > 0 {
      RankWithIdFindsEntry(es[1..], index - 1);
    }
  }

  function InsertUnique(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    ensures forall entry :: entry in InsertUnique(es, score, id) <==> entry in es || entry == Entry(score, id)
    ensures SortedEntries(InsertUnique(es, score, id))
  {
    if |es| == 0 then [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then [Entry(score, id)] + es
    else
      var tail := InsertUnique(es[1..], score, id);
      assert SortedEntries([es[0]] + tail) by {
        forall index | 0 <= index < |tail|
          ensures LexLt(es[0], tail[index])
        {
          assert tail[index] in tail;
          if tail[index] in es[1..] {
            assert exists oldIndex :: 1 <= oldIndex < |es| && es[oldIndex] == tail[index];
          } else {
            assert tail[index] == Entry(score, id);
          }
        }
      }
      [es[0]] + tail
  }

  function RemoveOne(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    ensures forall entry :: entry in RemoveOne(es, score, id) <==> entry in es && entry != Entry(score, id)
    ensures SortedEntries(RemoveOne(es, score, id))
  {
    if |es| == 0 then es
    else if es[0].score == score && es[0].id == id then es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then es
    else
      var tail := RemoveOne(es[1..], score, id);
      assert SortedEntries([es[0]] + tail) by {
        forall index | 0 <= index < |tail|
          ensures LexLt(es[0], tail[index])
        {
          assert tail[index] in tail;
          assert tail[index] in es[1..];
          assert exists oldIndex :: 1 <= oldIndex < |es| && es[oldIndex] == tail[index];
        }
      }
      [es[0]] + tail
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

  lemma PositionAtPrefix(prefix: seq<Entry>, suffix: seq<Entry>, index: nat)
    requires SortedEntries(prefix)
    requires SortedEntries(prefix + suffix)
    requires index < |prefix|
    ensures PositionAt(prefix + suffix, index) == PositionAt(prefix, index)
    decreases index
  {
    if index > 0 {
      PositionAtPrefix(prefix, suffix, index - 1);
    }
  }

  lemma PositionAtSuffix(prefix: seq<Entry>, suffix: seq<Entry>, index: nat)
    requires SortedEntries(suffix)
    requires SortedEntries(prefix + suffix)
    requires index < |suffix|
    requires |prefix| == 0 || prefix[|prefix| - 1].score != suffix[0].score
    ensures PositionAt(prefix + suffix, |prefix| + index) == PositionAt(suffix, index)
    decreases index
  {
    if index > 0 {
      PositionAtSuffix(prefix, suffix, index - 1);
    }
  }

  lemma CountStrictLessZero(es: seq<Entry>, score: Score)
    requires forall index :: 0 <= index < |es| ==> score <= es[index].score
    ensures CountStrictLessScore(es, score) == 0
    decreases |es|
  {
    if |es| > 0 {
      CountStrictLessZero(es[1..], score);
    }
  }

  lemma CountStrictLessAtBucketStart(es: seq<Entry>, index: nat)
    requires SortedEntries(es)
    requires index < |es|
    requires index == 0 || es[index - 1].score < es[index].score
    ensures CountStrictLessScore(es, es[index].score) == index
    decreases index
  {
    if index == 0 {
      CountStrictLessZero(es, es[0].score);
    } else {
      CountStrictLessAtBucketStart(es[1..], index - 1);
    }
  }

  lemma PositionAtMatchesScoreRank(es: seq<Entry>, index: nat)
    requires SortedEntries(es)
    requires index < |es|
    ensures CountStrictLessScore(es, es[index].score) <= index
    ensures PositionAt(es, index) == index - CountStrictLessScore(es, es[index].score)
    decreases index
  {
    if index == 0 || es[index - 1].score != es[index].score {
      CountStrictLessAtBucketStart(es, index);
    } else {
      PositionAtMatchesScoreRank(es, index - 1);
    }
  }

  function CollectRange(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SortedEntries(es)
  {
    if |es| == 0 || limit == 0 then []
    else if es[0].score < minScore then CollectRange(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then []
    else [es[0].id] + CollectRange(es[1..], minScore, maxScore, limit - 1)
  }

  lemma CollectRangeSound(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat)
    requires SortedEntries(es)
    ensures |CollectRange(es, minScore, maxScore, limit)| <= limit
    ensures forall docId: DocId :: docId in CollectRange(es, minScore, maxScore, limit) ==>
      exists entry: Entry :: entry in es && entry.id == docId && minScore <= entry.score <= maxScore
    decreases |es|, limit
  {
    if |es| > 0 && limit > 0 {
      if es[0].score < minScore {
        CollectRangeSound(es[1..], minScore, maxScore, limit);
      } else if es[0].score <= maxScore {
        CollectRangeSound(es[1..], minScore, maxScore, limit - 1);
      }
    }
  }

  lemma RankNoDocMatchesPrefix(es: seq<Entry>, score: Score)
    ensures Rank(es, score, NoDoc) == CountStrictLessScore(es, score)
  {
  }

  lemma RankWithinBounds(es: seq<Entry>, score: Score, id: MaybeDocId)
    ensures Rank(es, score, id) <= |es|
  {
    match id
    case NoDoc =>
      CountStrictLessWithinBounds(es, score);
    case SomeDoc(doc) =>
      RankWithIdWithinBounds(es, score, doc);
  }

  lemma CountStrictLessWithinBounds(es: seq<Entry>, score: Score)
    ensures CountStrictLessScore(es, score) <= |es|
  {
    if |es| == 0 {
    } else {
      CountStrictLessWithinBounds(es[1..], score);
      if es[0].score < score {
        assert CountStrictLessScore(es, score) == 1 + CountStrictLessScore(es[1..], score);
        assert |es| == 1 + |es[1..]|;
      }
    }
  }

  lemma RankWithIdWithinBounds(es: seq<Entry>, score: Score, id: DocId)
    ensures RankWithId(es, score, id) <= |es|
  {
    if |es| == 0 {
    } else if es[0].score < score || (es[0].score == score && es[0].id < id) {
      RankWithIdWithinBounds(es[1..], score, id);
      assert RankWithId(es, score, id) == 1 + RankWithId(es[1..], score, id);
      assert |es| == 1 + |es[1..]|;
    }
  }

  lemma CountAtMostMonotone(es: seq<Entry>, lo: Score, hi: Score)
    requires lo <= hi
    ensures CountAtMost(es, lo) <= CountAtMost(es, hi)
  {
    if |es| == 0 {
    } else {
      CountAtMostMonotone(es[1..], lo, hi);
      if es[0].score <= lo {
        assert es[0].score <= hi;
      }
    }
  }
}