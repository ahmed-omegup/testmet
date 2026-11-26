include "DocsIndexModel.dfy"

module DocsIndexTreap {
  import opened DocsIndexModel

  type Priority = int

  datatype MaybeScore =
    | NoScore
    | SomeScore(v: Score)

  datatype Treap =
    | Empty
    | Node(score: Score, ids: seq<DocId>, prio: Priority, sum: nat, left: Treap, right: Treap)

  function NodeCount(t: Treap): nat {
    if t.Empty? then 0 else 1 + NodeCount(t.left) + NodeCount(t.right)
  }

  function Sum(t: Treap): nat {
    if t.Empty? then 0 else t.sum
  }

  function StructuralSum(t: Treap): nat {
    if t.Empty? then 0 else |t.ids| + StructuralSum(t.left) + StructuralSum(t.right)
  }

  predicate SortedStrictIds(ids: seq<DocId>) {
    forall i, j :: 0 <= i < j < |ids| ==> ids[i] < ids[j]
  }

  predicate ScoreAboveLower(score: Score, lo: MaybeScore) {
    match lo
    case NoScore => true
    case SomeScore(v) => v < score
  }

  predicate ScoreBelowUpper(score: Score, hi: MaybeScore) {
    match hi
    case NoScore => true
    case SomeScore(v) => score < v
  }

  function RootPrio(t: Treap): Priority {
    if t.Node? then t.prio else 0
  }

  predicate SumConsistent(t: Treap) {
    if t.Empty? then true
    else
      SumConsistent(t.left) &&
      SumConsistent(t.right) &&
      t.sum == |t.ids| + Sum(t.left) + Sum(t.right)
  }

  predicate HeapOrdered(t: Treap) {
    if t.Empty? then true
    else
      (if t.left.Node? then t.left.prio <= t.prio else true) &&
      (if t.right.Node? then t.right.prio <= t.prio else true) &&
      HeapOrdered(t.left) &&
      HeapOrdered(t.right)
  }

  predicate OrderedByScore(t: Treap, lo: MaybeScore, hi: MaybeScore) {
    if t.Empty? then true
    else
      ScoreAboveLower(t.score, lo) &&
      ScoreBelowUpper(t.score, hi) &&
      OrderedByScore(t.left, lo, SomeScore(t.score)) &&
      OrderedByScore(t.right, SomeScore(t.score), hi)
  }

  ghost predicate LowerBoundRelaxed(original: MaybeScore, relaxed: MaybeScore) {
    relaxed.NoScore? || (original.SomeScore? && relaxed.SomeScore? && relaxed.v <= original.v)
  }

  ghost predicate UpperBoundRelaxed(original: MaybeScore, relaxed: MaybeScore) {
    relaxed.NoScore? || (original.SomeScore? && relaxed.SomeScore? && original.v <= relaxed.v)
  }

  lemma OrderedByScoreRelaxBounds(t: Treap, lo: MaybeScore, hi: MaybeScore, newLo: MaybeScore, newHi: MaybeScore)
    requires OrderedByScore(t, lo, hi)
    requires LowerBoundRelaxed(lo, newLo)
    requires UpperBoundRelaxed(hi, newHi)
    ensures OrderedByScore(t, newLo, newHi)
    decreases NodeCount(t)
  {
    if t.Node? {
      OrderedByScoreRelaxBounds(t.left, lo, SomeScore(t.score), newLo, SomeScore(t.score));
      OrderedByScoreRelaxBounds(t.right, SomeScore(t.score), hi, SomeScore(t.score), newHi);
    }
  }

  predicate IdsSortedInTree(t: Treap) {
    if t.Empty? then true
    else SortedStrictIds(t.ids) && IdsSortedInTree(t.left) && IdsSortedInTree(t.right)
  }

  predicate NonEmptyBuckets(t: Treap) {
    if t.Empty? then true
    else |t.ids| > 0 && NonEmptyBuckets(t.left) && NonEmptyBuckets(t.right)
  }

  predicate ValidTreap(t: Treap) {
    SumConsistent(t) &&
    HeapOrdered(t) &&
    OrderedByScore(t, NoScore, NoScore) &&
    IdsSortedInTree(t) &&
    NonEmptyBuckets(t)
  }

  function EntriesFromIds(score: Score, ids: seq<DocId>): seq<Entry> {
    if |ids| == 0 then []
    else [Entry(score, ids[0])] + EntriesFromIds(score, ids[1..])
  }

  function Entries(t: Treap): seq<Entry> {
    if t.Empty? then []
    else Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right)
  }

  function InsertId(ids: seq<DocId>, id: DocId): seq<DocId> {
    if |ids| == 0 then [id]
    else if ids[0] == id then ids
    else if id < ids[0] then [id] + ids
    else [ids[0]] + InsertId(ids[1..], id)
  }

  lemma InsertIdProperties(ids: seq<DocId>, id: DocId)
    requires SortedStrictIds(ids)
    ensures SortedStrictIds(InsertId(ids, id))
    ensures |InsertId(ids, id)| > 0
    ensures forall other: DocId :: other in InsertId(ids, id) <==> other in ids || other == id
    decreases |ids|
  {
    if |ids| > 0 && ids[0] < id {
      InsertIdProperties(ids[1..], id);
      var tail := InsertId(ids[1..], id);
      forall index | 0 <= index < |tail|
        ensures ids[0] < tail[index]
      {
        assert tail[index] in tail;
        if tail[index] in ids[1..] {
          assert exists oldIndex :: 1 <= oldIndex < |ids| && ids[oldIndex] == tail[index];
        } else {
          assert tail[index] == id;
        }
      }
      assert SortedStrictIds([ids[0]] + tail);
    }
  }

  function RemoveId(ids: seq<DocId>, id: DocId): seq<DocId> {
    if |ids| == 0 then ids
    else if ids[0] == id then ids[1..]
    else if id < ids[0] then ids
    else [ids[0]] + RemoveId(ids[1..], id)
  }

  lemma RemoveIdProperties(ids: seq<DocId>, id: DocId)
    requires SortedStrictIds(ids)
    ensures SortedStrictIds(RemoveId(ids, id))
    ensures |RemoveId(ids, id)| <= |ids|
    ensures forall other: DocId :: other in RemoveId(ids, id) <==> other in ids && other != id
    decreases |ids|
  {
    if |ids| > 0 && ids[0] < id {
      RemoveIdProperties(ids[1..], id);
      var tail := RemoveId(ids[1..], id);
      forall index | 0 <= index < |tail|
        ensures ids[0] < tail[index]
      {
        assert tail[index] in ids[1..];
        assert exists oldIndex :: 1 <= oldIndex < |ids| && ids[oldIndex] == tail[index];
      }
      assert SortedStrictIds([ids[0]] + tail);
    }
  }

  lemma RemoveIdLength(ids: seq<DocId>, id: DocId)
    requires SortedStrictIds(ids)
    ensures |RemoveId(ids, id)| == (if id in ids then |ids| - 1 else |ids|)
    decreases |ids|
  {
    if |ids| > 0 && ids[0] < id {
      RemoveIdLength(ids[1..], id);
    }
  }

  function InsertionIndex(ids: seq<DocId>, id: DocId): nat {
    InsertionIndexFrom(ids, id, 0)
  }

  function InsertionIndexFrom(ids: seq<DocId>, id: DocId, index: nat): (result: nat)
    requires index <= |ids|
    decreases |ids| - index
  {
    if index == |ids| || ids[index] >= id then index
    else InsertionIndexFrom(ids, id, index + 1)
  } by method {
    var cursor := index;
    while cursor < |ids| && ids[cursor] < id
      invariant index <= cursor <= |ids|
      invariant InsertionIndexFrom(ids, id, index) == InsertionIndexFrom(ids, id, cursor)
      decreases |ids| - cursor
    {
      cursor := cursor + 1;
    }
    result := cursor;
  }

  ghost function InsertionIndexReference(ids: seq<DocId>, id: DocId): nat {
    if |ids| == 0 then 0
    else if ids[0] < id then 1 + InsertionIndexReference(ids[1..], id)
    else 0
  }

  lemma InsertionIndexFromMatchesReference(ids: seq<DocId>, id: DocId, index: nat)
    requires index <= |ids|
    ensures InsertionIndexFrom(ids, id, index) == index + InsertionIndexReference(ids[index..], id)
    decreases |ids| - index
  {
    if index < |ids| && ids[index] < id {
      InsertionIndexFromMatchesReference(ids, id, index + 1);
      assert ids[index..][1..] == ids[index + 1..];
    }
  }

  lemma InsertionIndexMatchesReference(ids: seq<DocId>, id: DocId)
    ensures InsertionIndex(ids, id) == InsertionIndexReference(ids, id)
  {
    InsertionIndexFromMatchesReference(ids, id, 0);
  }

  function Pull(t: Treap): Treap
    requires t.Node?
  {
    Node(t.score, t.ids, t.prio, |t.ids| + Sum(t.left) + Sum(t.right), t.left, t.right)
  }

  function RotateRight(t: Treap): Treap
    requires t.Node? && t.left.Node?
  {
    var demoted := Pull(Node(t.score, t.ids, t.prio, 0, t.left.right, t.right));
    Pull(Node(t.left.score, t.left.ids, t.left.prio, 0, t.left.left, demoted))
  }

  function RotateLeft(t: Treap): Treap
    requires t.Node? && t.right.Node?
  {
    var demoted := Pull(Node(t.score, t.ids, t.prio, 0, t.left, t.right.left));
    Pull(Node(t.right.score, t.right.ids, t.right.prio, 0, demoted, t.right.right))
  }

  function Join(left: Treap, right: Treap): Treap
    requires SumConsistent(left)
    requires SumConsistent(right)
    decreases NodeCount(left) + NodeCount(right)
    ensures SumConsistent(Join(left, right))
  {
    if left.Empty? then right
    else if right.Empty? then left
    else if left.prio > right.prio then
      Pull(Node(left.score, left.ids, left.prio, 0, left.left, Join(left.right, right)))
    else
      Pull(Node(right.score, right.ids, right.prio, 0, Join(left, right.left), right.right))
  }

  lemma JoinPreservesBucketInvariants(left: Treap, right: Treap)
    requires SumConsistent(left) && SumConsistent(right)
    requires IdsSortedInTree(left) && IdsSortedInTree(right)
    requires NonEmptyBuckets(left) && NonEmptyBuckets(right)
    ensures IdsSortedInTree(Join(left, right))
    ensures NonEmptyBuckets(Join(left, right))
    decreases NodeCount(left) + NodeCount(right)
  {
    if left.Node? && right.Node? {
      if left.prio > right.prio {
        JoinPreservesBucketInvariants(left.right, right);
      } else {
        JoinPreservesBucketInvariants(left, right.left);
      }
    }
  }

  lemma JoinPreservesHeap(left: Treap, right: Treap)
    requires SumConsistent(left) && SumConsistent(right)
    requires HeapOrdered(left) && HeapOrdered(right)
    ensures HeapOrdered(Join(left, right))
    ensures left.Node? && right.Node? ==> (Join(left, right).Node? &&
      Join(left, right).prio == (if left.prio > right.prio then left.prio else right.prio))
    decreases NodeCount(left) + NodeCount(right)
  {
    if left.Node? && right.Node? {
      if left.prio > right.prio {
        JoinPreservesHeap(left.right, right);
      } else {
        JoinPreservesHeap(left, right.left);
      }
    }
  }

  lemma JoinPreservesScoreOrder(left: Treap, right: Treap, lo: MaybeScore, hi: MaybeScore, split: Score)
    requires SumConsistent(left) && SumConsistent(right)
    requires OrderedByScore(left, lo, SomeScore(split))
    requires OrderedByScore(right, SomeScore(split), hi)
    requires ScoreAboveLower(split, lo) && ScoreBelowUpper(split, hi)
    ensures OrderedByScore(Join(left, right), lo, hi)
    decreases NodeCount(left) + NodeCount(right)
  {
    if left.Empty? {
      OrderedByScoreRelaxBounds(right, SomeScore(split), hi, lo, hi);
    } else if right.Empty? {
      OrderedByScoreRelaxBounds(left, lo, SomeScore(split), lo, hi);
    } else if left.prio > right.prio {
      JoinPreservesScoreOrder(left.right, right, SomeScore(left.score), hi, split);
    } else {
      JoinPreservesScoreOrder(left, right.left, lo, SomeScore(right.score), split);
    }
  }

  function Add(t: Treap, score: Score, id: DocId, prioForNew: Priority): Treap
    requires SumConsistent(t)
    decreases NodeCount(t)
    ensures SumConsistent(Add(t, score, id, prioForNew))
  {
    if t.Empty? then
      Node(score, [id], prioForNew, 1, Empty, Empty)
    else if score == t.score then
      Pull(Node(t.score, InsertId(t.ids, id), t.prio, 0, t.left, t.right))
    else if score < t.score then
      var left2 := Add(t.left, score, id, prioForNew);
      var n := Pull(Node(t.score, t.ids, t.prio, 0, left2, t.right));
      if left2.Node? && left2.prio > t.prio then RotateRight(n) else n
    else
      var right2 := Add(t.right, score, id, prioForNew);
      var n := Pull(Node(t.score, t.ids, t.prio, 0, t.left, right2));
      if right2.Node? && right2.prio > t.prio then RotateLeft(n) else n
  }

  lemma AddPreservesBucketInvariants(t: Treap, score: Score, id: DocId, priority: Priority)
    requires SumConsistent(t)
    requires IdsSortedInTree(t)
    requires NonEmptyBuckets(t)
    ensures IdsSortedInTree(Add(t, score, id, priority))
    ensures NonEmptyBuckets(Add(t, score, id, priority))
    decreases NodeCount(t)
  {
    if t.Node? {
      if score == t.score {
        InsertIdProperties(t.ids, id);
      } else if score < t.score {
        AddPreservesBucketInvariants(t.left, score, id, priority);
      } else {
        AddPreservesBucketInvariants(t.right, score, id, priority);
      }
    }
  }

  lemma AddPreservesHeap(t: Treap, score: Score, id: DocId, priority: Priority)
    requires SumConsistent(t)
    requires HeapOrdered(t)
    ensures HeapOrdered(Add(t, score, id, priority))
    ensures Add(t, score, id, priority).Node?
    ensures t.Node? ==> Add(t, score, id, priority).prio >= t.prio
    ensures t.Node? && Add(t, score, id, priority).prio > t.prio ==>
      ((!Add(t, score, id, priority).left.Node? || Add(t, score, id, priority).left.prio <= t.prio) &&
       (!Add(t, score, id, priority).right.Node? || Add(t, score, id, priority).right.prio <= t.prio))
    decreases NodeCount(t)
  {
    if t.Node? {
      if score < t.score {
        AddPreservesHeap(t.left, score, id, priority);
      } else if score > t.score {
        AddPreservesHeap(t.right, score, id, priority);
      }
    }
  }

  lemma AddPreservesScoreOrder(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score, id: DocId, priority: Priority)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    requires ScoreAboveLower(score, lo)
    requires ScoreBelowUpper(score, hi)
    ensures OrderedByScore(Add(t, score, id, priority), lo, hi)
    decreases NodeCount(t)
  {
    if t.Node? {
      if score < t.score {
        AddPreservesScoreOrder(t.left, lo, SomeScore(t.score), score, id, priority);
      } else if score > t.score {
        AddPreservesScoreOrder(t.right, SomeScore(t.score), hi, score, id, priority);
      }
    }
  }

  function Remove(t: Treap, score: Score, id: DocId): Treap
    requires SumConsistent(t)
    decreases NodeCount(t)
    ensures SumConsistent(Remove(t, score, id))
  {
    if t.Empty? then
      Empty
    else if score == t.score then
      var ids2 := RemoveId(t.ids, id);
      if |ids2| == |t.ids| then
        Pull(Node(t.score, t.ids, t.prio, 0, t.left, t.right))
      else if |ids2| == 0 then
        Join(t.left, t.right)
      else
        Pull(Node(t.score, ids2, t.prio, 0, t.left, t.right))
    else if score < t.score then
      Pull(Node(t.score, t.ids, t.prio, 0, Remove(t.left, score, id), t.right))
    else
      Pull(Node(t.score, t.ids, t.prio, 0, t.left, Remove(t.right, score, id)))
  }

  lemma RemovePreservesBucketInvariants(t: Treap, score: Score, id: DocId)
    requires SumConsistent(t)
    requires IdsSortedInTree(t)
    requires NonEmptyBuckets(t)
    ensures IdsSortedInTree(Remove(t, score, id))
    ensures NonEmptyBuckets(Remove(t, score, id))
    decreases NodeCount(t)
  {
    if t.Node? {
      if score == t.score {
        RemoveIdProperties(t.ids, id);
        JoinPreservesBucketInvariants(t.left, t.right);
      } else if score < t.score {
        RemovePreservesBucketInvariants(t.left, score, id);
      } else {
        RemovePreservesBucketInvariants(t.right, score, id);
      }
    }
  }

  lemma RemovePreservesHeap(t: Treap, score: Score, id: DocId)
    requires SumConsistent(t)
    requires HeapOrdered(t)
    ensures HeapOrdered(Remove(t, score, id))
    ensures t.Node? && Remove(t, score, id).Node? ==> Remove(t, score, id).prio <= t.prio
    decreases NodeCount(t)
  {
    if t.Node? {
      if score == t.score {
        JoinPreservesHeap(t.left, t.right);
      } else if score < t.score {
        RemovePreservesHeap(t.left, score, id);
      } else {
        RemovePreservesHeap(t.right, score, id);
      }
    }
  }

  lemma RemovePreservesScoreOrder(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score, id: DocId)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    ensures OrderedByScore(Remove(t, score, id), lo, hi)
    decreases NodeCount(t)
  {
    if t.Node? {
      if score == t.score {
        JoinPreservesScoreOrder(t.left, t.right, lo, hi, t.score);
      } else if score < t.score {
        RemovePreservesScoreOrder(t.left, lo, SomeScore(t.score), score, id);
      } else {
        RemovePreservesScoreOrder(t.right, SomeScore(t.score), hi, score, id);
      }
    }
  }

  lemma AddPreservesValidTreap(t: Treap, score: Score, id: DocId, priority: Priority)
    requires ValidTreap(t)
    ensures ValidTreap(Add(t, score, id, priority))
  {
    AddPreservesBucketInvariants(t, score, id, priority);
    AddPreservesHeap(t, score, id, priority);
    AddPreservesScoreOrder(t, NoScore, NoScore, score, id, priority);
  }

  lemma RemovePreservesValidTreap(t: Treap, score: Score, id: DocId)
    requires ValidTreap(t)
    ensures ValidTreap(Remove(t, score, id))
  {
    RemovePreservesBucketInvariants(t, score, id);
    RemovePreservesHeap(t, score, id);
    RemovePreservesScoreOrder(t, NoScore, NoScore, score, id);
  }

  function TreapRank(t: Treap, score: Score, id: MaybeDocId): nat
    requires SumConsistent(t)
    decreases NodeCount(t)
  {
    if t.Empty? then 0
    else if score < t.score then TreapRank(t.left, score, id)
    else if score > t.score then Sum(t.left) + |t.ids| + TreapRank(t.right, score, id)
    else
      Sum(t.left) +
      (match id
       case NoDoc => 0
       case SomeDoc(doc) => InsertionIndex(t.ids, doc))
  }

  function TreapCountAtMost(t: Treap, score: Score): nat
    requires SumConsistent(t)
    decreases NodeCount(t)
  {
    if t.Empty? then 0
    else if score < t.score then TreapCountAtMost(t.left, score)
    else Sum(t.left) + |t.ids| + TreapCountAtMost(t.right, score)
  }

  function TreapGetAtRank(t: Treap, rank: nat): AtRank
    requires SumConsistent(t)
    decreases NodeCount(t), rank
  {
    if t.Empty? then Missing
    else if rank < Sum(t.left) then TreapGetAtRank(t.left, rank)
    else if rank < Sum(t.left) + |t.ids| then
      var pos := rank - Sum(t.left);
      Found(t.score, t.ids[pos], pos)
    else
      TreapGetAtRank(t.right, rank - (Sum(t.left) + |t.ids|))
  }

  function TakePrefix<T>(xs: seq<T>, limit: nat): seq<T> {
    if |xs| == 0 || limit == 0 then []
    else [xs[0]] + TakePrefix(xs[1..], limit - 1)
  }

  function SatSub(a: nat, b: nat): nat {
    if b <= a then a - b else 0
  }

  ghost function FilterRangeIds(es: seq<Entry>, minScore: Score, maxScore: Score): seq<DocId> {
    if |es| == 0 then []
    else ((if minScore <= es[0].score <= maxScore then [es[0].id] else []) +
      FilterRangeIds(es[1..], minScore, maxScore))
  }

  lemma FilterRangeConcat(left: seq<Entry>, right: seq<Entry>, minScore: Score, maxScore: Score)
    ensures FilterRangeIds(left + right, minScore, maxScore) ==
      FilterRangeIds(left, minScore, maxScore) + FilterRangeIds(right, minScore, maxScore)
    decreases |left|
  {
    if |left| == 0 {
      assert left == [];
      assert left + right == right;
      assert FilterRangeIds(left, minScore, maxScore) == [];
    } else {
      assert left + right == [left[0]] + (left[1..] + right);
      assert (left + right)[1..] == left[1..] + right;
      FilterRangeConcat(left[1..], right, minScore, maxScore);
    }
  }

  lemma FilterRangeBucket(score: Score, ids: seq<DocId>, minScore: Score, maxScore: Score)
    ensures FilterRangeIds(EntriesFromIds(score, ids), minScore, maxScore) ==
      (if minScore <= score <= maxScore then ids else [])
    decreases |ids|
  {
    if |ids| > 0 {
      FilterRangeBucket(score, ids[1..], minScore, maxScore);
    }
  }

  lemma TakePrefixWithinLimit<T>(items: seq<T>, limit: nat)
    ensures |TakePrefix(items, limit)| <= limit
    decreases |items|, limit
  {
    if |items| > 0 && limit > 0 {
      TakePrefixWithinLimit(items[1..], limit - 1);
    }
  }

  lemma TakePrefixConcat<T>(left: seq<T>, right: seq<T>, limit: nat)
    ensures TakePrefix(left + right, limit) ==
      TakePrefix(left, limit) + TakePrefix(right, SatSub(limit, |TakePrefix(left, limit)|))
    decreases |left|, limit
  {
    if |left| == 0 {
      assert left == [];
      assert left + right == right;
      assert TakePrefix(left, limit) == [];
    } else if limit > 0 {
      assert left + right == [left[0]] + (left[1..] + right);
      assert (left + right)[1..] == left[1..] + right;
      TakePrefixWithinLimit(left[1..], limit - 1);
      TakePrefixConcat(left[1..], right, limit - 1);
      assert SatSub(limit, 1 + |TakePrefix(left[1..], limit - 1)|) ==
        SatSub(limit - 1, |TakePrefix(left[1..], limit - 1)|);
    }
  }

  lemma FilterRangeAboveMax(es: seq<Entry>, minScore: Score, maxScore: Score)
    requires forall index :: 0 <= index < |es| ==> es[index].score > maxScore
    ensures FilterRangeIds(es, minScore, maxScore) == []
    decreases |es|
  {
    if |es| > 0 {
      FilterRangeAboveMax(es[1..], minScore, maxScore);
    }
  }

  lemma CollectRangeMatchesFilter(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat)
    requires SortedEntries(es)
    ensures CollectRange(es, minScore, maxScore, limit) == TakePrefix(FilterRangeIds(es, minScore, maxScore), limit)
    decreases |es|, limit
  {
    if |es| > 0 && limit > 0 {
      if es[0].score < minScore {
        CollectRangeMatchesFilter(es[1..], minScore, maxScore, limit);
        assert FilterRangeIds(es, minScore, maxScore) == FilterRangeIds(es[1..], minScore, maxScore);
      } else if es[0].score > maxScore {
        FilterRangeAboveMax(es, minScore, maxScore);
      } else {
        CollectRangeMatchesFilter(es[1..], minScore, maxScore, limit - 1);
      }
    }
  }

  function TreapCollectRange(t: Treap, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SumConsistent(t)
    decreases NodeCount(t)
  {
    if t.Empty? || limit == 0 then []
    else
      var leftOut := if minScore < t.score then TreapCollectRange(t.left, minScore, maxScore, limit) else [];
      var rem1 := SatSub(limit, |leftOut|);
      if rem1 == 0 then
        leftOut
      else
        var selfOut := if t.score >= minScore && t.score <= maxScore then TakePrefix(t.ids, rem1) else [];
        var rem2 := SatSub(rem1, |selfOut|);
        if rem2 == 0 then
          leftOut + selfOut
        else
          var rightOut := if t.score < maxScore then TreapCollectRange(t.right, minScore, maxScore, rem2) else [];
          leftOut + selfOut + rightOut
  }

  function ModelRankOnEntries(t: Treap, score: Score, id: MaybeDocId): nat {
    Rank(Entries(t), score, id)
  }

  function ModelCountAtMostOnEntries(t: Treap, score: Score): nat {
    CountAtMost(Entries(t), score)
  }

  function ModelGetAtRankOnEntries(t: Treap, rank: nat): AtRank
    requires SortedEntries(Entries(t))
  {
    GetAtRank(Entries(t), rank)
  }

  function ModelCollectRangeOnEntries(t: Treap, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SortedEntries(Entries(t))
  {
    CollectRange(Entries(t), minScore, maxScore, limit)
  }

  predicate AllScoresLt(es: seq<Entry>, score: Score) {
    if |es| == 0 then true
    else es[0].score < score && AllScoresLt(es[1..], score)
  }

  predicate AllScoresLe(es: seq<Entry>, score: Score) {
    if |es| == 0 then true
    else es[0].score <= score && AllScoresLe(es[1..], score)
  }

  predicate AllScoresGt(es: seq<Entry>, score: Score) {
    if |es| == 0 then true
    else es[0].score > score && AllScoresGt(es[1..], score)
  }

  lemma FilterRangeBelowMin(es: seq<Entry>, minScore: Score, maxScore: Score)
    requires AllScoresLt(es, minScore)
    ensures FilterRangeIds(es, minScore, maxScore) == []
    decreases |es|
  {
    if |es| > 0 {
      FilterRangeBelowMin(es[1..], minScore, maxScore);
    }
  }

  lemma FilterRangeAboveBound(es: seq<Entry>, minScore: Score, maxScore: Score)
    requires AllScoresGt(es, maxScore)
    ensures FilterRangeIds(es, minScore, maxScore) == []
    decreases |es|
  {
    if |es| > 0 {
      FilterRangeAboveBound(es[1..], minScore, maxScore);
    }
  }

  lemma AllScoresLtAt(es: seq<Entry>, score: Score, index: nat)
    requires AllScoresLt(es, score)
    requires index < |es|
    ensures es[index].score < score
    decreases index
  {
    if index > 0 {
      AllScoresLtAt(es[1..], score, index - 1);
    }
  }

  lemma AllScoresGtAt(es: seq<Entry>, score: Score, index: nat)
    requires AllScoresGt(es, score)
    requires index < |es|
    ensures es[index].score > score
    decreases index
  {
    if index > 0 {
      AllScoresGtAt(es[1..], score, index - 1);
    }
  }

  lemma AllScoresLtMember(es: seq<Entry>, score: Score, entry: Entry)
    requires AllScoresLt(es, score)
    requires entry in es
    ensures entry.score < score
  {
    var index :| 0 <= index < |es| && es[index] == entry;
    AllScoresLtAt(es, score, index);
  }

  lemma AllScoresGtMember(es: seq<Entry>, score: Score, entry: Entry)
    requires AllScoresGt(es, score)
    requires entry in es
    ensures entry.score > score
  {
    var index :| 0 <= index < |es| && es[index] == entry;
    AllScoresGtAt(es, score, index);
  }

  lemma EntriesFromIdsLength(score: Score, ids: seq<DocId>)
    ensures |EntriesFromIds(score, ids)| == |ids|
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsLength(score, ids[1..]);
    }
  }

  lemma EntriesFromIdsMembership(score: Score, ids: seq<DocId>, entry: Entry)
    ensures entry in EntriesFromIds(score, ids) <==> entry.score == score && entry.id in ids
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsMembership(score, ids[1..], entry);
    }
  }

  lemma SumEqualsEntriesLength(t: Treap)
    requires SumConsistent(t)
    ensures Sum(t) == |Entries(t)|
    decreases NodeCount(t)
  {
    if t.Empty? {
    } else {
      SumEqualsEntriesLength(t.left);
      SumEqualsEntriesLength(t.right);
      EntriesFromIdsLength(t.score, t.ids);
      assert |Entries(t)| == |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)| + |Entries(t.right)|;
      assert Sum(t) == |t.ids| + Sum(t.left) + Sum(t.right);
    }
  }

  lemma EntriesFromIdsAt(score: Score, ids: seq<DocId>, index: nat)
    requires index < |ids|
    ensures index < |EntriesFromIds(score, ids)| && EntriesFromIds(score, ids)[index] == Entry(score, ids[index])
    decreases index
  {
    EntriesFromIdsLength(score, ids);
    if index > 0 {
      EntriesFromIdsAt(score, ids[1..], index - 1);
    }
  }

  lemma EntriesFromIdsAreSorted(score: Score, ids: seq<DocId>)
    requires SortedStrictIds(ids)
    ensures SortedEntries(EntriesFromIds(score, ids))
  {
    EntriesFromIdsLength(score, ids);
    forall left, right | 0 <= left < right < |EntriesFromIds(score, ids)|
      ensures LexLt(EntriesFromIds(score, ids)[left], EntriesFromIds(score, ids)[right])
    {
      EntriesFromIdsAt(score, ids, left);
      EntriesFromIdsAt(score, ids, right);
    }
  }

  lemma SortedEntriesConcat(left: seq<Entry>, right: seq<Entry>)
    requires SortedEntries(left) && SortedEntries(right)
    requires forall leftIndex, rightIndex :: 0 <= leftIndex < |left| && 0 <= rightIndex < |right| ==>
      LexLt(left[leftIndex], right[rightIndex])
    ensures SortedEntries(left + right)
  {
  }

  lemma TreapGetAtRankReturnsEntry(t: Treap, rank: nat)
    requires SumConsistent(t)
    ensures rank >= |Entries(t)| ==> TreapGetAtRank(t, rank).Missing?
    ensures rank < |Entries(t)| ==> (TreapGetAtRank(t, rank).Found? &&
      Entry(TreapGetAtRank(t, rank).score, TreapGetAtRank(t, rank).id) == Entries(t)[rank])
    ensures rank < |Entries(t)| ==> TreapGetAtRank(t, rank).position <= rank
    decreases NodeCount(t)
  {
    if t.Node? {
      SumEqualsEntriesLength(t.left);
      EntriesFromIdsLength(t.score, t.ids);
      if rank < Sum(t.left) {
        TreapGetAtRankReturnsEntry(t.left, rank);
      } else if rank < Sum(t.left) + |t.ids| {
        EntriesFromIdsAt(t.score, t.ids, rank - Sum(t.left));
      } else {
        TreapGetAtRankReturnsEntry(t.right, rank - (Sum(t.left) + |t.ids|));
      }
    }
  }

  lemma EntriesFromIdsAllLt(score: Score, ids: seq<DocId>, bound: Score)
    requires score < bound
    ensures AllScoresLt(EntriesFromIds(score, ids), bound)
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsAllLt(score, ids[1..], bound);
    }
  }

  lemma EntriesFromIdsAllLe(score: Score, ids: seq<DocId>, bound: Score)
    requires score <= bound
    ensures AllScoresLe(EntriesFromIds(score, ids), bound)
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsAllLe(score, ids[1..], bound);
    }
  }

  lemma EntriesFromIdsAllGt(score: Score, ids: seq<DocId>, bound: Score)
    requires score > bound
    ensures AllScoresGt(EntriesFromIds(score, ids), bound)
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsAllGt(score, ids[1..], bound);
    }
  }

  lemma AllScoresLtConcat(xs: seq<Entry>, ys: seq<Entry>, score: Score)
    requires AllScoresLt(xs, score)
    requires AllScoresLt(ys, score)
    ensures AllScoresLt(xs + ys, score)
    decreases |xs|
  {
    if |xs| == 0 {
      assert xs == [];
      assert xs + ys == ys;
    } else {
      assert xs + ys == [xs[0]] + (xs[1..] + ys);
      assert (xs + ys)[0] == xs[0];
      assert (xs + ys)[1..] == xs[1..] + ys;
      assert xs[0].score < score;
      AllScoresLtConcat(xs[1..], ys, score);
    }
  }

  lemma AllScoresLeConcat(xs: seq<Entry>, ys: seq<Entry>, score: Score)
    requires AllScoresLe(xs, score)
    requires AllScoresLe(ys, score)
    ensures AllScoresLe(xs + ys, score)
    decreases |xs|
  {
    if |xs| == 0 {
      assert xs == [];
      assert xs + ys == ys;
    } else {
      assert xs + ys == [xs[0]] + (xs[1..] + ys);
      assert (xs + ys)[0] == xs[0];
      assert (xs + ys)[1..] == xs[1..] + ys;
      assert xs[0].score <= score;
      AllScoresLeConcat(xs[1..], ys, score);
    }
  }

  lemma AllScoresGtConcat(xs: seq<Entry>, ys: seq<Entry>, score: Score)
    requires AllScoresGt(xs, score)
    requires AllScoresGt(ys, score)
    ensures AllScoresGt(xs + ys, score)
    decreases |xs|
  {
    if |xs| == 0 {
      assert xs == [];
      assert xs + ys == ys;
    } else {
      assert xs + ys == [xs[0]] + (xs[1..] + ys);
      assert (xs + ys)[0] == xs[0];
      assert (xs + ys)[1..] == xs[1..] + ys;
      assert xs[0].score > score;
      AllScoresGtConcat(xs[1..], ys, score);
    }
  }

  lemma AllScoresLtImpliesLe(xs: seq<Entry>, score: Score)
    requires AllScoresLt(xs, score)
    ensures AllScoresLe(xs, score)
    decreases |xs|
  {
    if |xs| > 0 {
      AllScoresLtImpliesLe(xs[1..], score);
    }
  }

  lemma AllScoresLtWeaken(xs: seq<Entry>, tight: Score, wide: Score)
    requires tight < wide
    requires AllScoresLt(xs, tight)
    ensures AllScoresLt(xs, wide)
    decreases |xs|
  {
    if |xs| > 0 {
      AllScoresLtWeaken(xs[1..], tight, wide);
    }
  }

  lemma AllScoresGtWeaken(xs: seq<Entry>, tight: Score, wide: Score)
    requires wide < tight
    requires AllScoresGt(xs, tight)
    ensures AllScoresGt(xs, wide)
    decreases |xs|
  {
    if |xs| > 0 {
      AllScoresGtWeaken(xs[1..], tight, wide);
    }
  }

  lemma EntriesLtFromOrdered(t: Treap, lo: MaybeScore, bound: Score)
    requires OrderedByScore(t, lo, SomeScore(bound))
    ensures AllScoresLt(Entries(t), bound)
    decreases NodeCount(t)
  {
    if t.Empty? {
    } else {
      assert t.score < bound;

      EntriesLtFromOrdered(t.left, lo, t.score);
      AllScoresLtWeaken(Entries(t.left), t.score, bound);

      EntriesFromIdsAllLt(t.score, t.ids, bound);

      EntriesLtFromOrdered(t.right, SomeScore(t.score), bound);

      AllScoresLtConcat(Entries(t.left), EntriesFromIds(t.score, t.ids), bound);
      AllScoresLtConcat(Entries(t.left) + EntriesFromIds(t.score, t.ids), Entries(t.right), bound);
    }
  }

  lemma EntriesGtFromOrdered(t: Treap, bound: Score, hi: MaybeScore)
    requires OrderedByScore(t, SomeScore(bound), hi)
    ensures AllScoresGt(Entries(t), bound)
    decreases NodeCount(t)
  {
    if t.Empty? {
    } else {
      assert bound < t.score;

      EntriesGtFromOrdered(t.left, bound, SomeScore(t.score));

      EntriesFromIdsAllGt(t.score, t.ids, bound);

      EntriesGtFromOrdered(t.right, t.score, hi);
      AllScoresGtWeaken(Entries(t.right), t.score, bound);

      AllScoresGtConcat(Entries(t.left), EntriesFromIds(t.score, t.ids), bound);
      AllScoresGtConcat(Entries(t.left) + EntriesFromIds(t.score, t.ids), Entries(t.right), bound);
    }
  }

  lemma CountStrictLessAllGtZero(es: seq<Entry>, score: Score)
    requires AllScoresGt(es, score)
    ensures CountStrictLessScore(es, score) == 0
    decreases |es|
  {
    if |es| > 0 {
      CountStrictLessAllGtZero(es[1..], score);
    }
  }

  lemma CountStrictLessPrefixLt(prefix: seq<Entry>, rest: seq<Entry>, score: Score)
    requires AllScoresLt(prefix, score)
    ensures CountStrictLessScore(prefix + rest, score) == |prefix| + CountStrictLessScore(rest, score)
    decreases |prefix|
  {
    if |prefix| == 0 {
      assert prefix == [];
      assert prefix + rest == rest;
    } else {
      assert prefix + rest == [prefix[0]] + (prefix[1..] + rest);
      assert prefix[0].score < score;
      CountStrictLessPrefixLt(prefix[1..], rest, score);
      assert CountStrictLessScore(prefix + rest, score) == 1 + CountStrictLessScore(prefix[1..] + rest, score);
      assert CountStrictLessScore(prefix[1..] + rest, score) == |prefix[1..]| + CountStrictLessScore(rest, score);
      assert |prefix| == 1 + |prefix[1..]|;
    }
  }

  lemma CountStrictLessSuffixGt(prefix: seq<Entry>, suffix: seq<Entry>, score: Score)
    requires AllScoresGt(suffix, score)
    ensures CountStrictLessScore(prefix + suffix, score) == CountStrictLessScore(prefix, score)
    decreases |prefix|
  {
    if |prefix| == 0 {
      assert prefix == [];
      assert prefix + suffix == suffix;
      CountStrictLessAllGtZero(suffix, score);
    } else {
      assert prefix + suffix == [prefix[0]] + (prefix[1..] + suffix);
      CountStrictLessSuffixGt(prefix[1..], suffix, score);
      if prefix[0].score < score {
        assert CountStrictLessScore(prefix + suffix, score) == 1 + CountStrictLessScore(prefix[1..] + suffix, score);
        assert CountStrictLessScore(prefix, score) == 1 + CountStrictLessScore(prefix[1..], score);
      } else {
        assert CountStrictLessScore(prefix + suffix, score) == CountStrictLessScore(prefix[1..] + suffix, score);
        assert CountStrictLessScore(prefix, score) == CountStrictLessScore(prefix[1..], score);
      }
    }
  }

  lemma CountStrictLessEntriesFromIdsEq(score: Score, ids: seq<DocId>)
    ensures CountStrictLessScore(EntriesFromIds(score, ids), score) == 0
    decreases |ids|
  {
    if |ids| > 0 {
      CountStrictLessEntriesFromIdsEq(score, ids[1..]);
    }
  }

  lemma RankWithIdAllGtZero(es: seq<Entry>, score: Score, id: DocId)
    requires AllScoresGt(es, score)
    ensures RankWithId(es, score, id) == 0
  {
    if |es| > 0 {
      assert es[0].score > score;
    }
  }

  lemma RankWithIdPrefixLt(prefix: seq<Entry>, rest: seq<Entry>, score: Score, id: DocId)
    requires AllScoresLt(prefix, score)
    ensures RankWithId(prefix + rest, score, id) == |prefix| + RankWithId(rest, score, id)
    decreases |prefix|
  {
    if |prefix| == 0 {
      assert prefix == [];
      assert prefix + rest == rest;
    } else {
      assert prefix + rest == [prefix[0]] + (prefix[1..] + rest);
      assert prefix[0].score < score;
      RankWithIdPrefixLt(prefix[1..], rest, score, id);
      assert RankWithId(prefix + rest, score, id) == 1 + RankWithId(prefix[1..] + rest, score, id);
      assert RankWithId(prefix[1..] + rest, score, id) == |prefix[1..]| + RankWithId(rest, score, id);
      assert |prefix| == 1 + |prefix[1..]|;
    }
  }

  lemma RankWithIdSuffixGt(prefix: seq<Entry>, suffix: seq<Entry>, score: Score, id: DocId)
    requires AllScoresGt(suffix, score)
    ensures RankWithId(prefix + suffix, score, id) == RankWithId(prefix, score, id)
    decreases |prefix|
  {
    if |prefix| == 0 {
      RankWithIdAllGtZero(suffix, score, id);
    } else {
      assert prefix + suffix == [prefix[0]] + (prefix[1..] + suffix);
      if prefix[0].score < score || (prefix[0].score == score && prefix[0].id < id) {
        RankWithIdSuffixGt(prefix[1..], suffix, score, id);
        assert RankWithId(prefix + suffix, score, id) == 1 + RankWithId(prefix[1..] + suffix, score, id);
        assert RankWithId(prefix, score, id) == 1 + RankWithId(prefix[1..], score, id);
      } else {
        assert RankWithId(prefix + suffix, score, id) == 0;
        assert RankWithId(prefix, score, id) == 0;
      }
    }
  }

  lemma RankWithIdEntriesFromIds(score: Score, ids: seq<DocId>, doc: DocId)
    requires SortedStrictIds(ids)
    ensures RankWithId(EntriesFromIds(score, ids), score, doc) == InsertionIndex(ids, doc)
    decreases |ids|
  {
    InsertionIndexFromMatchesReference(ids, doc, 0);
    assert InsertionIndex(ids, doc) == InsertionIndexReference(ids, doc);
    if |ids| == 0 {
    } else if ids[0] < doc {
      RankWithIdEntriesFromIds(score, ids[1..], doc);
      InsertionIndexFromMatchesReference(ids[1..], doc, 0);
      assert InsertionIndex(ids[1..], doc) == InsertionIndexReference(ids[1..], doc);
      assert InsertionIndex(ids, doc) == 1 + InsertionIndex(ids[1..], doc);
    }
  }

  lemma CountAtMostAllGtZero(es: seq<Entry>, score: Score)
    requires AllScoresGt(es, score)
    ensures CountAtMost(es, score) == 0
    decreases |es|
  {
    if |es| > 0 {
      CountAtMostAllGtZero(es[1..], score);
    }
  }

  lemma CountAtMostPrefixLe(prefix: seq<Entry>, rest: seq<Entry>, score: Score)
    requires AllScoresLe(prefix, score)
    ensures CountAtMost(prefix + rest, score) == |prefix| + CountAtMost(rest, score)
    decreases |prefix|
  {
    if |prefix| == 0 {
      assert prefix == [];
      assert prefix + rest == rest;
    } else {
      assert prefix + rest == [prefix[0]] + (prefix[1..] + rest);
      assert prefix[0].score <= score;
      CountAtMostPrefixLe(prefix[1..], rest, score);
      assert CountAtMost(prefix + rest, score) == 1 + CountAtMost(prefix[1..] + rest, score);
      assert CountAtMost(prefix[1..] + rest, score) == |prefix[1..]| + CountAtMost(rest, score);
      assert |prefix| == 1 + |prefix[1..]|;
    }
  }

  lemma CountAtMostSuffixGt(prefix: seq<Entry>, suffix: seq<Entry>, score: Score)
    requires AllScoresGt(suffix, score)
    ensures CountAtMost(prefix + suffix, score) == CountAtMost(prefix, score)
    decreases |prefix|
  {
    if |prefix| == 0 {
      assert prefix == [];
      assert prefix + suffix == suffix;
      CountAtMostAllGtZero(suffix, score);
    } else {
      assert prefix + suffix == [prefix[0]] + (prefix[1..] + suffix);
      CountAtMostSuffixGt(prefix[1..], suffix, score);
      if prefix[0].score <= score {
        assert CountAtMost(prefix + suffix, score) == 1 + CountAtMost(prefix[1..] + suffix, score);
        assert CountAtMost(prefix, score) == 1 + CountAtMost(prefix[1..], score);
      } else {
        assert CountAtMost(prefix + suffix, score) == CountAtMost(prefix[1..] + suffix, score);
        assert CountAtMost(prefix, score) == CountAtMost(prefix[1..], score);
      }
    }
  }

  lemma TreapRankNoDocRefinesBounded(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    ensures TreapRank(t, score, NoDoc) == CountStrictLessScore(Entries(t), score)
    decreases NodeCount(t)
  {
    if t.Empty? {
    } else if score < t.score {
      TreapRankNoDocRefinesBounded(t.left, lo, SomeScore(t.score), score);
      EntriesFromIdsAllGt(t.score, t.ids, score);
      EntriesGtFromOrdered(t.right, t.score, hi);
      AllScoresGtWeaken(Entries(t.right), t.score, score);
      AllScoresGtConcat(EntriesFromIds(t.score, t.ids), Entries(t.right), score);
      CountStrictLessSuffixGt(Entries(t.left), EntriesFromIds(t.score, t.ids) + Entries(t.right), score);
      assert Entries(t) == Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right));
      assert CountStrictLessScore(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score) == CountStrictLessScore(Entries(t.left), score);
      calc {
        TreapRank(t, score, NoDoc);
        == { }
        TreapRank(t.left, score, NoDoc);
        == { }
        CountStrictLessScore(Entries(t.left), score);
        == { }
        CountStrictLessScore(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score);
        == { }
        CountStrictLessScore(Entries(t), score);
      }
    } else if score > t.score {
      TreapRankNoDocRefinesBounded(t.right, SomeScore(t.score), hi, score);
      EntriesLtFromOrdered(t.left, lo, t.score);
      AllScoresLtWeaken(Entries(t.left), t.score, score);
      EntriesFromIdsAllLt(t.score, t.ids, score);
      AllScoresLtConcat(Entries(t.left), EntriesFromIds(t.score, t.ids), score);
      CountStrictLessPrefixLt(Entries(t.left) + EntriesFromIds(t.score, t.ids), Entries(t.right), score);
      SumEqualsEntriesLength(t.left);
      EntriesFromIdsLength(t.score, t.ids);
      assert |Entries(t.left) + EntriesFromIds(t.score, t.ids)| == |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)|;
      assert Entries(t) == (Entries(t.left) + EntriesFromIds(t.score, t.ids)) + Entries(t.right);
      calc {
        TreapRank(t, score, NoDoc);
        == { }
        Sum(t.left) + |t.ids| + TreapRank(t.right, score, NoDoc);
        == { }
        |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)| + CountStrictLessScore(Entries(t.right), score);
        == { }
        |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + CountStrictLessScore(Entries(t.right), score);
        == { }
        CountStrictLessScore((Entries(t.left) + EntriesFromIds(t.score, t.ids)) + Entries(t.right), score);
        == { }
        CountStrictLessScore(Entries(t), score);
      }
    } else {
      EntriesLtFromOrdered(t.left, lo, t.score);
      CountStrictLessPrefixLt(Entries(t.left), EntriesFromIds(t.score, t.ids) + Entries(t.right), score);
      EntriesGtFromOrdered(t.right, t.score, hi);
      CountStrictLessSuffixGt(EntriesFromIds(t.score, t.ids), Entries(t.right), score);
      CountStrictLessEntriesFromIdsEq(t.score, t.ids);
      SumEqualsEntriesLength(t.left);
      assert CountStrictLessScore(EntriesFromIds(t.score, t.ids) + Entries(t.right), score) == 0;
      assert Entries(t) == Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right));
      calc {
        TreapRank(t, score, NoDoc);
        == { }
        Sum(t.left);
        == { }
        |Entries(t.left)|;
        == { }
        CountStrictLessScore(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score);
        == { }
        CountStrictLessScore(Entries(t), score);
      }
    }
  }

  lemma TreapRankSomeDocRefinesBounded(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score, doc: DocId)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    requires IdsSortedInTree(t)
    ensures TreapRank(t, score, SomeDoc(doc)) == RankWithId(Entries(t), score, doc)
    decreases NodeCount(t)
  {
    if t.Empty? {
    } else if score < t.score {
      TreapRankSomeDocRefinesBounded(t.left, lo, SomeScore(t.score), score, doc);
      EntriesFromIdsAllGt(t.score, t.ids, score);
      EntriesGtFromOrdered(t.right, t.score, hi);
      AllScoresGtWeaken(Entries(t.right), t.score, score);
      AllScoresGtConcat(EntriesFromIds(t.score, t.ids), Entries(t.right), score);
      RankWithIdSuffixGt(Entries(t.left), EntriesFromIds(t.score, t.ids) + Entries(t.right), score, doc);
      assert Entries(t) == Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right));
      assert RankWithId(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score, doc) == RankWithId(Entries(t.left), score, doc);
      calc {
        TreapRank(t, score, SomeDoc(doc));
        == { }
        TreapRank(t.left, score, SomeDoc(doc));
        == { }
        RankWithId(Entries(t.left), score, doc);
        == { }
        RankWithId(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score, doc);
        == { }
        RankWithId(Entries(t), score, doc);
      }
    } else if score > t.score {
      TreapRankSomeDocRefinesBounded(t.right, SomeScore(t.score), hi, score, doc);
      EntriesLtFromOrdered(t.left, lo, t.score);
      AllScoresLtWeaken(Entries(t.left), t.score, score);
      EntriesFromIdsAllLt(t.score, t.ids, score);
      AllScoresLtConcat(Entries(t.left), EntriesFromIds(t.score, t.ids), score);
      RankWithIdPrefixLt(Entries(t.left) + EntriesFromIds(t.score, t.ids), Entries(t.right), score, doc);
      SumEqualsEntriesLength(t.left);
      EntriesFromIdsLength(t.score, t.ids);
      assert |Entries(t.left) + EntriesFromIds(t.score, t.ids)| == |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)|;
      assert Entries(t) == (Entries(t.left) + EntriesFromIds(t.score, t.ids)) + Entries(t.right);
      calc {
        TreapRank(t, score, SomeDoc(doc));
        == { }
        Sum(t.left) + |t.ids| + TreapRank(t.right, score, SomeDoc(doc));
        == { }
        |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)| + RankWithId(Entries(t.right), score, doc);
        == { }
        |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + RankWithId(Entries(t.right), score, doc);
        == { }
        RankWithId((Entries(t.left) + EntriesFromIds(t.score, t.ids)) + Entries(t.right), score, doc);
        == { }
        RankWithId(Entries(t), score, doc);
      }
    } else {
      EntriesLtFromOrdered(t.left, lo, t.score);
      RankWithIdPrefixLt(Entries(t.left), [], score, doc);
      RankWithIdPrefixLt(Entries(t.left), EntriesFromIds(t.score, t.ids) + Entries(t.right), score, doc);
      EntriesGtFromOrdered(t.right, t.score, hi);
      RankWithIdSuffixGt(EntriesFromIds(t.score, t.ids), Entries(t.right), score, doc);
      RankWithIdEntriesFromIds(t.score, t.ids, doc);
      SumEqualsEntriesLength(t.left);
      assert Entries(t.left) + [] == Entries(t.left);
      assert RankWithId(Entries(t.left), score, doc) == |Entries(t.left)|;
      assert RankWithId(EntriesFromIds(t.score, t.ids) + Entries(t.right), score, doc) == RankWithId(EntriesFromIds(t.score, t.ids), score, doc);
      assert RankWithId(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score, doc)
        == |Entries(t.left)| + RankWithId(EntriesFromIds(t.score, t.ids), score, doc);
      assert Entries(t) == Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right));
      calc {
        TreapRank(t, score, SomeDoc(doc));
        == { }
        Sum(t.left) + InsertionIndex(t.ids, doc);
        == { }
        |Entries(t.left)| + RankWithId(EntriesFromIds(t.score, t.ids), score, doc);
        == { }
        RankWithId(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score, doc);
        == { }
        RankWithId(Entries(t), score, doc);
      }
    }
  }

  lemma TreapRankRefinesModel(t: Treap, score: Score, id: MaybeDocId)
    requires ValidTreap(t)
    ensures TreapRank(t, score, id) == Rank(Entries(t), score, id)
  {
    match id
    case NoDoc =>
      TreapRankNoDocRefinesBounded(t, NoScore, NoScore, score);
      assert Rank(Entries(t), score, NoDoc) == CountStrictLessScore(Entries(t), score);
    case SomeDoc(doc) =>
      TreapRankSomeDocRefinesBounded(t, NoScore, NoScore, score, doc);
      assert Rank(Entries(t), score, SomeDoc(doc)) == RankWithId(Entries(t), score, doc);
  }

  lemma TreapCountAtMostRefinesModelBounded(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    ensures TreapCountAtMost(t, score) == CountAtMost(Entries(t), score)
    decreases NodeCount(t)
  {
    if t.Empty? {
    } else if score < t.score {
      TreapCountAtMostRefinesModelBounded(t.left, lo, SomeScore(t.score), score);
      EntriesFromIdsAllGt(t.score, t.ids, score);
      EntriesGtFromOrdered(t.right, t.score, hi);
      AllScoresGtWeaken(Entries(t.right), t.score, score);
      AllScoresGtConcat(EntriesFromIds(t.score, t.ids), Entries(t.right), score);
      CountAtMostSuffixGt(Entries(t.left), EntriesFromIds(t.score, t.ids) + Entries(t.right), score);
      assert Entries(t) == Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right));
      assert CountAtMost(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score) == CountAtMost(Entries(t.left), score);
      calc {
        TreapCountAtMost(t, score);
        == { }
        TreapCountAtMost(t.left, score);
        == { }
        CountAtMost(Entries(t.left), score);
        == { }
        CountAtMost(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score);
        == { }
        CountAtMost(Entries(t), score);
      }
    } else {
      TreapCountAtMostRefinesModelBounded(t.right, SomeScore(t.score), hi, score);
      EntriesLtFromOrdered(t.left, lo, t.score);
      if score == t.score {
        AllScoresLtImpliesLe(Entries(t.left), t.score);
      } else {
        assert t.score < score;
        AllScoresLtWeaken(Entries(t.left), t.score, score);
        AllScoresLtImpliesLe(Entries(t.left), score);
      }
      EntriesFromIdsAllLe(t.score, t.ids, score);
      AllScoresLeConcat(Entries(t.left), EntriesFromIds(t.score, t.ids), score);
      CountAtMostPrefixLe(Entries(t.left) + EntriesFromIds(t.score, t.ids), Entries(t.right), score);
      SumEqualsEntriesLength(t.left);
      EntriesFromIdsLength(t.score, t.ids);
      assert |Entries(t.left) + EntriesFromIds(t.score, t.ids)| == |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)|;
      assert CountAtMost((Entries(t.left) + EntriesFromIds(t.score, t.ids)) + Entries(t.right), score) == |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + CountAtMost(Entries(t.right), score);
      assert Entries(t) == (Entries(t.left) + EntriesFromIds(t.score, t.ids)) + Entries(t.right);
      calc {
        TreapCountAtMost(t, score);
        == { }
        Sum(t.left) + |t.ids| + TreapCountAtMost(t.right, score);
        == { }
        |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)| + CountAtMost(Entries(t.right), score);
        == { }
        |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + CountAtMost(Entries(t.right), score);
        == { }
        CountAtMost((Entries(t.left) + EntriesFromIds(t.score, t.ids)) + Entries(t.right), score);
        == { }
        CountAtMost(Entries(t), score);
      }
    }
  }

  lemma TreapCountAtMostRefinesModel(t: Treap, score: Score)
    requires ValidTreap(t)
    ensures TreapCountAtMost(t, score) == CountAtMost(Entries(t), score)
  {
    TreapCountAtMostRefinesModelBounded(t, NoScore, NoScore, score);
  }

  lemma EntriesSortedFromTree(t: Treap, lo: MaybeScore, hi: MaybeScore)
    requires OrderedByScore(t, lo, hi)
    requires IdsSortedInTree(t)
    ensures SortedEntries(Entries(t))
    decreases NodeCount(t)
  {
    if t.Node? {
      var left := Entries(t.left);
      var bucket := EntriesFromIds(t.score, t.ids);
      var right := Entries(t.right);
      EntriesSortedFromTree(t.left, lo, SomeScore(t.score));
      EntriesSortedFromTree(t.right, SomeScore(t.score), hi);
      EntriesFromIdsAreSorted(t.score, t.ids);
      EntriesLtFromOrdered(t.left, lo, t.score);
      EntriesGtFromOrdered(t.right, t.score, hi);
      EntriesFromIdsLength(t.score, t.ids);
      forall leftIndex, bucketIndex | 0 <= leftIndex < |left| && 0 <= bucketIndex < |bucket|
        ensures LexLt(left[leftIndex], bucket[bucketIndex])
      {
        AllScoresLtAt(left, t.score, leftIndex);
        EntriesFromIdsAt(t.score, t.ids, bucketIndex);
      }
      SortedEntriesConcat(left, bucket);
      forall prefixIndex, rightIndex | 0 <= prefixIndex < |left + bucket| && 0 <= rightIndex < |right|
        ensures LexLt((left + bucket)[prefixIndex], right[rightIndex])
      {
        AllScoresGtAt(right, t.score, rightIndex);
        if prefixIndex < |left| {
          AllScoresLtAt(left, t.score, prefixIndex);
        } else {
          EntriesFromIdsAt(t.score, t.ids, prefixIndex - |left|);
        }
      }
      SortedEntriesConcat(left + bucket, right);
    }
  }

  lemma TreapGetAtRankPosition(t: Treap, lo: MaybeScore, hi: MaybeScore, rank: nat)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    requires rank < Sum(t)
    ensures TreapGetAtRank(t, rank).Found?
    ensures TreapRank(t, TreapGetAtRank(t, rank).score, NoDoc) <= rank
    ensures TreapGetAtRank(t, rank).position == rank - TreapRank(t, TreapGetAtRank(t, rank).score, NoDoc)
    decreases NodeCount(t)
  {
    if t.Node? {
      if rank < Sum(t.left) {
        TreapGetAtRankPosition(t.left, lo, SomeScore(t.score), rank);
        SumEqualsEntriesLength(t.left);
        TreapGetAtRankReturnsEntry(t.left, rank);
        EntriesLtFromOrdered(t.left, lo, t.score);
        AllScoresLtAt(Entries(t.left), t.score, rank);
      } else if rank < Sum(t.left) + |t.ids| {
      } else {
        var rightRank := rank - (Sum(t.left) + |t.ids|);
        TreapGetAtRankPosition(t.right, SomeScore(t.score), hi, rightRank);
        SumEqualsEntriesLength(t.right);
        TreapGetAtRankReturnsEntry(t.right, rightRank);
        EntriesGtFromOrdered(t.right, t.score, hi);
        AllScoresGtAt(Entries(t.right), t.score, rightRank);
      }
    }
  }

  lemma TreapGetAtRankRefinesModel(t: Treap, rank: nat)
    requires SumConsistent(t)
    requires OrderedByScore(t, NoScore, NoScore)
    requires SortedEntries(Entries(t))
    ensures TreapGetAtRank(t, rank) == GetAtRank(Entries(t), rank)
  {
    SumEqualsEntriesLength(t);
    TreapGetAtRankReturnsEntry(t, rank);
    if rank < Sum(t) {
      TreapGetAtRankPosition(t, NoScore, NoScore, rank);
      TreapRankNoDocRefinesBounded(t, NoScore, NoScore, TreapGetAtRank(t, rank).score);
      PositionAtMatchesScoreRank(Entries(t), rank);
    }
  }

  lemma ValidTreapGetAtRankRefinesModel(t: Treap, rank: nat)
    requires ValidTreap(t)
    ensures SortedEntries(Entries(t))
    ensures TreapGetAtRank(t, rank) == GetAtRank(Entries(t), rank)
  {
    EntriesSortedFromTree(t, NoScore, NoScore);
    TreapGetAtRankRefinesModel(t, rank);
  }

  lemma ValidTreapRankFindsEntry(t: Treap, index: nat)
    requires ValidTreap(t)
    requires index < |Entries(t)|
    ensures TreapRank(t, Entries(t)[index].score, SomeDoc(Entries(t)[index].id)) == index
  {
    EntriesSortedFromTree(t, NoScore, NoScore);
    RankWithIdFindsEntry(Entries(t), index);
    TreapRankRefinesModel(t, Entries(t)[index].score, SomeDoc(Entries(t)[index].id));
  }

  lemma TreapCollectRangeMatchesFilter(t: Treap, lo: MaybeScore, hi: MaybeScore, minScore: Score, maxScore: Score, limit: nat)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    ensures TreapCollectRange(t, minScore, maxScore, limit) ==
      TakePrefix(FilterRangeIds(Entries(t), minScore, maxScore), limit)
    decreases NodeCount(t)
  {
    if t.Node? && limit > 0 {
      var leftEntries := Entries(t.left);
      var bucketEntries := EntriesFromIds(t.score, t.ids);
      var rightEntries := Entries(t.right);
      var leftIds := FilterRangeIds(leftEntries, minScore, maxScore);
      var bucketIds := FilterRangeIds(bucketEntries, minScore, maxScore);
      var rightIds := FilterRangeIds(rightEntries, minScore, maxScore);

      if minScore < t.score {
        TreapCollectRangeMatchesFilter(t.left, lo, SomeScore(t.score), minScore, maxScore, limit);
      } else {
        EntriesLtFromOrdered(t.left, lo, t.score);
        if t.score < minScore {
          AllScoresLtWeaken(leftEntries, t.score, minScore);
        }
        FilterRangeBelowMin(leftEntries, minScore, maxScore);
      }
      var leftOut := if minScore < t.score then TreapCollectRange(t.left, minScore, maxScore, limit) else [];
      assert leftOut == TakePrefix(leftIds, limit);
      var remaining := SatSub(limit, |leftOut|);
      FilterRangeBucket(t.score, t.ids, minScore, maxScore);
      var selfOut := if t.score >= minScore && t.score <= maxScore then TakePrefix(t.ids, remaining) else [];
      assert selfOut == TakePrefix(bucketIds, remaining);
      var rightLimit := SatSub(remaining, |selfOut|);
      if t.score < maxScore {
        TreapCollectRangeMatchesFilter(t.right, SomeScore(t.score), hi, minScore, maxScore, rightLimit);
      } else {
        EntriesGtFromOrdered(t.right, t.score, hi);
        if maxScore < t.score {
          AllScoresGtWeaken(rightEntries, t.score, maxScore);
        }
        FilterRangeAboveBound(rightEntries, minScore, maxScore);
      }
      FilterRangeConcat(bucketEntries, rightEntries, minScore, maxScore);
      FilterRangeConcat(leftEntries, bucketEntries + rightEntries, minScore, maxScore);
      TakePrefixConcat(leftIds, bucketIds + rightIds, limit);
      TakePrefixConcat(bucketIds, rightIds, remaining);
      assert Entries(t) == leftEntries + (bucketEntries + rightEntries);
    }
  }

  lemma ValidTreapCollectRangeRefinesModel(t: Treap, minScore: Score, maxScore: Score, limit: nat)
    requires ValidTreap(t)
    ensures SortedEntries(Entries(t))
    ensures TreapCollectRange(t, minScore, maxScore, limit) == CollectRange(Entries(t), minScore, maxScore, limit)
  {
    EntriesSortedFromTree(t, NoScore, NoScore);
    TreapCollectRangeMatchesFilter(t, NoScore, NoScore, minScore, maxScore, limit);
    CollectRangeMatchesFilter(Entries(t), minScore, maxScore, limit);
  }

  lemma AddPreservesEntryMembership(t: Treap, score: Score, id: DocId, priority: Priority, entry: Entry)
    requires SumConsistent(t)
    requires IdsSortedInTree(t)
    ensures entry in Entries(Add(t, score, id, priority)) <==> entry in Entries(t) || entry == Entry(score, id)
    decreases NodeCount(t)
  {
    if t.Empty? {
      EntriesFromIdsMembership(score, [id], entry);
    } else if score == t.score {
      InsertIdProperties(t.ids, id);
      EntriesFromIdsMembership(t.score, t.ids, entry);
      EntriesFromIdsMembership(t.score, InsertId(t.ids, id), entry);
    } else if score < t.score {
      AddPreservesEntryMembership(t.left, score, id, priority, entry);
      var left := Add(t.left, score, id, priority);
      if left.Node? && left.prio > t.prio {
        var node := Pull(Node(t.score, t.ids, t.prio, 0, left, t.right));
        RotateRightPreservesEntries(node);
      }
    } else {
      AddPreservesEntryMembership(t.right, score, id, priority, entry);
      var right := Add(t.right, score, id, priority);
      if right.Node? && right.prio > t.prio {
        var node := Pull(Node(t.score, t.ids, t.prio, 0, t.left, right));
        RotateLeftPreservesEntries(node);
      }
    }
  }

  lemma JoinPreservesEntryMembership(left: Treap, right: Treap, entry: Entry)
    requires SumConsistent(left) && SumConsistent(right)
    ensures entry in Entries(Join(left, right)) <==> entry in Entries(left) || entry in Entries(right)
    decreases NodeCount(left) + NodeCount(right)
  {
    if left.Node? && right.Node? {
      if left.prio > right.prio {
        JoinPreservesEntryMembership(left.right, right, entry);
      } else {
        JoinPreservesEntryMembership(left, right.left, entry);
      }
    }
  }

  lemma RemovePreservesEntryMembership(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score, id: DocId, entry: Entry)
    requires SumConsistent(t)
    requires OrderedByScore(t, lo, hi)
    requires IdsSortedInTree(t)
    ensures entry in Entries(Remove(t, score, id)) <==> entry in Entries(t) && entry != Entry(score, id)
    decreases NodeCount(t)
  {
    if t.Node? {
      EntriesLtFromOrdered(t.left, lo, t.score);
      EntriesGtFromOrdered(t.right, t.score, hi);
      if entry in Entries(t.left) {
        AllScoresLtMember(Entries(t.left), t.score, entry);
      }
      if entry in Entries(t.right) {
        AllScoresGtMember(Entries(t.right), t.score, entry);
      }
      EntriesFromIdsMembership(t.score, t.ids, entry);
      if score == t.score {
        RemoveIdProperties(t.ids, id);
        RemoveIdLength(t.ids, id);
        EntriesFromIdsMembership(t.score, RemoveId(t.ids, id), entry);
        JoinPreservesEntryMembership(t.left, t.right, entry);
      } else if score < t.score {
        RemovePreservesEntryMembership(t.left, lo, SomeScore(t.score), score, id, entry);
      } else {
        RemovePreservesEntryMembership(t.right, SomeScore(t.score), hi, score, id, entry);
      }
    }
  }

  lemma ValidTreapAddRefinesModel(t: Treap, score: Score, id: DocId, priority: Priority)
    requires ValidTreap(t)
    ensures SortedEntries(Entries(t))
    ensures Entries(Add(t, score, id, priority)) == InsertUnique(Entries(t), score, id)
  {
    EntriesSortedFromTree(t, NoScore, NoScore);
    AddPreservesValidTreap(t, score, id, priority);
    EntriesSortedFromTree(Add(t, score, id, priority), NoScore, NoScore);
    forall entry: Entry
      ensures entry in Entries(Add(t, score, id, priority)) <==> entry in InsertUnique(Entries(t), score, id)
    {
      AddPreservesEntryMembership(t, score, id, priority, entry);
    }
    SortedEntriesWithSameMembersAreEqual(Entries(Add(t, score, id, priority)), InsertUnique(Entries(t), score, id));
  }

  lemma ValidTreapRemoveRefinesModel(t: Treap, score: Score, id: DocId)
    requires ValidTreap(t)
    ensures SortedEntries(Entries(t))
    ensures Entries(Remove(t, score, id)) == RemoveOne(Entries(t), score, id)
  {
    EntriesSortedFromTree(t, NoScore, NoScore);
    RemovePreservesValidTreap(t, score, id);
    EntriesSortedFromTree(Remove(t, score, id), NoScore, NoScore);
    forall entry: Entry
      ensures entry in Entries(Remove(t, score, id)) <==> entry in RemoveOne(Entries(t), score, id)
    {
      RemovePreservesEntryMembership(t, NoScore, NoScore, score, id, entry);
    }
    SortedEntriesWithSameMembersAreEqual(Entries(Remove(t, score, id)), RemoveOne(Entries(t), score, id));
  }

  lemma PullPreservesEntries(t: Treap)
    requires t.Node?
    ensures Entries(Pull(t)) == Entries(t)
  {
  }

  lemma RotateRightPreservesEntries(t: Treap)
    requires t.Node? && t.left.Node?
    ensures Entries(RotateRight(t)) == Entries(t)
  {
  }

  lemma RotateLeftPreservesEntries(t: Treap)
    requires t.Node? && t.right.Node?
    ensures Entries(RotateLeft(t)) == Entries(t)
  {
  }
}