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

  function RemoveId(ids: seq<DocId>, id: DocId): seq<DocId> {
    if |ids| == 0 then ids
    else if ids[0] == id then ids[1..]
    else if id < ids[0] then ids
    else [ids[0]] + RemoveId(ids[1..], id)
  }

  function InsertionIndex(ids: seq<DocId>, id: DocId): nat {
    if |ids| == 0 then 0
    else if ids[0] < id then 1 + InsertionIndex(ids[1..], id)
    else 0
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

  lemma EntriesFromIdsLength(score: Score, ids: seq<DocId>)
    ensures |EntriesFromIds(score, ids)| == |ids|
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsLength(score, ids[1..]);
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
    if |ids| == 0 {
    } else if ids[0] < doc {
      RankWithIdEntriesFromIds(score, ids[1..], doc);
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