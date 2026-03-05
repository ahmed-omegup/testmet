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