// Dafny program DocsIndexBench.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.11.0.0
// Command-line arguments: run specs/dafny/DocsIndexBench.dfy --no-verify
// DocsIndexBench.dfy


module DocsIndexBench {
  const Modulus: int := 2147483647
  const Multiplier: int := 48271

  function NextState(state: int): int
    requires 0 < state < Modulus
    decreases state
  {
    var next: int := state * Multiplier % Modulus;
    if next == 0 then
      1
    else
      next
  }

  method NextRand(state: int, bound: nat)
      returns (next: int, value: nat)
    requires 0 < state < Modulus
    requires bound > 0
    ensures 0 < next < Modulus
    ensures value < bound
    decreases state, bound
  {
    next := NextState(state);
    value := next % bound;
  }

  function RefInsertUnique(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    decreases es, score, id
  {
    if |es| == 0 then
      [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then
      es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      [Entry(score, id)] + es
    else
      [es[0]] + RefInsertUnique(es[1..], score, id)
  }

  function RefRemoveOne(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    decreases es, score, id
  {
    if |es| == 0 then
      es
    else if es[0].score == score && es[0].id == id then
      es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      es
    else
      [es[0]] + RefRemoveOne(es[1..], score, id)
  }

  function RefCountStrictLess(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score < score then 1 else 0) + RefCountStrictLess(es[1..], score)
  }

  function RefCountAtMost(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score <= score then 1 else 0) + RefCountAtMost(es[1..], score)
  }

  function RefRankWithId(es: seq<Entry>, score: Score, id: DocId): nat
    decreases es, score, id
  {
    if |es| == 0 then
      0
    else if es[0].score < score || (es[0].score == score && es[0].id < id) then
      1 + RefRankWithId(es[1..], score, id)
    else
      0
  }

  function RefRank(es: seq<Entry>, score: Score, id: MaybeDocId): nat
    decreases es, score, id
  {
    match id
    case NoDoc() =>
      RefCountStrictLess(es, score)
    case SomeDoc(doc) =>
      RefRankWithId(es, score, doc)
  }

  function RefPositionAt(es: seq<Entry>, idx: nat): nat
    requires idx < |es|
    decreases es, idx
  {
    if idx == 0 then
      0
    else if es[idx - 1].score == es[idx].score then
      1 + RefPositionAt(es, idx - 1)
    else
      0
  }

  function RefGetAtRank(es: seq<Entry>, rank: nat): AtRank
    decreases es, rank
  {
    if rank >= |es| then
      Missing
    else
      Found(es[rank].score, es[rank].id, RefPositionAt(es, rank))
  }

  function RefCollectRange(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    decreases es, minScore, maxScore, limit
  {
    if |es| == 0 || limit == 0 then
      []
    else if es[0].score < minScore then
      RefCollectRange(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then
      []
    else
      [es[0].id] + RefCollectRange(es[1..], minScore, maxScore, limit - 1)
  }

  function RemoveAt<T>(xs: seq<T>, idx: nat): seq<T>
    requires idx < |xs|
    decreases xs, idx
  {
    if idx == 0 then
      xs[1..]
    else
      [xs[0]] + RemoveAt(xs[1..], idx - 1)
  }

  method {:print} CheckState(name: string, opIndex: nat, t: Treap, ref: seq<Entry>, rng: int, scoreRange: nat, nextId: DocId)
      returns (ok: bool, nextRng: int)
    requires 0 < rng < Modulus
    requires scoreRange > 0
    requires SumConsistent(t)
    ensures 0 < nextRng < Modulus
    decreases name, opIndex, t, ref, rng, scoreRange, nextId
  {
    ok := false;
    nextRng := rng;
    if !ValidTreap(t) {
      print name;
      print "": invalid treap at op "";
      print opIndex;
      print ""\n"";
      return;
    }
    if Entries(t) != ref {
      print name;
      print "": entries mismatch at op "";
      print opIndex;
      print ""\n"";
      print ""  treap size="";
      print |Entries(t)|;
      print "" ref size="";
      print |ref|;
      print ""\n"";
      return;
    }
    var scoreSel: nat;
    nextRng, scoreSel := NextRand(nextRng, scoreRange);
    var score := scoreSel as int;
    if TreapRank(t, score, NoDoc) != RefRank(ref, score, NoDoc) {
      print name;
      print "": rank(score,null) mismatch at op "";
      print opIndex;
      print "" score="";
      print score;
      print ""\n"";
      print ""  treap="";
      print TreapRank(t, score, NoDoc);
      print "" ref="";
      print RefRank(ref, score, NoDoc);
      print ""\n"";
      return;
    }
    var doc: DocId;
    if |ref| == 0 {
      doc := nextId;
    } else {
      var pick: nat;
      nextRng, pick := NextRand(nextRng, |ref|);
      doc := ref[pick].id;
    }
    if TreapRank(t, score, SomeDoc(doc)) != RefRank(ref, score, SomeDoc(doc)) {
      print name;
      print "": rank(score,id) mismatch at op "";
      print opIndex;
      print "" score="";
      print score;
      print "" doc="";
      print doc;
      print ""\n"";
      print ""  treap="";
      print TreapRank(t, score, SomeDoc(doc));
      print "" ref="";
      print RefRank(ref, score, SomeDoc(doc));
      print ""\n"";
      return;
    }
    if TreapCountAtMost(t, score) != RefCountAtMost(ref, score) {
      print name;
      print "": countAtMost mismatch at op "";
      print opIndex;
      print "" score="";
      print score;
      print ""\n"";
      print ""  treap="";
      print TreapCountAtMost(t, score);
      print "" ref="";
      print RefCountAtMost(ref, score);
      print ""\n"";
      return;
    }
    var rankBound := |ref| + 3;
    var rankPick: nat;
    nextRng, rankPick := NextRand(nextRng, rankBound);
    if TreapGetAtRank(t, rankPick) != RefGetAtRank(ref, rankPick) {
      print name;
      print "": getAtRank mismatch at op "";
      print opIndex;
      print "" rank="";
      print rankPick;
      print ""\n"";
      print ""  treap kind/value mismatch against reference\n"";
      return;
    }
    var minSel: nat;
    var widthSel: nat;
    var limitSel: nat;
    nextRng, minSel := NextRand(nextRng, scoreRange);
    nextRng, widthSel := NextRand(nextRng, scoreRange);
    nextRng, limitSel := NextRand(nextRng, 16);
    var minScore := minSel as int;
    var maxScore := minScore + widthSel as int;
    var limit := limitSel + 1;
    if TreapCollectRange(t, minScore, maxScore, limit) != RefCollectRange(ref, minScore, maxScore, limit) {
      print name;
      print "": collectRange mismatch at op "";
      print opIndex;
      print "" min="";
      print minScore;
      print "" max="";
      print maxScore;
      print "" limit="";
      print limit;
      print ""\n"";
      print ""  treap size="";
      print |TreapCollectRange(t, minScore, maxScore, limit)|;
      print "" ref size="";
      print |RefCollectRange(ref, minScore, maxScore, limit)|;
      print ""\n"";
      return;
    }
    ok := true;
  }

  method {:print} RunScenario(name: string, documents: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, scoreRange: nat, checksEveryOps: nat)
      returns (ok: bool)
    requires scoreRange > 0
    requires checksEveryOps > 0
    decreases name, documents, ticks, updatesPerTick, insertsPerTick, deletesPerTick, scoreRange, checksEveryOps
  {
    var t := Empty;
    var ref: seq<Entry> := [];
    var rng := 42;
    var nextId: DocId := 0;
    var opIndex: nat := 0;
    ok := false;
    print ""[dafny-bench] scenario="";
    print name;
    print "" docs="";
    print documents;
    print "" ticks="";
    print ticks;
    print "" updates/tick="";
    print updatesPerTick;
    print "" inserts/tick="";
    print insertsPerTick;
    print "" deletes/tick="";
    print deletesPerTick;
    print "" scoreRange="";
    print scoreRange;
    print "" checksEveryOps="";
    print checksEveryOps;
    print ""\n"";
    var i: nat := 0;
    while i < documents
      invariant i <= documents
      invariant SumConsistent(t)
      invariant 0 < rng < Modulus
      decreases documents - i
    {
      var scoreSel: nat;
      rng, scoreSel := NextRand(rng, scoreRange);
      var score := scoreSel as int;
      var prioSel: nat;
      rng, prioSel := NextRand(rng, 1000000);
      t := Add(t, score, nextId, prioSel as int);
      ref := RefInsertUnique(ref, score, nextId);
      nextId := nextId + 1;
      opIndex := opIndex + 1;
      i := i + 1;
    }
    var seededOk: bool;
    seededOk, rng := CheckState(name + "" seed"", opIndex, t, ref, rng, scoreRange, nextId);
    if !seededOk {
      return;
    }
    var tick: nat := 0;
    while tick < ticks
      invariant tick <= ticks
      invariant SumConsistent(t)
      invariant 0 < rng < Modulus
      decreases ticks - tick
    {
      var u: nat := 0;
      while u < updatesPerTick
        invariant u <= updatesPerTick
        invariant SumConsistent(t)
        invariant 0 < rng < Modulus
        decreases updatesPerTick - u
      {
        if |ref| > 0 {
          var pick: nat;
          rng, pick := NextRand(rng, |ref|);
          var chosen := ref[pick];
          var newScoreSel: nat;
          rng, newScoreSel := NextRand(rng, scoreRange);
          var newScore := newScoreSel as int;
          var prioSel: nat;
          rng, prioSel := NextRand(rng, 1000000);
          t := Remove(t, chosen.score, chosen.id);
          ref := RefRemoveOne(ref, chosen.score, chosen.id);
          t := Add(t, newScore, chosen.id, prioSel as int);
          ref := RefInsertUnique(ref, newScore, chosen.id);
          opIndex := opIndex + 1;
          if opIndex % checksEveryOps == 0 {
            var stepOk: bool;
            stepOk, rng := CheckState(name, opIndex, t, ref, rng, scoreRange, nextId);
            if !stepOk {
              return;
            }
          }
        }
        u := u + 1;
      }
      var ins: nat := 0;
      while ins < insertsPerTick
        invariant ins <= insertsPerTick
        invariant SumConsistent(t)
        invariant 0 < rng < Modulus
        decreases insertsPerTick - ins
      {
        var scoreSel: nat;
        rng, scoreSel := NextRand(rng, scoreRange);
        var prioSel: nat;
        rng, prioSel := NextRand(rng, 1000000);
        var score := scoreSel as int;
        t := Add(t, score, nextId, prioSel as int);
        ref := RefInsertUnique(ref, score, nextId);
        nextId := nextId + 1;
        opIndex := opIndex + 1;
        if opIndex % checksEveryOps == 0 {
          var insOk: bool;
          insOk, rng := CheckState(name, opIndex, t, ref, rng, scoreRange, nextId);
          if !insOk {
            return;
          }
        }
        ins := ins + 1;
      }
      var del: nat := 0;
      while del < deletesPerTick
        invariant del <= deletesPerTick
        invariant SumConsistent(t)
        invariant 0 < rng < Modulus
        decreases deletesPerTick - del
      {
        if |ref| > 0 {
          var pick: nat;
          rng, pick := NextRand(rng, |ref|);
          var chosen := ref[pick];
          t := Remove(t, chosen.score, chosen.id);
          ref := RefRemoveOne(ref, chosen.score, chosen.id);
          opIndex := opIndex + 1;
          if opIndex % checksEveryOps == 0 {
            var delOk: bool;
            delOk, rng := CheckState(name, opIndex, t, ref, rng, scoreRange, nextId);
            if !delOk {
              return;
            }
          }
        }
        del := del + 1;
      }
      tick := tick + 1;
    }
    var finalOk: bool;
    finalOk, rng := CheckState(name + "" final"", opIndex, t, ref, rng, scoreRange, nextId);
    if !finalOk {
      return;
    }
    print ""[dafny-bench] passed scenario="";
    print name;
    print "" totalOps="";
    print opIndex;
    print "" finalEntries="";
    print |ref|;
    print ""\n"";
    ok := true;
  }

  method {:main} {:print} Main(_noArgsParameter: seq<seq<char>>)
  {
    var ok := RunScenario(""correctness-small"", 400, 40, 20, 4, 4, 1000, 1);
    if !ok {
      return;
    }
    ok := RunScenario(""benchmark-like"", 2500, 120, 125, 25, 25, 2500, 200);
    if !ok {
      return;
    }
    print ""[dafny-bench] all scenarios passed\n"";
  }

  import opened DocsIndexModel

  import opened DocsIndexTreap
}

module DocsIndexTreap {
  function NodeCount(t: Treap): nat
    decreases t
  {
    if t.Empty? then
      0
    else
      1 + NodeCount(t.left) + NodeCount(t.right)
  }

  function Sum(t: Treap): nat
    decreases t
  {
    if t.Empty? then
      0
    else
      t.sum
  }

  function StructuralSum(t: Treap): nat
    decreases t
  {
    if t.Empty? then
      0
    else
      |t.ids| + StructuralSum(t.left) + StructuralSum(t.right)
  }

  predicate SortedStrictIds(ids: seq<DocId>)
    decreases ids
  {
    forall i: int, j: int {:trigger ids[j], ids[i]} :: 
      0 <= i < j < |ids| ==>
        ids[i] < ids[j]
  }

  predicate ScoreAboveLower(score: Score, lo: MaybeScore)
    decreases score, lo
  {
    match lo
    case NoScore() =>
      true
    case SomeScore(v) =>
      v < score
  }

  predicate ScoreBelowUpper(score: Score, hi: MaybeScore)
    decreases score, hi
  {
    match hi
    case NoScore() =>
      true
    case SomeScore(v) =>
      score < v
  }

  function RootPrio(t: Treap): Priority
    decreases t
  {
    if t.Node? then
      t.prio
    else
      0
  }

  predicate SumConsistent(t: Treap)
    decreases t
  {
    if t.Empty? then
      true
    else
      SumConsistent(t.left) && SumConsistent(t.right) && t.sum == |t.ids| + Sum(t.left) + Sum(t.right)
  }

  predicate HeapOrdered(t: Treap)
    decreases t
  {
    if t.Empty? then
      true
    else
      (if t.left.Node? then t.left.prio <= t.prio else true) && (if t.right.Node? then t.right.prio <= t.prio else true) && HeapOrdered(t.left) && HeapOrdered(t.right)
  }

  predicate OrderedByScore(t: Treap, lo: MaybeScore, hi: MaybeScore)
    decreases t, lo, hi
  {
    if t.Empty? then
      true
    else
      ScoreAboveLower(t.score, lo) && ScoreBelowUpper(t.score, hi) && OrderedByScore(t.left, lo, SomeScore(t.score)) && OrderedByScore(t.right, SomeScore(t.score), hi)
  }

  predicate IdsSortedInTree(t: Treap)
    decreases t
  {
    if t.Empty? then
      true
    else
      SortedStrictIds(t.ids) && IdsSortedInTree(t.left) && IdsSortedInTree(t.right)
  }

  predicate NonEmptyBuckets(t: Treap)
    decreases t
  {
    if t.Empty? then
      true
    else
      |t.ids| > 0 && NonEmptyBuckets(t.left) && NonEmptyBuckets(t.right)
  }

  predicate ValidTreap(t: Treap)
    decreases t
  {
    SumConsistent(t) &&
    HeapOrdered(t) &&
    OrderedByScore(t, NoScore, NoScore) &&
    IdsSortedInTree(t) &&
    NonEmptyBuckets(t)
  }

  function EntriesFromIds(score: Score, ids: seq<DocId>): seq<Entry>
    decreases score, ids
  {
    if |ids| == 0 then
      []
    else
      [Entry(score, ids[0])] + EntriesFromIds(score, ids[1..])
  }

  function Entries(t: Treap): seq<Entry>
    decreases t
  {
    if t.Empty? then
      []
    else
      Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right)
  }

  function InsertId(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if |ids| == 0 then
      [id]
    else if ids[0] == id then
      ids
    else if id < ids[0] then
      [id] + ids
    else
      [ids[0]] + InsertId(ids[1..], id)
  }

  function RemoveId(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if |ids| == 0 then
      ids
    else if ids[0] == id then
      ids[1..]
    else if id < ids[0] then
      ids
    else
      [ids[0]] + RemoveId(ids[1..], id)
  }

  function InsertionIndex(ids: seq<DocId>, id: DocId): nat
    decreases ids, id
  {
    if |ids| == 0 then
      0
    else if ids[0] < id then
      1 + InsertionIndex(ids[1..], id)
    else
      0
  }

  function Pull(t: Treap): Treap
    requires t.Node?
    decreases t
  {
    Node(t.score, t.ids, t.prio, |t.ids| + Sum(t.left) + Sum(t.right), t.left, t.right)
  }

  function RotateRight(t: Treap): Treap
    requires t.Node? && t.left.Node?
    decreases t
  {
    var demoted: Treap := Pull(Node(t.score, t.ids, t.prio, 0, t.left.right, t.right));
    Pull(Node(t.left.score, t.left.ids, t.left.prio, 0, t.left.left, demoted))
  }

  function RotateLeft(t: Treap): Treap
    requires t.Node? && t.right.Node?
    decreases t
  {
    var demoted: Treap := Pull(Node(t.score, t.ids, t.prio, 0, t.left, t.right.left));
    Pull(Node(t.right.score, t.right.ids, t.right.prio, 0, demoted, t.right.right))
  }

  function Join(left: Treap, right: Treap): Treap
    requires SumConsistent(left)
    requires SumConsistent(right)
    ensures SumConsistent(Join(left, right))
    decreases NodeCount(left) + NodeCount(right)
  {
    if left.Empty? then
      right
    else if right.Empty? then
      left
    else if left.prio > right.prio then
      Pull(Node(left.score, left.ids, left.prio, 0, left.left, Join(left.right, right)))
    else
      Pull(Node(right.score, right.ids, right.prio, 0, Join(left, right.left), right.right))
  }

  function Add(t: Treap, score: Score, id: DocId, prioForNew: Priority): Treap
    requires SumConsistent(t)
    ensures SumConsistent(Add(t, score, id, prioForNew))
    decreases NodeCount(t)
  {
    if t.Empty? then
      Node(score, [id], prioForNew, 1, Empty, Empty)
    else if score == t.score then
      Pull(Node(t.score, InsertId(t.ids, id), t.prio, 0, t.left, t.right))
    else if score < t.score then
      var left2: Treap := Add(t.left, score, id, prioForNew);
      var n: Treap := Pull(Node(t.score, t.ids, t.prio, 0, left2, t.right));
      if left2.Node? && left2.prio > t.prio then
        RotateRight(n)
      else
        n
    else
      var right2: Treap := Add(t.right, score, id, prioForNew); var n: Treap := Pull(Node(t.score, t.ids, t.prio, 0, t.left, right2)); if right2.Node? && right2.prio > t.prio then RotateLeft(n) else n
  }

  function Remove(t: Treap, score: Score, id: DocId): Treap
    requires SumConsistent(t)
    ensures SumConsistent(Remove(t, score, id))
    decreases NodeCount(t)
  {
    if t.Empty? then
      Empty
    else if score == t.score then
      var ids2: seq<DocId> := RemoveId(t.ids, id);
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
    if t.Empty? then
      0
    else if score < t.score then
      TreapRank(t.left, score, id)
    else if score > t.score then
      Sum(t.left) + |t.ids| + TreapRank(t.right, score, id)
    else
      Sum(t.left) + match id case NoDoc() => 0 case SomeDoc(doc) => InsertionIndex(t.ids, doc)
  }

  function TreapCountAtMost(t: Treap, score: Score): nat
    requires SumConsistent(t)
    decreases NodeCount(t)
  {
    if t.Empty? then
      0
    else if score < t.score then
      TreapCountAtMost(t.left, score)
    else
      Sum(t.left) + |t.ids| + TreapCountAtMost(t.right, score)
  }

  function TreapGetAtRank(t: Treap, rank: nat): AtRank
    requires SumConsistent(t)
    decreases NodeCount(t), rank
  {
    if t.Empty? then
      Missing
    else if rank < Sum(t.left) then
      TreapGetAtRank(t.left, rank)
    else if rank < Sum(t.left) + |t.ids| then
      var pos: int := rank - Sum(t.left);
      Found(t.score, t.ids[pos], pos)
    else
      TreapGetAtRank(t.right, rank - (Sum(t.left) + |t.ids|))
  }

  function TakePrefix<T>(xs: seq<T>, limit: nat): seq<T>
    decreases xs, limit
  {
    if |xs| == 0 || limit == 0 then
      []
    else
      [xs[0]] + TakePrefix(xs[1..], limit - 1)
  }

  function SatSub(a: nat, b: nat): nat
    decreases a, b
  {
    if b <= a then
      a - b
    else
      0
  }

  function TreapCollectRange(t: Treap, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SumConsistent(t)
    decreases NodeCount(t)
  {
    if t.Empty? || limit == 0 then
      []
    else
      var leftOut: seq<DocId> := if minScore < t.score then TreapCollectRange(t.left, minScore, maxScore, limit) else []; var rem1: nat := SatSub(limit, |leftOut|); if rem1 == 0 then leftOut else var selfOut: seq<int> := if t.score >= minScore && t.score <= maxScore then TakePrefix(t.ids, rem1) else []; var rem2: nat := SatSub(rem1, |selfOut|); if rem2 == 0 then leftOut + selfOut else var rightOut: seq<DocId> := if t.score < maxScore then TreapCollectRange(t.right, minScore, maxScore, rem2) else []; leftOut + selfOut + rightOut
  }

  function ModelRankOnEntries(t: Treap, score: Score, id: MaybeDocId): nat
    decreases t, score, id
  {
    Rank(Entries(t), score, id)
  }

  function ModelCountAtMostOnEntries(t: Treap, score: Score): nat
    decreases t, score
  {
    CountAtMost(Entries(t), score)
  }

  function ModelGetAtRankOnEntries(t: Treap, rank: nat): AtRank
    requires SortedEntries(Entries(t))
    decreases t, rank
  {
    GetAtRank(Entries(t), rank)
  }

  function ModelCollectRangeOnEntries(t: Treap, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SortedEntries(Entries(t))
    decreases t, minScore, maxScore, limit
  {
    CollectRange(Entries(t), minScore, maxScore, limit)
  }

  predicate AllScoresLt(es: seq<Entry>, score: Score)
    decreases es, score
  {
    if |es| == 0 then
      true
    else
      es[0].score < score && AllScoresLt(es[1..], score)
  }

  predicate AllScoresLe(es: seq<Entry>, score: Score)
    decreases es, score
  {
    if |es| == 0 then
      true
    else
      es[0].score <= score && AllScoresLe(es[1..], score)
  }

  predicate AllScoresGt(es: seq<Entry>, score: Score)
    decreases es, score
  {
    if |es| == 0 then
      true
    else
      es[0].score > score && AllScoresGt(es[1..], score)
  }

  lemma /*{:_inductionTrigger EntriesFromIds(score, ids)}*/ /*{:_induction score, ids}*/ EntriesFromIdsLength(score: Score, ids: seq<DocId>)
    ensures |EntriesFromIds(score, ids)| == |ids|
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsLength(score, ids[1..]);
    }
  }

  lemma /*{:_inductionTrigger Entries(t)}*/ /*{:_inductionTrigger Sum(t)}*/ /*{:_inductionTrigger SumConsistent(t)}*/ /*{:_induction t}*/ SumEqualsEntriesLength(t: Treap)
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

  lemma /*{:_inductionTrigger AllScoresLt(EntriesFromIds(score, ids), bound)}*/ /*{:_induction score, ids, bound}*/ EntriesFromIdsAllLt(score: Score, ids: seq<DocId>, bound: Score)
    requires score < bound
    ensures AllScoresLt(EntriesFromIds(score, ids), bound)
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsAllLt(score, ids[1..], bound);
    }
  }

  lemma /*{:_inductionTrigger AllScoresLe(EntriesFromIds(score, ids), bound)}*/ /*{:_induction score, ids, bound}*/ EntriesFromIdsAllLe(score: Score, ids: seq<DocId>, bound: Score)
    requires score <= bound
    ensures AllScoresLe(EntriesFromIds(score, ids), bound)
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsAllLe(score, ids[1..], bound);
    }
  }

  lemma /*{:_inductionTrigger AllScoresGt(EntriesFromIds(score, ids), bound)}*/ /*{:_induction score, ids, bound}*/ EntriesFromIdsAllGt(score: Score, ids: seq<DocId>, bound: Score)
    requires score > bound
    ensures AllScoresGt(EntriesFromIds(score, ids), bound)
    decreases |ids|
  {
    if |ids| > 0 {
      EntriesFromIdsAllGt(score, ids[1..], bound);
    }
  }

  lemma /*{:_inductionTrigger AllScoresLt(xs + ys, score)}*/ /*{:_induction xs, ys, score}*/ AllScoresLtConcat(xs: seq<Entry>, ys: seq<Entry>, score: Score)
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

  lemma /*{:_inductionTrigger AllScoresLe(xs + ys, score)}*/ /*{:_induction xs, ys, score}*/ AllScoresLeConcat(xs: seq<Entry>, ys: seq<Entry>, score: Score)
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

  lemma /*{:_inductionTrigger AllScoresGt(xs + ys, score)}*/ /*{:_induction xs, ys, score}*/ AllScoresGtConcat(xs: seq<Entry>, ys: seq<Entry>, score: Score)
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

  lemma /*{:_inductionTrigger AllScoresLe(xs, score)}*/ /*{:_inductionTrigger AllScoresLt(xs, score)}*/ /*{:_induction xs, score}*/ AllScoresLtImpliesLe(xs: seq<Entry>, score: Score)
    requires AllScoresLt(xs, score)
    ensures AllScoresLe(xs, score)
    decreases |xs|
  {
    if |xs| > 0 {
      AllScoresLtImpliesLe(xs[1..], score);
    }
  }

  lemma /*{:_inductionTrigger AllScoresLt(xs, wide), AllScoresLt(xs, tight)}*/ /*{:_induction xs, tight, wide}*/ AllScoresLtWeaken(xs: seq<Entry>, tight: Score, wide: Score)
    requires tight < wide
    requires AllScoresLt(xs, tight)
    ensures AllScoresLt(xs, wide)
    decreases |xs|
  {
    if |xs| > 0 {
      AllScoresLtWeaken(xs[1..], tight, wide);
    }
  }

  lemma /*{:_inductionTrigger AllScoresGt(xs, wide), AllScoresGt(xs, tight)}*/ /*{:_induction xs, tight, wide}*/ AllScoresGtWeaken(xs: seq<Entry>, tight: Score, wide: Score)
    requires wide < tight
    requires AllScoresGt(xs, tight)
    ensures AllScoresGt(xs, wide)
    decreases |xs|
  {
    if |xs| > 0 {
      AllScoresGtWeaken(xs[1..], tight, wide);
    }
  }

  lemma /*{:_inductionTrigger OrderedByScore(t, lo, MaybeScore.SomeScore(bound))}*/ /*{:_induction t, lo, bound}*/ EntriesLtFromOrdered(t: Treap, lo: MaybeScore, bound: Score)
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

  lemma /*{:_inductionTrigger OrderedByScore(t, MaybeScore.SomeScore(bound), hi)}*/ /*{:_induction t, bound, hi}*/ EntriesGtFromOrdered(t: Treap, bound: Score, hi: MaybeScore)
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

  lemma /*{:_inductionTrigger CountStrictLessScore(es, score)}*/ /*{:_inductionTrigger AllScoresGt(es, score)}*/ /*{:_induction es, score}*/ CountStrictLessAllGtZero(es: seq<Entry>, score: Score)
    requires AllScoresGt(es, score)
    ensures CountStrictLessScore(es, score) == 0
    decreases |es|
  {
    if |es| > 0 {
      CountStrictLessAllGtZero(es[1..], score);
    }
  }

  lemma /*{:_inductionTrigger prefix + rest, AllScoresLt(prefix, score)}*/ /*{:_induction prefix, rest, score}*/ CountStrictLessPrefixLt(prefix: seq<Entry>, rest: seq<Entry>, score: Score)
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

  lemma /*{:_inductionTrigger prefix + suffix, AllScoresGt(suffix, score)}*/ /*{:_induction prefix, suffix, score}*/ CountStrictLessSuffixGt(prefix: seq<Entry>, suffix: seq<Entry>, score: Score)
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

  lemma /*{:_inductionTrigger EntriesFromIds(score, ids)}*/ /*{:_induction score, ids}*/ CountStrictLessEntriesFromIdsEq(score: Score, ids: seq<DocId>)
    ensures CountStrictLessScore(EntriesFromIds(score, ids), score) == 0
    decreases |ids|
  {
    if |ids| > 0 {
      CountStrictLessEntriesFromIdsEq(score, ids[1..]);
    }
  }

  lemma /*{:_inductionTrigger RankWithId(es, score, id)}*/ /*{:_induction es, score, id}*/ RankWithIdAllGtZero(es: seq<Entry>, score: Score, id: DocId)
    requires AllScoresGt(es, score)
    ensures RankWithId(es, score, id) == 0
    decreases es, score, id
  {
    if |es| > 0 {
      assert es[0].score > score;
    }
  }

  lemma /*{:_inductionTrigger RankWithId(prefix + rest, score, id)}*/ /*{:_induction prefix, rest, score, id}*/ RankWithIdPrefixLt(prefix: seq<Entry>, rest: seq<Entry>, score: Score, id: DocId)
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

  lemma /*{:_inductionTrigger RankWithId(prefix + suffix, score, id)}*/ /*{:_induction prefix, suffix, score, id}*/ RankWithIdSuffixGt(prefix: seq<Entry>, suffix: seq<Entry>, score: Score, id: DocId)
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

  lemma /*{:_inductionTrigger RankWithId(EntriesFromIds(score, ids), score, doc)}*/ /*{:_induction score, ids, doc}*/ RankWithIdEntriesFromIds(score: Score, ids: seq<DocId>, doc: DocId)
    requires SortedStrictIds(ids)
    ensures RankWithId(EntriesFromIds(score, ids), score, doc) == InsertionIndex(ids, doc)
    decreases |ids|
  {
    if |ids| == 0 {
    } else if ids[0] < doc {
      RankWithIdEntriesFromIds(score, ids[1..], doc);
    }
  }

  lemma /*{:_inductionTrigger CountAtMost(es, score)}*/ /*{:_inductionTrigger AllScoresGt(es, score)}*/ /*{:_induction es, score}*/ CountAtMostAllGtZero(es: seq<Entry>, score: Score)
    requires AllScoresGt(es, score)
    ensures CountAtMost(es, score) == 0
    decreases |es|
  {
    if |es| > 0 {
      CountAtMostAllGtZero(es[1..], score);
    }
  }

  lemma /*{:_inductionTrigger prefix + rest, AllScoresLe(prefix, score)}*/ /*{:_induction prefix, rest, score}*/ CountAtMostPrefixLe(prefix: seq<Entry>, rest: seq<Entry>, score: Score)
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

  lemma /*{:_inductionTrigger prefix + suffix, AllScoresGt(suffix, score)}*/ /*{:_induction prefix, suffix, score}*/ CountAtMostSuffixGt(prefix: seq<Entry>, suffix: seq<Entry>, score: Score)
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

  lemma /*{:_inductionTrigger TreapRank(t, score, MaybeDocId.NoDoc), OrderedByScore(t, lo, hi)}*/ /*{:_induction t, lo, hi, score}*/ TreapRankNoDocRefinesBounded(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score)
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
      ==
        {
        }
        TreapRank(t.left, score, NoDoc);
      ==
        {
        }
        CountStrictLessScore(Entries(t.left), score);
      ==
        {
        }
        CountStrictLessScore(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score);
      ==
        {
        }
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
      assert Entries(t) == Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right);
      calc {
        TreapRank(t, score, NoDoc);
      ==
        {
        }
        Sum(t.left) + |t.ids| + TreapRank(t.right, score, NoDoc);
      ==
        {
        }
        |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)| + CountStrictLessScore(Entries(t.right), score);
      ==
        {
        }
        |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + CountStrictLessScore(Entries(t.right), score);
      ==
        {
        }
        CountStrictLessScore(Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right), score);
      ==
        {
        }
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
      ==
        {
        }
        Sum(t.left);
      ==
        {
        }
        |Entries(t.left)|;
      ==
        {
        }
        CountStrictLessScore(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score);
      ==
        {
        }
        CountStrictLessScore(Entries(t), score);
      }
    }
  }

  lemma /*{:_inductionTrigger TreapRank(t, score, MaybeDocId.SomeDoc(doc)), OrderedByScore(t, lo, hi)}*/ /*{:_induction t, lo, hi, score, doc}*/ TreapRankSomeDocRefinesBounded(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score, doc: DocId)
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
      ==
        {
        }
        TreapRank(t.left, score, SomeDoc(doc));
      ==
        {
        }
        RankWithId(Entries(t.left), score, doc);
      ==
        {
        }
        RankWithId(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score, doc);
      ==
        {
        }
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
      assert Entries(t) == Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right);
      calc {
        TreapRank(t, score, SomeDoc(doc));
      ==
        {
        }
        Sum(t.left) + |t.ids| + TreapRank(t.right, score, SomeDoc(doc));
      ==
        {
        }
        |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)| + RankWithId(Entries(t.right), score, doc);
      ==
        {
        }
        |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + RankWithId(Entries(t.right), score, doc);
      ==
        {
        }
        RankWithId(Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right), score, doc);
      ==
        {
        }
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
      assert RankWithId(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score, doc) == |Entries(t.left)| + RankWithId(EntriesFromIds(t.score, t.ids), score, doc);
      assert Entries(t) == Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right));
      calc {
        TreapRank(t, score, SomeDoc(doc));
      ==
        {
        }
        Sum(t.left) + InsertionIndex(t.ids, doc);
      ==
        {
        }
        |Entries(t.left)| + RankWithId(EntriesFromIds(t.score, t.ids), score, doc);
      ==
        {
        }
        RankWithId(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score, doc);
      ==
        {
        }
        RankWithId(Entries(t), score, doc);
      }
    }
  }

  lemma /*{:_inductionTrigger Rank(Entries(t), score, id)}*/ /*{:_inductionTrigger TreapRank(t, score, id)}*/ /*{:_induction t, score, id}*/ TreapRankRefinesModel(t: Treap, score: Score, id: MaybeDocId)
    requires ValidTreap(t)
    ensures TreapRank(t, score, id) == Rank(Entries(t), score, id)
    decreases t, score, id
  {
    match id
    case {:split false} NoDoc() =>
      TreapRankNoDocRefinesBounded(t, NoScore, NoScore, score);
      assert Rank(Entries(t), score, NoDoc) == CountStrictLessScore(Entries(t), score);
    case {:split false} SomeDoc(doc) =>
      TreapRankSomeDocRefinesBounded(t, NoScore, NoScore, score, doc);
      assert Rank(Entries(t), score, SomeDoc(doc)) == RankWithId(Entries(t), score, doc);
  }

  lemma /*{:_inductionTrigger TreapCountAtMost(t, score), OrderedByScore(t, lo, hi)}*/ /*{:_induction t, lo, hi, score}*/ TreapCountAtMostRefinesModelBounded(t: Treap, lo: MaybeScore, hi: MaybeScore, score: Score)
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
      ==
        {
        }
        TreapCountAtMost(t.left, score);
      ==
        {
        }
        CountAtMost(Entries(t.left), score);
      ==
        {
        }
        CountAtMost(Entries(t.left) + (EntriesFromIds(t.score, t.ids) + Entries(t.right)), score);
      ==
        {
        }
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
      assert CountAtMost(Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right), score) == |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + CountAtMost(Entries(t.right), score);
      assert Entries(t) == Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right);
      calc {
        TreapCountAtMost(t, score);
      ==
        {
        }
        Sum(t.left) + |t.ids| + TreapCountAtMost(t.right, score);
      ==
        {
        }
        |Entries(t.left)| + |EntriesFromIds(t.score, t.ids)| + CountAtMost(Entries(t.right), score);
      ==
        {
        }
        |Entries(t.left) + EntriesFromIds(t.score, t.ids)| + CountAtMost(Entries(t.right), score);
      ==
        {
        }
        CountAtMost(Entries(t.left) + EntriesFromIds(t.score, t.ids) + Entries(t.right), score);
      ==
        {
        }
        CountAtMost(Entries(t), score);
      }
    }
  }

  lemma /*{:_inductionTrigger CountAtMost(Entries(t), score)}*/ /*{:_inductionTrigger TreapCountAtMost(t, score)}*/ /*{:_induction t, score}*/ TreapCountAtMostRefinesModel(t: Treap, score: Score)
    requires ValidTreap(t)
    ensures TreapCountAtMost(t, score) == CountAtMost(Entries(t), score)
    decreases t, score
  {
    TreapCountAtMostRefinesModelBounded(t, NoScore, NoScore, score);
  }

  lemma /*{:_inductionTrigger Pull(t)}*/ /*{:_inductionTrigger t.Node?}*/ /*{:_induction t}*/ PullPreservesEntries(t: Treap)
    requires t.Node?
    ensures Entries(Pull(t)) == Entries(t)
    decreases t
  {
  }

  lemma /*{:_inductionTrigger RotateRight(t)}*/ /*{:_inductionTrigger t.left}*/ /*{:_induction t}*/ RotateRightPreservesEntries(t: Treap)
    requires t.Node? && t.left.Node?
    ensures Entries(RotateRight(t)) == Entries(t)
    decreases t
  {
  }

  lemma /*{:_inductionTrigger RotateLeft(t)}*/ /*{:_inductionTrigger t.right}*/ /*{:_induction t}*/ RotateLeftPreservesEntries(t: Treap)
    requires t.Node? && t.right.Node?
    ensures Entries(RotateLeft(t)) == Entries(t)
    decreases t
  {
  }

  import opened DocsIndexModel

  type Priority = int

  datatype MaybeScore = NoScore | SomeScore(v: Score)

  datatype Treap = Empty | Node(score: Score, ids: seq<DocId>, prio: Priority, sum: nat, left: Treap, right: Treap)
}

module DocsIndexModel {
  function LexLt(a: Entry, b: Entry): bool
    decreases a, b
  {
    a.score < b.score || (a.score == b.score && a.id < b.id)
  }

  predicate SortedEntries(es: seq<Entry>)
    decreases es
  {
    forall i: int, j: int {:trigger es[j], es[i]} :: 
      0 <= i < j < |es| ==>
        LexLt(es[i], es[j])
  }

  function CountStrictLessScore(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score < score then 1 else 0) + CountStrictLessScore(es[1..], score)
  }

  function CountAtMost(es: seq<Entry>, score: Score): nat
    decreases es, score
  {
    if |es| == 0 then
      0
    else
      (if es[0].score <= score then 1 else 0) + CountAtMost(es[1..], score)
  }

  function RankWithId(es: seq<Entry>, score: Score, id: DocId): nat
    decreases es, score, id
  {
    if |es| == 0 then
      0
    else if es[0].score < score || (es[0].score == score && es[0].id < id) then
      1 + RankWithId(es[1..], score, id)
    else
      0
  }

  function Rank(es: seq<Entry>, score: Score, id: MaybeDocId): nat
    decreases es, score, id
  {
    match id
    case NoDoc() =>
      CountStrictLessScore(es, score)
    case SomeDoc(doc) =>
      RankWithId(es, score, doc)
  }

  function InsertUnique(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    decreases es, score, id
  {
    if |es| == 0 then
      [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then
      es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      [Entry(score, id)] + es
    else
      [es[0]] + InsertUnique(es[1..], score, id)
  }

  function RemoveOne(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    requires SortedEntries(es)
    decreases es, score, id
  {
    if |es| == 0 then
      es
    else if es[0].score == score && es[0].id == id then
      es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      es
    else
      [es[0]] + RemoveOne(es[1..], score, id)
  }

  function PositionAt(es: seq<Entry>, idx: nat): nat
    requires SortedEntries(es)
    requires idx < |es|
    decreases es, idx
  {
    if idx == 0 then
      0
    else if es[idx - 1].score == es[idx].score then
      1 + PositionAt(es, idx - 1)
    else
      0
  }

  function GetAtRank(es: seq<Entry>, rank: nat): AtRank
    requires SortedEntries(es)
    decreases es, rank
  {
    if rank >= |es| then
      Missing
    else
      Found(es[rank].score, es[rank].id, PositionAt(es, rank))
  }

  function CollectRange(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    requires SortedEntries(es)
    decreases es, minScore, maxScore, limit
  {
    if |es| == 0 || limit == 0 then
      []
    else if es[0].score < minScore then
      CollectRange(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then
      []
    else
      [es[0].id] + CollectRange(es[1..], minScore, maxScore, limit - 1)
  }

  lemma /*{:_inductionTrigger CountStrictLessScore(es, score)}*/ /*{:_inductionTrigger Rank(es, score, MaybeDocId.NoDoc)}*/ /*{:_induction es, score}*/ RankNoDocMatchesPrefix(es: seq<Entry>, score: Score)
    ensures Rank(es, score, NoDoc) == CountStrictLessScore(es, score)
    decreases es, score
  {
  }

  lemma RankWithinBounds(es: seq<Entry>, score: Score, id: MaybeDocId)
    ensures Rank(es, score, id) <= |es|
    decreases es, score, id
  {
    match id
    case {:split false} NoDoc() =>
      CountStrictLessWithinBounds(es, score);
    case {:split false} SomeDoc(doc) =>
      RankWithIdWithinBounds(es, score, doc);
  }

  lemma /*{:_inductionTrigger CountStrictLessScore(es, score)}*/ /*{:_induction es, score}*/ CountStrictLessWithinBounds(es: seq<Entry>, score: Score)
    ensures CountStrictLessScore(es, score) <= |es|
    decreases es, score
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

  lemma /*{:_inductionTrigger RankWithId(es, score, id)}*/ /*{:_induction es, score, id}*/ RankWithIdWithinBounds(es: seq<Entry>, score: Score, id: DocId)
    ensures RankWithId(es, score, id) <= |es|
    decreases es, score, id
  {
    if |es| == 0 {
    } else if es[0].score < score || (es[0].score == score && es[0].id < id) {
      RankWithIdWithinBounds(es[1..], score, id);
      assert RankWithId(es, score, id) == 1 + RankWithId(es[1..], score, id);
      assert |es| == 1 + |es[1..]|;
    }
  }

  lemma /*{:_inductionTrigger CountAtMost(es, hi), CountAtMost(es, lo)}*/ /*{:_induction es, lo, hi}*/ CountAtMostMonotone(es: seq<Entry>, lo: Score, hi: Score)
    requires lo <= hi
    ensures CountAtMost(es, lo) <= CountAtMost(es, hi)
    decreases es, lo, hi
  {
    if |es| == 0 {
    } else {
      CountAtMostMonotone(es[1..], lo, hi);
      if es[0].score <= lo {
        assert es[0].score <= hi;
      }
    }
  }

  type Score = int

  type DocId = int

  datatype MaybeDocId = NoDoc | SomeDoc(doc: DocId)

  datatype AtRank = Missing | Found(score: Score, id: DocId, position: nat)

  datatype Entry = Entry(score: Score, id: DocId)
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      // Be sure to use ElementCount to avoid casting into 32 bits
      // integers that could lead to overflows (see https://github.com/dafny-lang/dafny/issues/5554)
      return th.ElementCount < other.ElementCount && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    internal volatile ISequence<T> left, right;
    internal ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    internal ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
// end of class FuncExtensions
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
// end of class FuncExtensions
namespace DocsIndexModel {

  public partial class __default {
    public static bool LexLt(DocsIndexModel._IEntry a, DocsIndexModel._IEntry b)
    {
      return (((a).dtor_score) < ((b).dtor_score)) || ((((a).dtor_score) == ((b).dtor_score)) && (((a).dtor_id) < ((b).dtor_id)));
    }
    public static bool SortedEntries(Dafny.ISequence<DocsIndexModel._IEntry> es) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DocsIndexModel._IEntry>, bool>>((_0_es) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_0_es).Count)), true, (((_forall_var_0) => {
        BigInteger _1_i = (BigInteger)_forall_var_0;
        return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_1_i) + (BigInteger.One), new BigInteger((_0_es).Count)), true, (((_forall_var_1) => {
          BigInteger _2_j = (BigInteger)_forall_var_1;
          return !((((_1_i).Sign != -1) && ((_1_i) < (_2_j))) && ((_2_j) < (new BigInteger((_0_es).Count)))) || (DocsIndexModel.__default.LexLt((_0_es).Select(_1_i), (_0_es).Select(_2_j)));
        })));
      }))))(es);
    }
    public static BigInteger CountStrictLessScore(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) < (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger CountAtMost(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) <= (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger RankWithId(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) < (score)) || (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) < (id)))) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static BigInteger Rank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, DocsIndexModel._IMaybeDocId id)
    {
      DocsIndexModel._IMaybeDocId _source0 = id;
      {
        if (_source0.is_NoDoc) {
          return DocsIndexModel.__default.CountStrictLessScore(es, score);
        }
      }
      {
        BigInteger _0_doc = _source0.dtor_doc;
        return DocsIndexModel.__default.RankWithId(es, score, _0_doc);
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> InsertUnique(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)));
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.Concat(Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)), es));
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> RemoveOne(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, (es).Drop(BigInteger.One));
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger PositionAt(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger idx)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((idx).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if ((((es).Select((idx) - (BigInteger.One))).dtor_score) == (((es).Select(idx)).dtor_score)) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = es;
        BigInteger _in1 = (idx) - (BigInteger.One);
        es = _in0;
        idx = _in1;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static DocsIndexModel._IAtRank GetAtRank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger rank)
    {
      if ((rank) >= (new BigInteger((es).Count))) {
        return DocsIndexModel.AtRank.create_Missing();
      } else {
        return DocsIndexModel.AtRank.create_Found(((es).Select(rank)).dtor_score, ((es).Select(rank)).dtor_id, DocsIndexModel.__default.PositionAt(es, rank));
      }
    }
    public static Dafny.ISequence<BigInteger> CollectRange(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((es).Count)).Sign == 0) || ((limit).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) < (minScore)) {
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = minScore;
        BigInteger _in2 = maxScore;
        BigInteger _in3 = limit;
        es = _in0;
        minScore = _in1;
        maxScore = _in2;
        limit = _in3;
        goto TAIL_CALL_START;
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) > (maxScore)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((es).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<DocsIndexModel._IEntry> _in4 = (es).Drop(BigInteger.One);
        BigInteger _in5 = minScore;
        BigInteger _in6 = maxScore;
        BigInteger _in7 = (limit) - (BigInteger.One);
        es = _in4;
        minScore = _in5;
        maxScore = _in6;
        limit = _in7;
        goto TAIL_CALL_START;
      }
    }
  }

  public interface _IMaybeDocId {
    bool is_NoDoc { get; }
    bool is_SomeDoc { get; }
    BigInteger dtor_doc { get; }
    _IMaybeDocId DowncastClone();
  }
  public abstract class MaybeDocId : _IMaybeDocId {
    public MaybeDocId() {
    }
    private static readonly DocsIndexModel._IMaybeDocId theDefault = create_NoDoc();
    public static DocsIndexModel._IMaybeDocId Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId>(DocsIndexModel.MaybeDocId.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IMaybeDocId> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaybeDocId create_NoDoc() {
      return new MaybeDocId_NoDoc();
    }
    public static _IMaybeDocId create_SomeDoc(BigInteger doc) {
      return new MaybeDocId_SomeDoc(doc);
    }
    public bool is_NoDoc { get { return this is MaybeDocId_NoDoc; } }
    public bool is_SomeDoc { get { return this is MaybeDocId_SomeDoc; } }
    public BigInteger dtor_doc {
      get {
        var d = this;
        return ((MaybeDocId_SomeDoc)d)._doc;
      }
    }
    public abstract _IMaybeDocId DowncastClone();
  }
  public class MaybeDocId_NoDoc : MaybeDocId {
    public MaybeDocId_NoDoc() : base() {
    }
    public override _IMaybeDocId DowncastClone() {
      if (this is _IMaybeDocId dt) { return dt; }
      return new MaybeDocId_NoDoc();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.MaybeDocId_NoDoc;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.MaybeDocId.NoDoc";
      return s;
    }
  }
  public class MaybeDocId_SomeDoc : MaybeDocId {
    public readonly BigInteger _doc;
    public MaybeDocId_SomeDoc(BigInteger doc) : base() {
      this._doc = doc;
    }
    public override _IMaybeDocId DowncastClone() {
      if (this is _IMaybeDocId dt) { return dt; }
      return new MaybeDocId_SomeDoc(_doc);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.MaybeDocId_SomeDoc;
      return oth != null && this._doc == oth._doc;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._doc));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.MaybeDocId.SomeDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._doc);
      s += ")";
      return s;
    }
  }

  public interface _IAtRank {
    bool is_Missing { get; }
    bool is_Found { get; }
    BigInteger dtor_score { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_position { get; }
    _IAtRank DowncastClone();
  }
  public abstract class AtRank : _IAtRank {
    public AtRank() {
    }
    private static readonly DocsIndexModel._IAtRank theDefault = create_Missing();
    public static DocsIndexModel._IAtRank Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IAtRank> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IAtRank>(DocsIndexModel.AtRank.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IAtRank> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAtRank create_Missing() {
      return new AtRank_Missing();
    }
    public static _IAtRank create_Found(BigInteger score, BigInteger id, BigInteger position) {
      return new AtRank_Found(score, id, position);
    }
    public bool is_Missing { get { return this is AtRank_Missing; } }
    public bool is_Found { get { return this is AtRank_Found; } }
    public BigInteger dtor_score {
      get {
        var d = this;
        return ((AtRank_Found)d)._score;
      }
    }
    public BigInteger dtor_id {
      get {
        var d = this;
        return ((AtRank_Found)d)._id;
      }
    }
    public BigInteger dtor_position {
      get {
        var d = this;
        return ((AtRank_Found)d)._position;
      }
    }
    public abstract _IAtRank DowncastClone();
  }
  public class AtRank_Missing : AtRank {
    public AtRank_Missing() : base() {
    }
    public override _IAtRank DowncastClone() {
      if (this is _IAtRank dt) { return dt; }
      return new AtRank_Missing();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.AtRank_Missing;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.AtRank.Missing";
      return s;
    }
  }
  public class AtRank_Found : AtRank {
    public readonly BigInteger _score;
    public readonly BigInteger _id;
    public readonly BigInteger _position;
    public AtRank_Found(BigInteger score, BigInteger id, BigInteger position) : base() {
      this._score = score;
      this._id = id;
      this._position = position;
    }
    public override _IAtRank DowncastClone() {
      if (this is _IAtRank dt) { return dt; }
      return new AtRank_Found(_score, _id, _position);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.AtRank_Found;
      return oth != null && this._score == oth._score && this._id == oth._id && this._position == oth._position;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._score));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._position));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.AtRank.Found";
      s += "(";
      s += Dafny.Helpers.ToString(this._score);
      s += ", ";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._position);
      s += ")";
      return s;
    }
  }

  public interface _IEntry {
    bool is_Entry { get; }
    BigInteger dtor_score { get; }
    BigInteger dtor_id { get; }
    _IEntry DowncastClone();
  }
  public class Entry : _IEntry {
    public readonly BigInteger _score;
    public readonly BigInteger _id;
    public Entry(BigInteger score, BigInteger id) {
      this._score = score;
      this._id = id;
    }
    public _IEntry DowncastClone() {
      if (this is _IEntry dt) { return dt; }
      return new Entry(_score, _id);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexModel.Entry;
      return oth != null && this._score == oth._score && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._score));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexModel.Entry.Entry";
      s += "(";
      s += Dafny.Helpers.ToString(this._score);
      s += ", ";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
    private static readonly DocsIndexModel._IEntry theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static DocsIndexModel._IEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexModel._IEntry> _TYPE = new Dafny.TypeDescriptor<DocsIndexModel._IEntry>(DocsIndexModel.Entry.Default());
    public static Dafny.TypeDescriptor<DocsIndexModel._IEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEntry create(BigInteger score, BigInteger id) {
      return new Entry(score, id);
    }
    public static _IEntry create_Entry(BigInteger score, BigInteger id) {
      return create(score, id);
    }
    public bool is_Entry { get { return true; } }
    public BigInteger dtor_score {
      get {
        return this._score;
      }
    }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
  }
} // end of namespace DocsIndexModel
namespace DocsIndexTreap {

  public partial class __default {
    public static BigInteger NodeCount(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return BigInteger.Zero;
      } else {
        return ((BigInteger.One) + (DocsIndexTreap.__default.NodeCount((t).dtor_left))) + (DocsIndexTreap.__default.NodeCount((t).dtor_right));
      }
    }
    public static BigInteger Sum(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return BigInteger.Zero;
      } else {
        return (t).dtor_sum;
      }
    }
    public static BigInteger StructuralSum(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return BigInteger.Zero;
      } else {
        return ((new BigInteger(((t).dtor_ids).Count)) + (DocsIndexTreap.__default.StructuralSum((t).dtor_left))) + (DocsIndexTreap.__default.StructuralSum((t).dtor_right));
      }
    }
    public static bool SortedStrictIds(Dafny.ISequence<BigInteger> ids) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<BigInteger>, bool>>((_0_ids) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_0_ids).Count)), true, (((_forall_var_0) => {
        BigInteger _1_i = (BigInteger)_forall_var_0;
        return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_1_i) + (BigInteger.One), new BigInteger((_0_ids).Count)), true, (((_forall_var_1) => {
          BigInteger _2_j = (BigInteger)_forall_var_1;
          return !((((_1_i).Sign != -1) && ((_1_i) < (_2_j))) && ((_2_j) < (new BigInteger((_0_ids).Count)))) || (((_0_ids).Select(_1_i)) < ((_0_ids).Select(_2_j)));
        })));
      }))))(ids);
    }
    public static bool ScoreAboveLower(BigInteger score, DocsIndexTreap._IMaybeScore lo)
    {
      DocsIndexTreap._IMaybeScore _source0 = lo;
      {
        if (_source0.is_NoScore) {
          return true;
        }
      }
      {
        BigInteger _0_v = _source0.dtor_v;
        return (_0_v) < (score);
      }
    }
    public static bool ScoreBelowUpper(BigInteger score, DocsIndexTreap._IMaybeScore hi)
    {
      DocsIndexTreap._IMaybeScore _source0 = hi;
      {
        if (_source0.is_NoScore) {
          return true;
        }
      }
      {
        BigInteger _0_v = _source0.dtor_v;
        return (score) < (_0_v);
      }
    }
    public static BigInteger RootPrio(DocsIndexTreap._ITreap t) {
      if ((t).is_Node) {
        return (t).dtor_prio;
      } else {
        return BigInteger.Zero;
      }
    }
    public static bool SumConsistent(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return true;
      } else {
        return ((DocsIndexTreap.__default.SumConsistent((t).dtor_left)) && (DocsIndexTreap.__default.SumConsistent((t).dtor_right))) && (((t).dtor_sum) == (((new BigInteger(((t).dtor_ids).Count)) + (DocsIndexTreap.__default.Sum((t).dtor_left))) + (DocsIndexTreap.__default.Sum((t).dtor_right))));
      }
    }
    public static bool HeapOrdered(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return true;
      } else {
        return (((((((t).dtor_left).is_Node) ? ((((t).dtor_left).dtor_prio) <= ((t).dtor_prio)) : (true))) && (((((t).dtor_right).is_Node) ? ((((t).dtor_right).dtor_prio) <= ((t).dtor_prio)) : (true)))) && (DocsIndexTreap.__default.HeapOrdered((t).dtor_left))) && (DocsIndexTreap.__default.HeapOrdered((t).dtor_right));
      }
    }
    public static bool OrderedByScore(DocsIndexTreap._ITreap t, DocsIndexTreap._IMaybeScore lo, DocsIndexTreap._IMaybeScore hi)
    {
      if ((t).is_Empty) {
        return true;
      } else {
        return (((DocsIndexTreap.__default.ScoreAboveLower((t).dtor_score, lo)) && (DocsIndexTreap.__default.ScoreBelowUpper((t).dtor_score, hi))) && (DocsIndexTreap.__default.OrderedByScore((t).dtor_left, lo, DocsIndexTreap.MaybeScore.create_SomeScore((t).dtor_score)))) && (DocsIndexTreap.__default.OrderedByScore((t).dtor_right, DocsIndexTreap.MaybeScore.create_SomeScore((t).dtor_score), hi));
      }
    }
    public static bool IdsSortedInTree(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return true;
      } else {
        return ((DocsIndexTreap.__default.SortedStrictIds((t).dtor_ids)) && (DocsIndexTreap.__default.IdsSortedInTree((t).dtor_left))) && (DocsIndexTreap.__default.IdsSortedInTree((t).dtor_right));
      }
    }
    public static bool NonEmptyBuckets(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return true;
      } else {
        return (((new BigInteger(((t).dtor_ids).Count)).Sign == 1) && (DocsIndexTreap.__default.NonEmptyBuckets((t).dtor_left))) && (DocsIndexTreap.__default.NonEmptyBuckets((t).dtor_right));
      }
    }
    public static bool ValidTreap(DocsIndexTreap._ITreap t) {
      return ((((DocsIndexTreap.__default.SumConsistent(t)) && (DocsIndexTreap.__default.HeapOrdered(t))) && (DocsIndexTreap.__default.OrderedByScore(t, DocsIndexTreap.MaybeScore.create_NoScore(), DocsIndexTreap.MaybeScore.create_NoScore()))) && (DocsIndexTreap.__default.IdsSortedInTree(t))) && (DocsIndexTreap.__default.NonEmptyBuckets(t));
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> EntriesFromIds(BigInteger score, Dafny.ISequence<BigInteger> ids)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, (ids).Select(BigInteger.Zero))));
        BigInteger _in0 = score;
        Dafny.ISequence<BigInteger> _in1 = (ids).Drop(BigInteger.One);
        score = _in0;
        ids = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> Entries(DocsIndexTreap._ITreap t) {
      if ((t).is_Empty) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
      } else {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(Dafny.Sequence<DocsIndexModel._IEntry>.Concat(DocsIndexTreap.__default.Entries((t).dtor_left), DocsIndexTreap.__default.EntriesFromIds((t).dtor_score, (t).dtor_ids)), DocsIndexTreap.__default.Entries((t).dtor_right));
      }
    }
    public static Dafny.ISequence<BigInteger> InsertId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(id));
      } else if (((ids).Select(BigInteger.Zero)) == (id)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, ids);
      } else if ((id) < ((ids).Select(BigInteger.Zero))) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(id), ids));
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> RemoveId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, ids);
      } else if (((ids).Select(BigInteger.Zero)) == (id)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, (ids).Drop(BigInteger.One));
      } else if ((id) < ((ids).Select(BigInteger.Zero))) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, ids);
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger InsertionIndex(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if (((ids).Select(BigInteger.Zero)) < (id)) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static DocsIndexTreap._ITreap Pull(DocsIndexTreap._ITreap t) {
      return DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, ((new BigInteger(((t).dtor_ids).Count)) + (DocsIndexTreap.__default.Sum((t).dtor_left))) + (DocsIndexTreap.__default.Sum((t).dtor_right)), (t).dtor_left, (t).dtor_right);
    }
    public static DocsIndexTreap._ITreap RotateRight(DocsIndexTreap._ITreap t) {
      DocsIndexTreap._ITreap _0_demoted = DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, BigInteger.Zero, ((t).dtor_left).dtor_right, (t).dtor_right));
      return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node(((t).dtor_left).dtor_score, ((t).dtor_left).dtor_ids, ((t).dtor_left).dtor_prio, BigInteger.Zero, ((t).dtor_left).dtor_left, _0_demoted));
    }
    public static DocsIndexTreap._ITreap RotateLeft(DocsIndexTreap._ITreap t) {
      DocsIndexTreap._ITreap _0_demoted = DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, BigInteger.Zero, (t).dtor_left, ((t).dtor_right).dtor_left));
      return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node(((t).dtor_right).dtor_score, ((t).dtor_right).dtor_ids, ((t).dtor_right).dtor_prio, BigInteger.Zero, _0_demoted, ((t).dtor_right).dtor_right));
    }
    public static DocsIndexTreap._ITreap Join(DocsIndexTreap._ITreap left, DocsIndexTreap._ITreap right)
    {
      if ((left).is_Empty) {
        return right;
      } else if ((right).is_Empty) {
        return left;
      } else if (((left).dtor_prio) > ((right).dtor_prio)) {
        return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((left).dtor_score, (left).dtor_ids, (left).dtor_prio, BigInteger.Zero, (left).dtor_left, DocsIndexTreap.__default.Join((left).dtor_right, right)));
      } else {
        return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((right).dtor_score, (right).dtor_ids, (right).dtor_prio, BigInteger.Zero, DocsIndexTreap.__default.Join(left, (right).dtor_left), (right).dtor_right));
      }
    }
    public static DocsIndexTreap._ITreap Add(DocsIndexTreap._ITreap t, BigInteger score, BigInteger id, BigInteger prioForNew)
    {
      if ((t).is_Empty) {
        return DocsIndexTreap.Treap.create_Node(score, Dafny.Sequence<BigInteger>.FromElements(id), prioForNew, BigInteger.One, DocsIndexTreap.Treap.create_Empty(), DocsIndexTreap.Treap.create_Empty());
      } else if ((score) == ((t).dtor_score)) {
        return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, DocsIndexTreap.__default.InsertId((t).dtor_ids, id), (t).dtor_prio, BigInteger.Zero, (t).dtor_left, (t).dtor_right));
      } else if ((score) < ((t).dtor_score)) {
        DocsIndexTreap._ITreap _0_left2 = DocsIndexTreap.__default.Add((t).dtor_left, score, id, prioForNew);
        DocsIndexTreap._ITreap _1_n = DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, BigInteger.Zero, _0_left2, (t).dtor_right));
        if (((_0_left2).is_Node) && (((_0_left2).dtor_prio) > ((t).dtor_prio))) {
          return DocsIndexTreap.__default.RotateRight(_1_n);
        } else {
          return _1_n;
        }
      } else {
        DocsIndexTreap._ITreap _2_right2 = DocsIndexTreap.__default.Add((t).dtor_right, score, id, prioForNew);
        DocsIndexTreap._ITreap _3_n = DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, BigInteger.Zero, (t).dtor_left, _2_right2));
        if (((_2_right2).is_Node) && (((_2_right2).dtor_prio) > ((t).dtor_prio))) {
          return DocsIndexTreap.__default.RotateLeft(_3_n);
        } else {
          return _3_n;
        }
      }
    }
    public static DocsIndexTreap._ITreap Remove(DocsIndexTreap._ITreap t, BigInteger score, BigInteger id)
    {
      if ((t).is_Empty) {
        return DocsIndexTreap.Treap.create_Empty();
      } else if ((score) == ((t).dtor_score)) {
        Dafny.ISequence<BigInteger> _0_ids2 = DocsIndexTreap.__default.RemoveId((t).dtor_ids, id);
        if ((new BigInteger((_0_ids2).Count)) == (new BigInteger(((t).dtor_ids).Count))) {
          return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, BigInteger.Zero, (t).dtor_left, (t).dtor_right));
        } else if ((new BigInteger((_0_ids2).Count)).Sign == 0) {
          return DocsIndexTreap.__default.Join((t).dtor_left, (t).dtor_right);
        } else {
          return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, _0_ids2, (t).dtor_prio, BigInteger.Zero, (t).dtor_left, (t).dtor_right));
        }
      } else if ((score) < ((t).dtor_score)) {
        return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, BigInteger.Zero, DocsIndexTreap.__default.Remove((t).dtor_left, score, id), (t).dtor_right));
      } else {
        return DocsIndexTreap.__default.Pull(DocsIndexTreap.Treap.create_Node((t).dtor_score, (t).dtor_ids, (t).dtor_prio, BigInteger.Zero, (t).dtor_left, DocsIndexTreap.__default.Remove((t).dtor_right, score, id)));
      }
    }
    public static BigInteger TreapRank(DocsIndexTreap._ITreap t, BigInteger score, DocsIndexModel._IMaybeDocId id)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((t).is_Empty) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if ((score) < ((t).dtor_score)) {
        DocsIndexTreap._ITreap _in0 = (t).dtor_left;
        BigInteger _in1 = score;
        DocsIndexModel._IMaybeDocId _in2 = id;
        t = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else if ((score) > ((t).dtor_score)) {
        _0___accumulator = (_0___accumulator) + ((DocsIndexTreap.__default.Sum((t).dtor_left)) + (new BigInteger(((t).dtor_ids).Count)));
        DocsIndexTreap._ITreap _in3 = (t).dtor_right;
        BigInteger _in4 = score;
        DocsIndexModel._IMaybeDocId _in5 = id;
        t = _in3;
        score = _in4;
        id = _in5;
        goto TAIL_CALL_START;
      } else {
        return ((DocsIndexTreap.__default.Sum((t).dtor_left)) + (((System.Func<BigInteger>)(() => {
          DocsIndexModel._IMaybeDocId _source0 = id;
          {
            if (_source0.is_NoDoc) {
              return BigInteger.Zero;
            }
          }
          {
            BigInteger _1_doc = _source0.dtor_doc;
            return DocsIndexTreap.__default.InsertionIndex((t).dtor_ids, _1_doc);
          }
        }))())) + (_0___accumulator);
      }
    }
    public static BigInteger TreapCountAtMost(DocsIndexTreap._ITreap t, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((t).is_Empty) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if ((score) < ((t).dtor_score)) {
        DocsIndexTreap._ITreap _in0 = (t).dtor_left;
        BigInteger _in1 = score;
        t = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = (_0___accumulator) + ((DocsIndexTreap.__default.Sum((t).dtor_left)) + (new BigInteger(((t).dtor_ids).Count)));
        DocsIndexTreap._ITreap _in2 = (t).dtor_right;
        BigInteger _in3 = score;
        t = _in2;
        score = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static DocsIndexModel._IAtRank TreapGetAtRank(DocsIndexTreap._ITreap t, BigInteger rank)
    {
    TAIL_CALL_START: ;
      if ((t).is_Empty) {
        return DocsIndexModel.AtRank.create_Missing();
      } else if ((rank) < (DocsIndexTreap.__default.Sum((t).dtor_left))) {
        DocsIndexTreap._ITreap _in0 = (t).dtor_left;
        BigInteger _in1 = rank;
        t = _in0;
        rank = _in1;
        goto TAIL_CALL_START;
      } else if ((rank) < ((DocsIndexTreap.__default.Sum((t).dtor_left)) + (new BigInteger(((t).dtor_ids).Count)))) {
        BigInteger _0_pos = (rank) - (DocsIndexTreap.__default.Sum((t).dtor_left));
        return DocsIndexModel.AtRank.create_Found((t).dtor_score, ((t).dtor_ids).Select(_0_pos), _0_pos);
      } else {
        DocsIndexTreap._ITreap _in2 = (t).dtor_right;
        BigInteger _in3 = (rank) - ((DocsIndexTreap.__default.Sum((t).dtor_left)) + (new BigInteger(((t).dtor_ids).Count)));
        t = _in2;
        rank = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> TakePrefix<__T>(Dafny.ISequence<__T> xs, BigInteger limit)
    {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((xs).Count)).Sign == 0) || ((limit).Sign == 0)) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in0 = (xs).Drop(BigInteger.One);
        BigInteger _in1 = (limit) - (BigInteger.One);
        xs = _in0;
        limit = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger SatSub(BigInteger a, BigInteger b)
    {
      if ((b) <= (a)) {
        return (a) - (b);
      } else {
        return BigInteger.Zero;
      }
    }
    public static Dafny.ISequence<BigInteger> TreapCollectRange(DocsIndexTreap._ITreap t, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      if (((t).is_Empty) || ((limit).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else {
        Dafny.ISequence<BigInteger> _0_leftOut = (((minScore) < ((t).dtor_score)) ? (DocsIndexTreap.__default.TreapCollectRange((t).dtor_left, minScore, maxScore, limit)) : (Dafny.Sequence<BigInteger>.FromElements()));
        BigInteger _1_rem1 = DocsIndexTreap.__default.SatSub(limit, new BigInteger((_0_leftOut).Count));
        if ((_1_rem1).Sign == 0) {
          return _0_leftOut;
        } else {
          Dafny.ISequence<BigInteger> _2_selfOut = (((((t).dtor_score) >= (minScore)) && (((t).dtor_score) <= (maxScore))) ? (DocsIndexTreap.__default.TakePrefix<BigInteger>((t).dtor_ids, _1_rem1)) : (Dafny.Sequence<BigInteger>.FromElements()));
          BigInteger _3_rem2 = DocsIndexTreap.__default.SatSub(_1_rem1, new BigInteger((_2_selfOut).Count));
          if ((_3_rem2).Sign == 0) {
            return Dafny.Sequence<BigInteger>.Concat(_0_leftOut, _2_selfOut);
          } else {
            Dafny.ISequence<BigInteger> _4_rightOut = ((((t).dtor_score) < (maxScore)) ? (DocsIndexTreap.__default.TreapCollectRange((t).dtor_right, minScore, maxScore, _3_rem2)) : (Dafny.Sequence<BigInteger>.FromElements()));
            return Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.Concat(_0_leftOut, _2_selfOut), _4_rightOut);
          }
        }
      }
    }
    public static BigInteger ModelRankOnEntries(DocsIndexTreap._ITreap t, BigInteger score, DocsIndexModel._IMaybeDocId id)
    {
      return DocsIndexModel.__default.Rank(DocsIndexTreap.__default.Entries(t), score, id);
    }
    public static BigInteger ModelCountAtMostOnEntries(DocsIndexTreap._ITreap t, BigInteger score)
    {
      return DocsIndexModel.__default.CountAtMost(DocsIndexTreap.__default.Entries(t), score);
    }
    public static DocsIndexModel._IAtRank ModelGetAtRankOnEntries(DocsIndexTreap._ITreap t, BigInteger rank)
    {
      return DocsIndexModel.__default.GetAtRank(DocsIndexTreap.__default.Entries(t), rank);
    }
    public static Dafny.ISequence<BigInteger> ModelCollectRangeOnEntries(DocsIndexTreap._ITreap t, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      return DocsIndexModel.__default.CollectRange(DocsIndexTreap.__default.Entries(t), minScore, maxScore, limit);
    }
    public static bool AllScoresLt(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      if ((new BigInteger((es).Count)).Sign == 0) {
        return true;
      } else {
        return ((((es).Select(BigInteger.Zero)).dtor_score) < (score)) && (DocsIndexTreap.__default.AllScoresLt((es).Drop(BigInteger.One), score));
      }
    }
    public static bool AllScoresLe(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      if ((new BigInteger((es).Count)).Sign == 0) {
        return true;
      } else {
        return ((((es).Select(BigInteger.Zero)).dtor_score) <= (score)) && (DocsIndexTreap.__default.AllScoresLe((es).Drop(BigInteger.One), score));
      }
    }
    public static bool AllScoresGt(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      if ((new BigInteger((es).Count)).Sign == 0) {
        return true;
      } else {
        return ((((es).Select(BigInteger.Zero)).dtor_score) > (score)) && (DocsIndexTreap.__default.AllScoresGt((es).Drop(BigInteger.One), score));
      }
    }
  }

  public interface _IMaybeScore {
    bool is_NoScore { get; }
    bool is_SomeScore { get; }
    BigInteger dtor_v { get; }
    _IMaybeScore DowncastClone();
  }
  public abstract class MaybeScore : _IMaybeScore {
    public MaybeScore() {
    }
    private static readonly DocsIndexTreap._IMaybeScore theDefault = create_NoScore();
    public static DocsIndexTreap._IMaybeScore Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexTreap._IMaybeScore> _TYPE = new Dafny.TypeDescriptor<DocsIndexTreap._IMaybeScore>(DocsIndexTreap.MaybeScore.Default());
    public static Dafny.TypeDescriptor<DocsIndexTreap._IMaybeScore> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaybeScore create_NoScore() {
      return new MaybeScore_NoScore();
    }
    public static _IMaybeScore create_SomeScore(BigInteger v) {
      return new MaybeScore_SomeScore(v);
    }
    public bool is_NoScore { get { return this is MaybeScore_NoScore; } }
    public bool is_SomeScore { get { return this is MaybeScore_SomeScore; } }
    public BigInteger dtor_v {
      get {
        var d = this;
        return ((MaybeScore_SomeScore)d)._v;
      }
    }
    public abstract _IMaybeScore DowncastClone();
  }
  public class MaybeScore_NoScore : MaybeScore {
    public MaybeScore_NoScore() : base() {
    }
    public override _IMaybeScore DowncastClone() {
      if (this is _IMaybeScore dt) { return dt; }
      return new MaybeScore_NoScore();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexTreap.MaybeScore_NoScore;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexTreap.MaybeScore.NoScore";
      return s;
    }
  }
  public class MaybeScore_SomeScore : MaybeScore {
    public readonly BigInteger _v;
    public MaybeScore_SomeScore(BigInteger v) : base() {
      this._v = v;
    }
    public override _IMaybeScore DowncastClone() {
      if (this is _IMaybeScore dt) { return dt; }
      return new MaybeScore_SomeScore(_v);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexTreap.MaybeScore_SomeScore;
      return oth != null && this._v == oth._v;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexTreap.MaybeScore.SomeScore";
      s += "(";
      s += Dafny.Helpers.ToString(this._v);
      s += ")";
      return s;
    }
  }

  public interface _ITreap {
    bool is_Empty { get; }
    bool is_Node { get; }
    BigInteger dtor_score { get; }
    Dafny.ISequence<BigInteger> dtor_ids { get; }
    BigInteger dtor_prio { get; }
    BigInteger dtor_sum { get; }
    DocsIndexTreap._ITreap dtor_left { get; }
    DocsIndexTreap._ITreap dtor_right { get; }
    _ITreap DowncastClone();
  }
  public abstract class Treap : _ITreap {
    public Treap() {
    }
    private static readonly DocsIndexTreap._ITreap theDefault = create_Empty();
    public static DocsIndexTreap._ITreap Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DocsIndexTreap._ITreap> _TYPE = new Dafny.TypeDescriptor<DocsIndexTreap._ITreap>(DocsIndexTreap.Treap.Default());
    public static Dafny.TypeDescriptor<DocsIndexTreap._ITreap> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITreap create_Empty() {
      return new Treap_Empty();
    }
    public static _ITreap create_Node(BigInteger score, Dafny.ISequence<BigInteger> ids, BigInteger prio, BigInteger sum, DocsIndexTreap._ITreap left, DocsIndexTreap._ITreap right) {
      return new Treap_Node(score, ids, prio, sum, left, right);
    }
    public bool is_Empty { get { return this is Treap_Empty; } }
    public bool is_Node { get { return this is Treap_Node; } }
    public BigInteger dtor_score {
      get {
        var d = this;
        return ((Treap_Node)d)._score;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_ids {
      get {
        var d = this;
        return ((Treap_Node)d)._ids;
      }
    }
    public BigInteger dtor_prio {
      get {
        var d = this;
        return ((Treap_Node)d)._prio;
      }
    }
    public BigInteger dtor_sum {
      get {
        var d = this;
        return ((Treap_Node)d)._sum;
      }
    }
    public DocsIndexTreap._ITreap dtor_left {
      get {
        var d = this;
        return ((Treap_Node)d)._left;
      }
    }
    public DocsIndexTreap._ITreap dtor_right {
      get {
        var d = this;
        return ((Treap_Node)d)._right;
      }
    }
    public abstract _ITreap DowncastClone();
  }
  public class Treap_Empty : Treap {
    public Treap_Empty() : base() {
    }
    public override _ITreap DowncastClone() {
      if (this is _ITreap dt) { return dt; }
      return new Treap_Empty();
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexTreap.Treap_Empty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexTreap.Treap.Empty";
      return s;
    }
  }
  public class Treap_Node : Treap {
    public readonly BigInteger _score;
    public readonly Dafny.ISequence<BigInteger> _ids;
    public readonly BigInteger _prio;
    public readonly BigInteger _sum;
    public readonly DocsIndexTreap._ITreap _left;
    public readonly DocsIndexTreap._ITreap _right;
    public Treap_Node(BigInteger score, Dafny.ISequence<BigInteger> ids, BigInteger prio, BigInteger sum, DocsIndexTreap._ITreap left, DocsIndexTreap._ITreap right) : base() {
      this._score = score;
      this._ids = ids;
      this._prio = prio;
      this._sum = sum;
      this._left = left;
      this._right = right;
    }
    public override _ITreap DowncastClone() {
      if (this is _ITreap dt) { return dt; }
      return new Treap_Node(_score, _ids, _prio, _sum, _left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as DocsIndexTreap.Treap_Node;
      return oth != null && this._score == oth._score && object.Equals(this._ids, oth._ids) && this._prio == oth._prio && this._sum == oth._sum && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._score));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ids));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._prio));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._sum));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DocsIndexTreap.Treap.Node";
      s += "(";
      s += Dafny.Helpers.ToString(this._score);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ids);
      s += ", ";
      s += Dafny.Helpers.ToString(this._prio);
      s += ", ";
      s += Dafny.Helpers.ToString(this._sum);
      s += ", ";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
} // end of namespace DocsIndexTreap
namespace DocsIndexBench {

  public partial class __default {
    public static BigInteger NextState(BigInteger state) {
      BigInteger _0_next = Dafny.Helpers.EuclideanModulus((state) * (DocsIndexBench.__default.Multiplier), DocsIndexBench.__default.Modulus);
      if ((_0_next).Sign == 0) {
        return BigInteger.One;
      } else {
        return _0_next;
      }
    }
    public static void NextRand(BigInteger state, BigInteger bound, out BigInteger next, out BigInteger @value)
    {
      next = BigInteger.Zero;
      @value = BigInteger.Zero;
      next = DocsIndexBench.__default.NextState(state);
      @value = Dafny.Helpers.EuclideanModulus(next, bound);
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> RefInsertUnique(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)));
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.Concat(Dafny.Sequence<DocsIndexModel._IEntry>.FromElements(DocsIndexModel.Entry.create(score, id)), es));
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> RefRemoveOne(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      Dafny.ISequence<DocsIndexModel._IEntry> _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) == (id))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, (es).Drop(BigInteger.One));
      } else if (((score) < (((es).Select(BigInteger.Zero)).dtor_score)) || (((score) == (((es).Select(BigInteger.Zero)).dtor_score)) && ((id) < (((es).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, es);
      } else {
        _0___accumulator = Dafny.Sequence<DocsIndexModel._IEntry>.Concat(_0___accumulator, Dafny.Sequence<DocsIndexModel._IEntry>.FromElements((es).Select(BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger RefCountStrictLess(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) < (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger RefCountAtMost(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((((((es).Select(BigInteger.Zero)).dtor_score) <= (score)) ? (BigInteger.One) : (BigInteger.Zero)));
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        es = _in0;
        score = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger RefRankWithId(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((es).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if (((((es).Select(BigInteger.Zero)).dtor_score) < (score)) || (((((es).Select(BigInteger.Zero)).dtor_score) == (score)) && ((((es).Select(BigInteger.Zero)).dtor_id) < (id)))) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = score;
        BigInteger _in2 = id;
        es = _in0;
        score = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static BigInteger RefRank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, DocsIndexModel._IMaybeDocId id)
    {
      DocsIndexModel._IMaybeDocId _source0 = id;
      {
        if (_source0.is_NoDoc) {
          return DocsIndexBench.__default.RefCountStrictLess(es, score);
        }
      }
      {
        BigInteger _0_doc = _source0.dtor_doc;
        return DocsIndexBench.__default.RefRankWithId(es, score, _0_doc);
      }
    }
    public static BigInteger RefPositionAt(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger idx)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((idx).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else if ((((es).Select((idx) - (BigInteger.One))).dtor_score) == (((es).Select(idx)).dtor_score)) {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = es;
        BigInteger _in1 = (idx) - (BigInteger.One);
        es = _in0;
        idx = _in1;
        goto TAIL_CALL_START;
      } else {
        return (BigInteger.Zero) + (_0___accumulator);
      }
    }
    public static DocsIndexModel._IAtRank RefGetAtRank(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger rank)
    {
      if ((rank) >= (new BigInteger((es).Count))) {
        return DocsIndexModel.AtRank.create_Missing();
      } else {
        return DocsIndexModel.AtRank.create_Found(((es).Select(rank)).dtor_score, ((es).Select(rank)).dtor_id, DocsIndexBench.__default.RefPositionAt(es, rank));
      }
    }
    public static Dafny.ISequence<BigInteger> RefCollectRange(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger minScore, BigInteger maxScore, BigInteger limit)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((es).Count)).Sign == 0) || ((limit).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) < (minScore)) {
        Dafny.ISequence<DocsIndexModel._IEntry> _in0 = (es).Drop(BigInteger.One);
        BigInteger _in1 = minScore;
        BigInteger _in2 = maxScore;
        BigInteger _in3 = limit;
        es = _in0;
        minScore = _in1;
        maxScore = _in2;
        limit = _in3;
        goto TAIL_CALL_START;
      } else if ((((es).Select(BigInteger.Zero)).dtor_score) > (maxScore)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((es).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<DocsIndexModel._IEntry> _in4 = (es).Drop(BigInteger.One);
        BigInteger _in5 = minScore;
        BigInteger _in6 = maxScore;
        BigInteger _in7 = (limit) - (BigInteger.One);
        es = _in4;
        minScore = _in5;
        maxScore = _in6;
        limit = _in7;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> RemoveAt<__T>(Dafny.ISequence<__T> xs, BigInteger idx)
    {
      Dafny.ISequence<__T> _0___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((idx).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_0___accumulator, (xs).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<__T>.Concat(_0___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in0 = (xs).Drop(BigInteger.One);
        BigInteger _in1 = (idx) - (BigInteger.One);
        xs = _in0;
        idx = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static void CheckState(Dafny.ISequence<Dafny.Rune> name, BigInteger opIndex, DocsIndexTreap._ITreap t, Dafny.ISequence<DocsIndexModel._IEntry> @ref, BigInteger rng, BigInteger scoreRange, BigInteger nextId, out bool ok, out BigInteger nextRng)
    {
      ok = false;
      nextRng = BigInteger.Zero;
      ok = false;
      nextRng = rng;
      if (!(DocsIndexTreap.__default.ValidTreap(t))) {
        Dafny.Helpers.Print((name).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": invalid treap at op ")).ToVerbatimString(false));
        Dafny.Helpers.Print((opIndex));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        return ;
      }
      if (!(DocsIndexTreap.__default.Entries(t)).Equals(@ref)) {
        Dafny.Helpers.Print((name).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": entries mismatch at op ")).ToVerbatimString(false));
        Dafny.Helpers.Print((opIndex));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  treap size=")).ToVerbatimString(false));
        Dafny.Helpers.Print((new BigInteger((DocsIndexTreap.__default.Entries(t)).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ref size=")).ToVerbatimString(false));
        Dafny.Helpers.Print((new BigInteger((@ref).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        return ;
      }
      BigInteger _0_scoreSel = BigInteger.Zero;
      BigInteger _out0;
      BigInteger _out1;
      DocsIndexBench.__default.NextRand(nextRng, scoreRange, out _out0, out _out1);
      nextRng = _out0;
      _0_scoreSel = _out1;
      BigInteger _1_score;
      _1_score = _0_scoreSel;
      if ((DocsIndexTreap.__default.TreapRank(t, _1_score, DocsIndexModel.MaybeDocId.create_NoDoc())) != (DocsIndexBench.__default.RefRank(@ref, _1_score, DocsIndexModel.MaybeDocId.create_NoDoc()))) {
        Dafny.Helpers.Print((name).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": rank(score,null) mismatch at op ")).ToVerbatimString(false));
        Dafny.Helpers.Print((opIndex));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" score=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_1_score));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  treap=")).ToVerbatimString(false));
        Dafny.Helpers.Print((DocsIndexTreap.__default.TreapRank(t, _1_score, DocsIndexModel.MaybeDocId.create_NoDoc())));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ref=")).ToVerbatimString(false));
        Dafny.Helpers.Print((DocsIndexBench.__default.RefRank(@ref, _1_score, DocsIndexModel.MaybeDocId.create_NoDoc())));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        return ;
      }
      BigInteger _2_doc = BigInteger.Zero;
      if ((new BigInteger((@ref).Count)).Sign == 0) {
        _2_doc = nextId;
      } else {
        BigInteger _3_pick = BigInteger.Zero;
        BigInteger _out2;
        BigInteger _out3;
        DocsIndexBench.__default.NextRand(nextRng, new BigInteger((@ref).Count), out _out2, out _out3);
        nextRng = _out2;
        _3_pick = _out3;
        _2_doc = ((@ref).Select(_3_pick)).dtor_id;
      }
      if ((DocsIndexTreap.__default.TreapRank(t, _1_score, DocsIndexModel.MaybeDocId.create_SomeDoc(_2_doc))) != (DocsIndexBench.__default.RefRank(@ref, _1_score, DocsIndexModel.MaybeDocId.create_SomeDoc(_2_doc)))) {
        Dafny.Helpers.Print((name).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": rank(score,id) mismatch at op ")).ToVerbatimString(false));
        Dafny.Helpers.Print((opIndex));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" score=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_1_score));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" doc=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_2_doc));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  treap=")).ToVerbatimString(false));
        Dafny.Helpers.Print((DocsIndexTreap.__default.TreapRank(t, _1_score, DocsIndexModel.MaybeDocId.create_SomeDoc(_2_doc))));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ref=")).ToVerbatimString(false));
        Dafny.Helpers.Print((DocsIndexBench.__default.RefRank(@ref, _1_score, DocsIndexModel.MaybeDocId.create_SomeDoc(_2_doc))));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        return ;
      }
      if ((DocsIndexTreap.__default.TreapCountAtMost(t, _1_score)) != (DocsIndexBench.__default.RefCountAtMost(@ref, _1_score))) {
        Dafny.Helpers.Print((name).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": countAtMost mismatch at op ")).ToVerbatimString(false));
        Dafny.Helpers.Print((opIndex));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" score=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_1_score));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  treap=")).ToVerbatimString(false));
        Dafny.Helpers.Print((DocsIndexTreap.__default.TreapCountAtMost(t, _1_score)));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ref=")).ToVerbatimString(false));
        Dafny.Helpers.Print((DocsIndexBench.__default.RefCountAtMost(@ref, _1_score)));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        return ;
      }
      BigInteger _4_rankBound;
      _4_rankBound = (new BigInteger((@ref).Count)) + (new BigInteger(3));
      BigInteger _5_rankPick = BigInteger.Zero;
      BigInteger _out4;
      BigInteger _out5;
      DocsIndexBench.__default.NextRand(nextRng, _4_rankBound, out _out4, out _out5);
      nextRng = _out4;
      _5_rankPick = _out5;
      if (!object.Equals(DocsIndexTreap.__default.TreapGetAtRank(t, _5_rankPick), DocsIndexBench.__default.RefGetAtRank(@ref, _5_rankPick))) {
        Dafny.Helpers.Print((name).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": getAtRank mismatch at op ")).ToVerbatimString(false));
        Dafny.Helpers.Print((opIndex));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" rank=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_5_rankPick));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  treap kind/value mismatch against reference\n")).ToVerbatimString(false));
        return ;
      }
      BigInteger _6_minSel = BigInteger.Zero;
      BigInteger _7_widthSel = BigInteger.Zero;
      BigInteger _8_limitSel = BigInteger.Zero;
      BigInteger _out6;
      BigInteger _out7;
      DocsIndexBench.__default.NextRand(nextRng, scoreRange, out _out6, out _out7);
      nextRng = _out6;
      _6_minSel = _out7;
      BigInteger _out8;
      BigInteger _out9;
      DocsIndexBench.__default.NextRand(nextRng, scoreRange, out _out8, out _out9);
      nextRng = _out8;
      _7_widthSel = _out9;
      BigInteger _out10;
      BigInteger _out11;
      DocsIndexBench.__default.NextRand(nextRng, new BigInteger(16), out _out10, out _out11);
      nextRng = _out10;
      _8_limitSel = _out11;
      BigInteger _9_minScore;
      _9_minScore = _6_minSel;
      BigInteger _10_maxScore;
      _10_maxScore = (_9_minScore) + (_7_widthSel);
      BigInteger _11_limit;
      _11_limit = (_8_limitSel) + (BigInteger.One);
      if (!(DocsIndexTreap.__default.TreapCollectRange(t, _9_minScore, _10_maxScore, _11_limit)).Equals(DocsIndexBench.__default.RefCollectRange(@ref, _9_minScore, _10_maxScore, _11_limit))) {
        Dafny.Helpers.Print((name).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": collectRange mismatch at op ")).ToVerbatimString(false));
        Dafny.Helpers.Print((opIndex));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" min=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_9_minScore));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" max=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_10_maxScore));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" limit=")).ToVerbatimString(false));
        Dafny.Helpers.Print((_11_limit));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  treap size=")).ToVerbatimString(false));
        Dafny.Helpers.Print((new BigInteger((DocsIndexTreap.__default.TreapCollectRange(t, _9_minScore, _10_maxScore, _11_limit)).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ref size=")).ToVerbatimString(false));
        Dafny.Helpers.Print((new BigInteger((DocsIndexBench.__default.RefCollectRange(@ref, _9_minScore, _10_maxScore, _11_limit)).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        return ;
      }
      ok = true;
    }
    public static bool RunScenario(Dafny.ISequence<Dafny.Rune> name, BigInteger documents, BigInteger ticks, BigInteger updatesPerTick, BigInteger insertsPerTick, BigInteger deletesPerTick, BigInteger scoreRange, BigInteger checksEveryOps)
    {
      bool ok = false;
      DocsIndexTreap._ITreap _0_t;
      _0_t = DocsIndexTreap.Treap.create_Empty();
      Dafny.ISequence<DocsIndexModel._IEntry> _1_ref;
      _1_ref = Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
      BigInteger _2_rng;
      _2_rng = new BigInteger(42);
      BigInteger _3_nextId;
      _3_nextId = BigInteger.Zero;
      BigInteger _4_opIndex;
      _4_opIndex = BigInteger.Zero;
      ok = false;
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[dafny-bench] scenario=")).ToVerbatimString(false));
      Dafny.Helpers.Print((name).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" docs=")).ToVerbatimString(false));
      Dafny.Helpers.Print((documents));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ticks=")).ToVerbatimString(false));
      Dafny.Helpers.Print((ticks));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" updates/tick=")).ToVerbatimString(false));
      Dafny.Helpers.Print((updatesPerTick));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" inserts/tick=")).ToVerbatimString(false));
      Dafny.Helpers.Print((insertsPerTick));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" deletes/tick=")).ToVerbatimString(false));
      Dafny.Helpers.Print((deletesPerTick));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" scoreRange=")).ToVerbatimString(false));
      Dafny.Helpers.Print((scoreRange));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" checksEveryOps=")).ToVerbatimString(false));
      Dafny.Helpers.Print((checksEveryOps));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
      BigInteger _5_i;
      _5_i = BigInteger.Zero;
      while ((_5_i) < (documents)) {
        BigInteger _6_scoreSel = BigInteger.Zero;
        BigInteger _out0;
        BigInteger _out1;
        DocsIndexBench.__default.NextRand(_2_rng, scoreRange, out _out0, out _out1);
        _2_rng = _out0;
        _6_scoreSel = _out1;
        BigInteger _7_score;
        _7_score = _6_scoreSel;
        BigInteger _8_prioSel = BigInteger.Zero;
        BigInteger _out2;
        BigInteger _out3;
        DocsIndexBench.__default.NextRand(_2_rng, new BigInteger(1000000), out _out2, out _out3);
        _2_rng = _out2;
        _8_prioSel = _out3;
        _0_t = DocsIndexTreap.__default.Add(_0_t, _7_score, _3_nextId, _8_prioSel);
        _1_ref = DocsIndexBench.__default.RefInsertUnique(_1_ref, _7_score, _3_nextId);
        _3_nextId = (_3_nextId) + (BigInteger.One);
        _4_opIndex = (_4_opIndex) + (BigInteger.One);
        _5_i = (_5_i) + (BigInteger.One);
      }
      bool _9_seededOk = false;
      bool _out4;
      BigInteger _out5;
      DocsIndexBench.__default.CheckState(Dafny.Sequence<Dafny.Rune>.Concat(name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" seed")), _4_opIndex, _0_t, _1_ref, _2_rng, scoreRange, _3_nextId, out _out4, out _out5);
      _9_seededOk = _out4;
      _2_rng = _out5;
      if (!(_9_seededOk)) {
        return ok;
      }
      BigInteger _10_tick;
      _10_tick = BigInteger.Zero;
      while ((_10_tick) < (ticks)) {
        BigInteger _11_u;
        _11_u = BigInteger.Zero;
        while ((_11_u) < (updatesPerTick)) {
          if ((new BigInteger((_1_ref).Count)).Sign == 1) {
            BigInteger _12_pick = BigInteger.Zero;
            BigInteger _out6;
            BigInteger _out7;
            DocsIndexBench.__default.NextRand(_2_rng, new BigInteger((_1_ref).Count), out _out6, out _out7);
            _2_rng = _out6;
            _12_pick = _out7;
            DocsIndexModel._IEntry _13_chosen;
            _13_chosen = (_1_ref).Select(_12_pick);
            BigInteger _14_newScoreSel = BigInteger.Zero;
            BigInteger _out8;
            BigInteger _out9;
            DocsIndexBench.__default.NextRand(_2_rng, scoreRange, out _out8, out _out9);
            _2_rng = _out8;
            _14_newScoreSel = _out9;
            BigInteger _15_newScore;
            _15_newScore = _14_newScoreSel;
            BigInteger _16_prioSel = BigInteger.Zero;
            BigInteger _out10;
            BigInteger _out11;
            DocsIndexBench.__default.NextRand(_2_rng, new BigInteger(1000000), out _out10, out _out11);
            _2_rng = _out10;
            _16_prioSel = _out11;
            _0_t = DocsIndexTreap.__default.Remove(_0_t, (_13_chosen).dtor_score, (_13_chosen).dtor_id);
            _1_ref = DocsIndexBench.__default.RefRemoveOne(_1_ref, (_13_chosen).dtor_score, (_13_chosen).dtor_id);
            _0_t = DocsIndexTreap.__default.Add(_0_t, _15_newScore, (_13_chosen).dtor_id, _16_prioSel);
            _1_ref = DocsIndexBench.__default.RefInsertUnique(_1_ref, _15_newScore, (_13_chosen).dtor_id);
            _4_opIndex = (_4_opIndex) + (BigInteger.One);
            if ((Dafny.Helpers.EuclideanModulus(_4_opIndex, checksEveryOps)).Sign == 0) {
              bool _17_stepOk = false;
              bool _out12;
              BigInteger _out13;
              DocsIndexBench.__default.CheckState(name, _4_opIndex, _0_t, _1_ref, _2_rng, scoreRange, _3_nextId, out _out12, out _out13);
              _17_stepOk = _out12;
              _2_rng = _out13;
              if (!(_17_stepOk)) {
                return ok;
              }
            }
          }
          _11_u = (_11_u) + (BigInteger.One);
        }
        BigInteger _18_ins;
        _18_ins = BigInteger.Zero;
        while ((_18_ins) < (insertsPerTick)) {
          BigInteger _19_scoreSel = BigInteger.Zero;
          BigInteger _out14;
          BigInteger _out15;
          DocsIndexBench.__default.NextRand(_2_rng, scoreRange, out _out14, out _out15);
          _2_rng = _out14;
          _19_scoreSel = _out15;
          BigInteger _20_prioSel = BigInteger.Zero;
          BigInteger _out16;
          BigInteger _out17;
          DocsIndexBench.__default.NextRand(_2_rng, new BigInteger(1000000), out _out16, out _out17);
          _2_rng = _out16;
          _20_prioSel = _out17;
          BigInteger _21_score;
          _21_score = _19_scoreSel;
          _0_t = DocsIndexTreap.__default.Add(_0_t, _21_score, _3_nextId, _20_prioSel);
          _1_ref = DocsIndexBench.__default.RefInsertUnique(_1_ref, _21_score, _3_nextId);
          _3_nextId = (_3_nextId) + (BigInteger.One);
          _4_opIndex = (_4_opIndex) + (BigInteger.One);
          if ((Dafny.Helpers.EuclideanModulus(_4_opIndex, checksEveryOps)).Sign == 0) {
            bool _22_insOk = false;
            bool _out18;
            BigInteger _out19;
            DocsIndexBench.__default.CheckState(name, _4_opIndex, _0_t, _1_ref, _2_rng, scoreRange, _3_nextId, out _out18, out _out19);
            _22_insOk = _out18;
            _2_rng = _out19;
            if (!(_22_insOk)) {
              return ok;
            }
          }
          _18_ins = (_18_ins) + (BigInteger.One);
        }
        BigInteger _23_del;
        _23_del = BigInteger.Zero;
        while ((_23_del) < (deletesPerTick)) {
          if ((new BigInteger((_1_ref).Count)).Sign == 1) {
            BigInteger _24_pick = BigInteger.Zero;
            BigInteger _out20;
            BigInteger _out21;
            DocsIndexBench.__default.NextRand(_2_rng, new BigInteger((_1_ref).Count), out _out20, out _out21);
            _2_rng = _out20;
            _24_pick = _out21;
            DocsIndexModel._IEntry _25_chosen;
            _25_chosen = (_1_ref).Select(_24_pick);
            _0_t = DocsIndexTreap.__default.Remove(_0_t, (_25_chosen).dtor_score, (_25_chosen).dtor_id);
            _1_ref = DocsIndexBench.__default.RefRemoveOne(_1_ref, (_25_chosen).dtor_score, (_25_chosen).dtor_id);
            _4_opIndex = (_4_opIndex) + (BigInteger.One);
            if ((Dafny.Helpers.EuclideanModulus(_4_opIndex, checksEveryOps)).Sign == 0) {
              bool _26_delOk = false;
              bool _out22;
              BigInteger _out23;
              DocsIndexBench.__default.CheckState(name, _4_opIndex, _0_t, _1_ref, _2_rng, scoreRange, _3_nextId, out _out22, out _out23);
              _26_delOk = _out22;
              _2_rng = _out23;
              if (!(_26_delOk)) {
                return ok;
              }
            }
          }
          _23_del = (_23_del) + (BigInteger.One);
        }
        _10_tick = (_10_tick) + (BigInteger.One);
      }
      bool _27_finalOk = false;
      bool _out24;
      BigInteger _out25;
      DocsIndexBench.__default.CheckState(Dafny.Sequence<Dafny.Rune>.Concat(name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" final")), _4_opIndex, _0_t, _1_ref, _2_rng, scoreRange, _3_nextId, out _out24, out _out25);
      _27_finalOk = _out24;
      _2_rng = _out25;
      if (!(_27_finalOk)) {
        return ok;
      }
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[dafny-bench] passed scenario=")).ToVerbatimString(false));
      Dafny.Helpers.Print((name).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" totalOps=")).ToVerbatimString(false));
      Dafny.Helpers.Print((_4_opIndex));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" finalEntries=")).ToVerbatimString(false));
      Dafny.Helpers.Print((new BigInteger((_1_ref).Count)));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
      ok = true;
      return ok;
    }
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      bool _0_ok;
      bool _out0;
      _out0 = DocsIndexBench.__default.RunScenario(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("correctness-small"), new BigInteger(400), new BigInteger(40), new BigInteger(20), new BigInteger(4), new BigInteger(4), new BigInteger(1000), BigInteger.One);
      _0_ok = _out0;
      if (!(_0_ok)) {
        return ;
      }
      bool _out1;
      _out1 = DocsIndexBench.__default.RunScenario(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("benchmark-like"), new BigInteger(2500), new BigInteger(120), new BigInteger(125), new BigInteger(25), new BigInteger(25), new BigInteger(2500), new BigInteger(200));
      _0_ok = _out1;
      if (!(_0_ok)) {
        return ;
      }
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[dafny-bench] all scenarios passed\n")).ToVerbatimString(false));
    }
    public static BigInteger Modulus { get {
      return new BigInteger(2147483647);
    } }
    public static BigInteger Multiplier { get {
      return new BigInteger(48271);
    } }
  }
} // end of namespace DocsIndexBench
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => DocsIndexBench.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
