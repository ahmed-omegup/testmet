include "DocsIndexTreap.dfy"

module DocsIndexBench {
  import opened DocsIndexModel
  import opened DocsIndexTreap

  const Modulus: int := 2147483647
  const Multiplier: int := 48271

  function NextState(state: int): int
    requires 0 < state < Modulus
  {
    var next := (state * Multiplier) % Modulus;
    if next == 0 then 1 else next
  }

  method NextRand(state: int, bound: nat) returns (next: int, value: nat)
    requires 0 < state < Modulus
    requires bound > 0
    ensures 0 < next < Modulus
    ensures value < bound
  {
    next := NextState(state);
    value := next % bound;
  }

  function RefInsertUnique(es: seq<Entry>, score: Score, id: DocId): seq<Entry> {
    if |es| == 0 then [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then [Entry(score, id)] + es
    else [es[0]] + RefInsertUnique(es[1..], score, id)
  }

  function RefRemoveOne(es: seq<Entry>, score: Score, id: DocId): seq<Entry> {
    if |es| == 0 then es
    else if es[0].score == score && es[0].id == id then es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then es
    else [es[0]] + RefRemoveOne(es[1..], score, id)
  }

  function RefCountStrictLess(es: seq<Entry>, score: Score): nat {
    if |es| == 0 then 0
    else (if es[0].score < score then 1 else 0) + RefCountStrictLess(es[1..], score)
  }

  function RefCountAtMost(es: seq<Entry>, score: Score): nat {
    if |es| == 0 then 0
    else (if es[0].score <= score then 1 else 0) + RefCountAtMost(es[1..], score)
  }

  function RefRankWithId(es: seq<Entry>, score: Score, id: DocId): nat {
    if |es| == 0 then 0
    else if es[0].score < score || (es[0].score == score && es[0].id < id)
      then 1 + RefRankWithId(es[1..], score, id)
      else 0
  }

  function RefRank(es: seq<Entry>, score: Score, id: MaybeDocId): nat {
    match id
    case NoDoc => RefCountStrictLess(es, score)
    case SomeDoc(doc) => RefRankWithId(es, score, doc)
  }

  function RefPositionAt(es: seq<Entry>, idx: nat): nat
    requires idx < |es|
  {
    if idx == 0 then 0
    else if es[idx - 1].score == es[idx].score then 1 + RefPositionAt(es, idx - 1) else 0
  }

  function RefGetAtRank(es: seq<Entry>, rank: nat): AtRank {
    if rank >= |es| then Missing
    else Found(es[rank].score, es[rank].id, RefPositionAt(es, rank))
  }

  function RefCollectRange(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId> {
    if |es| == 0 || limit == 0 then []
    else if es[0].score < minScore then RefCollectRange(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then []
    else [es[0].id] + RefCollectRange(es[1..], minScore, maxScore, limit - 1)
  }

  function RemoveAt<T>(xs: seq<T>, idx: nat): seq<T>
    requires idx < |xs|
  {
    if idx == 0 then xs[1..] else [xs[0]] + RemoveAt(xs[1..], idx - 1)
  }

  method {:print} CheckState(name: string, opIndex: nat, t: Treap, ref: seq<Entry>, rng: int, scoreRange: nat, nextId: DocId)
    returns (ok: bool, nextRng: int)
    requires 0 < rng < Modulus
    requires scoreRange > 0
    requires SumConsistent(t)
    ensures 0 < nextRng < Modulus
  {
    ok := false;
    nextRng := rng;

    if !ValidTreap(t) {
      print name; print ": invalid treap at op "; print opIndex; print "\n";
      return;
    }

    if Entries(t) != ref {
      print name; print ": entries mismatch at op "; print opIndex; print "\n";
      print "  treap size="; print |Entries(t)|; print " ref size="; print |ref|; print "\n";
      return;
    }

    var scoreSel: nat;
    nextRng, scoreSel := NextRand(nextRng, scoreRange);
    var score := scoreSel as int;

    if TreapRank(t, score, NoDoc) != RefRank(ref, score, NoDoc) {
      print name; print ": rank(score,null) mismatch at op "; print opIndex; print " score="; print score; print "\n";
      print "  treap="; print TreapRank(t, score, NoDoc); print " ref="; print RefRank(ref, score, NoDoc); print "\n";
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
      print name; print ": rank(score,id) mismatch at op "; print opIndex; print " score="; print score; print " doc="; print doc; print "\n";
      print "  treap="; print TreapRank(t, score, SomeDoc(doc)); print " ref="; print RefRank(ref, score, SomeDoc(doc)); print "\n";
      return;
    }

    if TreapCountAtMost(t, score) != RefCountAtMost(ref, score) {
      print name; print ": countAtMost mismatch at op "; print opIndex; print " score="; print score; print "\n";
      print "  treap="; print TreapCountAtMost(t, score); print " ref="; print RefCountAtMost(ref, score); print "\n";
      return;
    }

    var rankBound := |ref| + 3;
    var rankPick: nat;
    nextRng, rankPick := NextRand(nextRng, rankBound);

    if TreapGetAtRank(t, rankPick) != RefGetAtRank(ref, rankPick) {
      print name; print ": getAtRank mismatch at op "; print opIndex; print " rank="; print rankPick; print "\n";
      print "  treap kind/value mismatch against reference\n";
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
      print name; print ": collectRange mismatch at op "; print opIndex; print " min="; print minScore; print " max="; print maxScore; print " limit="; print limit; print "\n";
      print "  treap size="; print |TreapCollectRange(t, minScore, maxScore, limit)|; print " ref size="; print |RefCollectRange(ref, minScore, maxScore, limit)|; print "\n";
      return;
    }

    ok := true;
  }

  method {:print} RunScenario(name: string, documents: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, scoreRange: nat, checksEveryOps: nat)
    returns (ok: bool)
    requires scoreRange > 0
    requires checksEveryOps > 0
  {
    var t := Empty;
    var ref: seq<Entry> := [];
    var rng := 42;
    var nextId: DocId := 0;
    var opIndex: nat := 0;

    ok := false;

    print "[dafny-bench] scenario="; print name;
    print " docs="; print documents;
    print " ticks="; print ticks;
    print " updates/tick="; print updatesPerTick;
    print " inserts/tick="; print insertsPerTick;
    print " deletes/tick="; print deletesPerTick;
    print " scoreRange="; print scoreRange;
    print " checksEveryOps="; print checksEveryOps;
    print "\n";

    var i: nat := 0;
    while i < documents
      invariant i <= documents
      invariant SumConsistent(t)
      invariant 0 < rng < Modulus
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
    seededOk, rng := CheckState(name + " seed", opIndex, t, ref, rng, scoreRange, nextId);
    if !seededOk {
      return;
    }

    var tick: nat := 0;
    while tick < ticks
      invariant tick <= ticks
      invariant SumConsistent(t)
      invariant 0 < rng < Modulus
    {
      var u: nat := 0;
      while u < updatesPerTick
        invariant u <= updatesPerTick
        invariant SumConsistent(t)
        invariant 0 < rng < Modulus
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
    finalOk, rng := CheckState(name + " final", opIndex, t, ref, rng, scoreRange, nextId);
    if !finalOk {
      return;
    }

    print "[dafny-bench] passed scenario="; print name; print " totalOps="; print opIndex; print " finalEntries="; print |ref|; print "\n";
    ok := true;
  }

  method {:main} {:print} Main() {
    var ok := RunScenario("correctness-small", 400, 40, 20, 4, 4, 1000, 1);
    if !ok {
      return;
    }

    ok := RunScenario("benchmark-like", 2500, 120, 125, 25, 25, 2500, 200);
    if !ok {
      return;
    }

    print "[dafny-bench] all scenarios passed\n";
  }
}