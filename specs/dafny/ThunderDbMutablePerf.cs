// Dafny program ThunderDbMutablePerf.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.11.0.0
// Command-line arguments: translate cs ThunderDbMutablePerf.dfy -o ThunderDbMutablePerf.cs --include-runtime --no-verify --allow-warnings
// ThunderDbMutablePerf.dfy


module ThunderDbMutablePerf {
  const Modulus: int := 2147483647
  const Multiplier: int := 48271

  function NextState(state: int): int
    decreases state
  {
    var next: int := state * Multiplier % Modulus;
    if next <= 0 then
      next + Modulus
    else
      next
  }

  method NextRand(state: int) returns (nextState: int, value: int)
    requires state > 0
    ensures nextState > 0
    ensures value == nextState
    decreases state
  {
    nextState := NextState(state);
    value := nextState;
  }

  method {:verify false} Main(_noArgsParameter: seq<seq<char>>)
    decreases *
  {
    var runner := new MutablePerfRunner();
    runner.RunScenario(""whole-stack-benchmark-like-mutable"", 123, 800, 120, 30, 35, 8, 8, 25, 10, false);
    runner := new MutablePerfRunner();
    runner.RunScenario(""whole-stack-benchmark-like-mutable-per-tick"", 123, 800, 120, 30, 35, 8, 8, 25, 10, true);
  }

  import opened DocsIndexTreap

  import opened ThunderDbStack

  import opened ThunderDbMutable

  class MutablePerfRunner {
    var engine: MutableEngine

    constructor ()
      ensures this.engine.Ready()
    {
      this.engine := new MutableEngine();
    }

    method {:verify false} RunScenario(name: string, seed: int, documents: nat, customers: nat, ticks: nat, updatesPerTick: nat, insertsPerTick: nat, deletesPerTick: nat, queryLimit: nat, density: nat, drainPerTick: bool)
      decreases *
    {
      var summary := SummaryZero();
      var rng := if seed <= 0 then 1 else seed;
      var seedDocs := new SeedDoc[documents];
      var nextDocId := documents;
      var range := if density == 0 then 1 else documents / density + 1;
      var i := 0;
      while i < documents
        invariant 0 <= i <= documents
        invariant rng > 0
        decreases documents - i
      {
        var nextRng, scoreSeed := NextRand(rng);
        rng := nextRng;
        seedDocs[i] := SeedDoc(i, DocState(scoreSeed % range));
        i := i + 1;
      }
      var seedEvents, ignoredQueryId := engine.ProcessItem(SeedDocsItem(seedDocs[..]));
      summary := UpdateSummary(summary, seedEvents);
      i := 0;
      while i < customers
        invariant 0 <= i <= customers
        invariant rng > 0
        invariant SumConsistent(engine.docs)
        decreases customers - i
      {
        var nextRng1, widthSeed := NextRand(rng);
        rng := nextRng1;
        var nextRng2, minSeed := NextRand(rng);
        rng := nextRng2;
        var width := 1 + widthSeed % (range / 2 + 1);
        var minScore := minSeed % range;
        var maxScore := minScore + width;
        var spec := QuerySpec(minScore, maxScore, queryLimit);
        var events: seq<DownstreamEvent>;
        var queryId: QueryId;
        if drainPerTick {
          events, queryId := engine.ProcessItemDeferred(QueryAddItem(spec));
        } else {
          events, queryId := engine.ProcessItem(QueryAddItem(spec));
        }
        summary := UpdateSummary(summary, events);
        i := i + 1;
      }
      if drainPerTick {
        var retrievalEvents := engine.DrainPendingRetrievalsGrouped();
        summary := UpdateSummary(summary, retrievalEvents);
      }
      var tick := 0;
      while tick < ticks
        invariant 0 <= tick <= ticks
        invariant rng > 0
        invariant SumConsistent(engine.docs)
        decreases ticks - tick
      {
        var update := 0;
        while update < updatesPerTick
          invariant 0 <= update <= updatesPerTick
          invariant rng > 0
          invariant SumConsistent(engine.docs)
          decreases updatesPerTick - update
        {
          if |engine.docIds| > 0 {
            var nextRng3, pickSeed := NextRand(rng);
            rng := nextRng3;
            var nextRng4, scoreSeed := NextRand(rng);
            rng := nextRng4;
            var picked := pickSeed % |engine.docIds|;
            var docId := engine.docIds[picked];
            match LookupState(engine.store, docId)
            case {:split false} NoState() =>
              {
              }
            case {:split false} HasState(docState) =>
              {
                var updatedDocState := DocState(scoreSeed % range);
                var events: seq<DownstreamEvent>;
                var ignoredQueryId2: QueryId;
                if drainPerTick {
                  events, ignoredQueryId2 := engine.ProcessItemDeferred(DocChangeItem(docId, HasState(docState), HasState(updatedDocState)));
                } else {
                  events, ignoredQueryId2 := engine.ProcessItem(DocChangeItem(docId, HasState(docState), HasState(updatedDocState)));
                }
                summary := UpdateSummary(summary, events);
              }
          }
          update := update + 1;
        }
        var insert := 0;
        while insert < insertsPerTick
          invariant 0 <= insert <= insertsPerTick
          invariant rng > 0
          invariant SumConsistent(engine.docs)
          decreases insertsPerTick - insert
        {
          var nextRng5, scoreSeed := NextRand(rng);
          rng := nextRng5;
          var newDoc := DocState(scoreSeed % range);
          var events: seq<DownstreamEvent>;
          var ignoredQueryId3: QueryId;
          if drainPerTick {
            events, ignoredQueryId3 := engine.ProcessItemDeferred(DocChangeItem(nextDocId, NoState, HasState(newDoc)));
          } else {
            events, ignoredQueryId3 := engine.ProcessItem(DocChangeItem(nextDocId, NoState, HasState(newDoc)));
          }
          summary := UpdateSummary(summary, events);
          nextDocId := nextDocId + 1;
          insert := insert + 1;
        }
        var delete := 0;
        while delete < deletesPerTick
          invariant 0 <= delete <= deletesPerTick
          invariant rng > 0
          invariant SumConsistent(engine.docs)
          decreases deletesPerTick - delete
        {
          if |engine.docIds| > 0 {
            var nextRng6, pickSeed := NextRand(rng);
            rng := nextRng6;
            var picked := pickSeed % |engine.docIds|;
            var docId := engine.docIds[picked];
            match LookupState(engine.store, docId)
            case {:split false} NoState() =>
              {
              }
            case {:split false} HasState(docState) =>
              {
                var events: seq<DownstreamEvent>;
                var ignoredQueryId4: QueryId;
                if drainPerTick {
                  events, ignoredQueryId4 := engine.ProcessItemDeferred(DocChangeItem(docId, HasState(docState), NoState));
                } else {
                  events, ignoredQueryId4 := engine.ProcessItem(DocChangeItem(docId, HasState(docState), NoState));
                }
                summary := UpdateSummary(summary, events);
              }
          }
          delete := delete + 1;
        }
        if drainPerTick {
          var retrievalEvents := engine.DrainPendingRetrievalsGrouped();
          summary := UpdateSummary(summary, retrievalEvents);
        }
        tick := tick + 1;
      }
      if drainPerTick {
        var retrievalEvents := engine.DrainPendingRetrievalsGrouped();
        summary := UpdateSummary(summary, retrievalEvents);
      }
      print ""scenario "";
      print name;
      print "" done: events="";
      print summary.eventsProcessed;
      print "", matches="";
      print summary.matchEvents;
      print "", evictions="";
      print summary.evictions;
      print "", retrievalBatches="";
      print summary.retrievalBatches;
      print "", retrievalDocs="";
      print summary.retrievalDocs;
      print ""\n"";
    }
  }
}

module ThunderDbMutable {
  const NegInfInt: int := -2147483647
  const NegInfScore: Score := -2147483647

  function MaxInt(a: int, b: int): int
    decreases a, b
  {
    if a >= b then
      a
    else
      b
  }

  function MaxScore(a: Score, b: Score): Score
    decreases a, b
  {
    if a >= b then
      a
    else
      b
  }

  function InsertQueryIndexEntry(items: seq<QueryIndexEntry>, entry: QueryIndexEntry): seq<QueryIndexEntry>
    decreases items, entry
  {
    if |items| == 0 then
      [entry]
    else if entry.baseScore < items[0].baseScore || (entry.baseScore == items[0].baseScore && entry.id < items[0].id) then
      [entry] + items
    else
      [items[0]] + InsertQueryIndexEntry(items[1..], entry)
  }

  function RemoveQueryIndexEntry(items: seq<QueryIndexEntry>, id: QueryId, baseScore: int, maxCap: Score): seq<QueryIndexEntry>
    decreases items, id, baseScore, maxCap
  {
    if |items| == 0 then
      []
    else if items[0].id == id && items[0].baseScore == baseScore && items[0].maxCap == maxCap then
      items[1..]
    else
      [items[0]] + RemoveQueryIndexEntry(items[1..], id, baseScore, maxCap)
  }

  function MaxBaseScore(items: seq<QueryIndexEntry>): int
    decreases items
  {
    if |items| == 0 then
      NegInfInt
    else
      MaxInt(items[0].baseScore, MaxBaseScore(items[1..]))
  }

  function MaxCapScore(items: seq<QueryIndexEntry>): Score
    decreases items
  {
    if |items| == 0 then
      NegInfScore
    else
      MaxScore(items[0].maxCap, MaxCapScore(items[1..]))
  }

  function CollectLocalIds(items: seq<QueryIndexEntry>, accHere: int, cutoff: int, value: Score): seq<QueryId>
    decreases |items|
  {
    if |items| == 0 then
      []
    else if items[0].maxCap >= value && items[0].baseScore + accHere > cutoff then
      [items[0].id] + CollectLocalIds(items[1..], accHere, cutoff, value)
    else
      CollectLocalIds(items[1..], accHere, cutoff, value)
  }

  function UniqueConcatQueryIds(left: seq<QueryId>, right: seq<QueryId>): seq<QueryId>
    decreases |right|
  {
    if |right| == 0 then
      left
    else
      UniqueConcatQueryIds(AppendQueryIdUnique(left, right[0]), right[1..])
  }

  function RemoveQueryId(ids: seq<QueryId>, id: QueryId): seq<QueryId>
    decreases ids, id
  {
    if |ids| == 0 then
      []
    else if ids[0] == id then
      ids[1..]
    else
      [ids[0]] + RemoveQueryId(ids[1..], id)
  }

  function RemovePendingRetrieval(pending: seq<PendingRetrieval>, docId: DocId, queryId: QueryId): seq<PendingRetrieval>
    decreases pending, docId, queryId
  {
    if |pending| == 0 then
      []
    else if pending[0].docId == docId && pending[0].queryId == queryId then
      pending[1..]
    else
      [pending[0]] + RemovePendingRetrieval(pending[1..], docId, queryId)
  }

  function RemovePendingRetrievalsForDoc(pending: seq<PendingRetrieval>, docId: DocId): seq<PendingRetrieval>
    decreases pending, docId
  {
    if |pending| == 0 then
      []
    else if pending[0].docId == docId then
      RemovePendingRetrievalsForDoc(pending[1..], docId)
    else
      [pending[0]] + RemovePendingRetrievalsForDoc(pending[1..], docId)
  }

  function QueryNodeCount(tree: QueryTree): nat
    decreases tree
  {
    if tree.QEmpty? then
      0
    else
      1 + QueryNodeCount(tree.left) + QueryNodeCount(tree.right)
  }

  function QuerySubMax(tree: QueryTree): int
    decreases tree
  {
    if tree.QEmpty? then
      NegInfInt
    else
      tree.subtreeMax
  }

  function QuerySubCap(tree: QueryTree): Score
    decreases tree
  {
    if tree.QEmpty? then
      NegInfScore
    else
      tree.subtreeMaxCap
  }

  function QueryPriorityForKey(key: Score): int
    decreases key
  {
    ((key + 1) * 1103515245 + 12345) % 2147483647
  }

  function QueryPush(tree: QueryTree): QueryTree
    requires tree.QNode?
    decreases tree
  {
    if tree.add == 0 then
      tree
    else
      var left2: QueryTree := if tree.left.QEmpty? then QEmpty else QNode(tree.left.key, tree.left.prio, tree.left.add + tree.add, tree.left.localAdd, tree.left.items, if tree.left.subtreeMax == NegInfInt then NegInfInt else tree.left.subtreeMax + tree.add, tree.left.localMaxCap, tree.left.subtreeMaxCap, tree.left.left, tree.left.right); var right2: QueryTree := if tree.right.QEmpty? then QEmpty else QNode(tree.right.key, tree.right.prio, tree.right.add + tree.add, tree.right.localAdd, tree.right.items, if tree.right.subtreeMax == NegInfInt then NegInfInt else tree.right.subtreeMax + tree.add, tree.right.localMaxCap, tree.right.subtreeMaxCap, tree.right.left, tree.right.right); QNode(tree.key, tree.prio, 0, tree.localAdd + tree.add, tree.items, tree.subtreeMax, tree.localMaxCap, tree.subtreeMaxCap, left2, right2)
  }

  function QueryPull(tree: QueryTree): QueryTree
    requires tree.QNode?
    decreases tree
  {
    var localCap: Score := MaxCapScore(tree.items);
    var localMax: int := if |tree.items| == 0 then NegInfInt else MaxBaseScore(tree.items) + tree.localAdd;
    var merged: int := MaxInt(localMax, MaxInt(QuerySubMax(tree.left), QuerySubMax(tree.right)));
    QNode(tree.key, tree.prio, tree.add, tree.localAdd, tree.items, if merged == NegInfInt then NegInfInt else tree.add + merged, localCap, MaxScore(localCap, MaxScore(QuerySubCap(tree.left), QuerySubCap(tree.right))), tree.left, tree.right)
  }

  function QueryRotateRight(tree: QueryTree): QueryTree
    requires tree.QNode? && tree.left.QNode?
    decreases tree
  {
    var pushed: QueryTree := QueryPush(tree);
    var leftPushed: QueryTree := QueryPush(pushed.left);
    var demoted: QueryTree := QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, leftPushed.right, pushed.right));
    QueryPull(QNode(leftPushed.key, leftPushed.prio, leftPushed.add, leftPushed.localAdd, leftPushed.items, 0, leftPushed.localMaxCap, leftPushed.subtreeMaxCap, leftPushed.left, demoted))
  }

  function QueryRotateLeft(tree: QueryTree): QueryTree
    requires tree.QNode? && tree.right.QNode?
    decreases tree
  {
    var pushed: QueryTree := QueryPush(tree);
    var rightPushed: QueryTree := QueryPush(pushed.right);
    var demoted: QueryTree := QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, pushed.left, rightPushed.left));
    QueryPull(QNode(rightPushed.key, rightPushed.prio, rightPushed.add, rightPushed.localAdd, rightPushed.items, 0, rightPushed.localMaxCap, rightPushed.subtreeMaxCap, demoted, rightPushed.right))
  }

  method QuerySplitByKey(tree: QueryTree, key: Score) returns (pair: QueryTreePair)
    decreases *
  {
    if tree.QEmpty? {
      pair := QueryTreePair(QEmpty, QEmpty);
    } else {
      var pushed := QueryPush(tree);
      if key < pushed.key {
        var nextPair := QuerySplitByKey(pushed.left, key);
        pair := QueryTreePair(nextPair.left, QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, nextPair.right, pushed.right)));
      } else {
        var nextPair := QuerySplitByKey(pushed.right, key);
        pair := QueryTreePair(QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, pushed.left, nextPair.left)), nextPair.right);
      }
    }
  }

  method QueryMerge(leftTree: QueryTree, rightTree: QueryTree) returns (result: QueryTree)
    decreases *
  {
    if leftTree.QEmpty? {
      result := rightTree;
    } else if rightTree.QEmpty? {
      result := leftTree;
    } else {
      var leftPushed := QueryPush(leftTree);
      var rightPushed := QueryPush(rightTree);
      if leftPushed.prio > rightPushed.prio {
        var mergedRight := QueryMerge(leftPushed.right, rightPushed);
        result := QueryPull(QNode(leftPushed.key, leftPushed.prio, leftPushed.add, leftPushed.localAdd, leftPushed.items, 0, leftPushed.localMaxCap, leftPushed.subtreeMaxCap, leftPushed.left, mergedRight));
      } else {
        var mergedLeft := QueryMerge(leftPushed, rightPushed.left);
        result := QueryPull(QNode(rightPushed.key, rightPushed.prio, rightPushed.add, rightPushed.localAdd, rightPushed.items, 0, rightPushed.localMaxCap, rightPushed.subtreeMaxCap, mergedLeft, rightPushed.right));
      }
    }
  }

  method QueryInsert(tree: QueryTree, key: Score, id: QueryId, effectiveScore: int, maxCap: Score, accAdd: int)
      returns (result: QueryTree)
    decreases *
  {
    if tree.QEmpty? {
      result := QueryPull(QNode(key, QueryPriorityForKey(key), 0, 0, [QueryIndexEntry(id, effectiveScore - accAdd, maxCap)], 0, NegInfScore, NegInfScore, QEmpty, QEmpty));
    } else if key == tree.key {
      result := QueryPull(QNode(tree.key, tree.prio, tree.add, tree.localAdd, InsertQueryIndexEntry(tree.items, QueryIndexEntry(id, effectiveScore - accAdd - tree.add - tree.localAdd, maxCap)), 0, tree.localMaxCap, tree.subtreeMaxCap, tree.left, tree.right));
    } else if key < tree.key {
      var left2 := QueryInsert(tree.left, key, id, effectiveScore, maxCap, accAdd + tree.add);
      var current := QueryPull(QNode(tree.key, tree.prio, tree.add, tree.localAdd, tree.items, 0, tree.localMaxCap, tree.subtreeMaxCap, left2, tree.right));
      if left2.QNode? && left2.prio > tree.prio {
        result := QueryRotateRight(current);
      } else {
        result := current;
      }
    } else {
      var right2 := QueryInsert(tree.right, key, id, effectiveScore, maxCap, accAdd + tree.add);
      var current := QueryPull(QNode(tree.key, tree.prio, tree.add, tree.localAdd, tree.items, 0, tree.localMaxCap, tree.subtreeMaxCap, tree.left, right2));
      if right2.QNode? && right2.prio > tree.prio {
        result := QueryRotateLeft(current);
      } else {
        result := current;
      }
    }
  }

  method QueryRemove(tree: QueryTree, key: Score, id: QueryId, baseScore: int, maxCap: Score)
      returns (result: QueryTree)
    decreases *
  {
    if tree.QEmpty? {
      result := QEmpty;
    } else {
      var pushed := QueryPush(tree);
      if key == pushed.key {
        var items2 := RemoveQueryIndexEntry(pushed.items, id, baseScore, maxCap);
        if |items2| == 0 {
          result := QueryMerge(pushed.left, pushed.right);
        } else {
          result := QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, items2, 0, pushed.localMaxCap, pushed.subtreeMaxCap, pushed.left, pushed.right));
        }
      } else if key < pushed.key {
        var left2 := QueryRemove(pushed.left, key, id, baseScore, maxCap);
        result := QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, left2, pushed.right));
      } else {
        var right2 := QueryRemove(pushed.right, key, id, baseScore, maxCap);
        result := QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, pushed.left, right2));
      }
    }
  }

  method QueryCollectForValue(tree: QueryTree, accAdd: int, cutoff: int, value: Score)
      returns (out: seq<QueryId>)
    decreases *
  {
    if tree.QEmpty? || tree.subtreeMaxCap < value {
      out := [];
    } else {
      var effSubMax := if tree.subtreeMax == NegInfInt then NegInfInt else tree.subtreeMax + accAdd;
      if effSubMax == NegInfInt || effSubMax <= cutoff {
        out := [];
      } else {
        var childAcc := accAdd + tree.add;
        if tree.key > value {
          out := QueryCollectForValue(tree.left, childAcc, cutoff, value);
        } else {
          var leftOut := QueryCollectForValue(tree.left, childAcc, cutoff, value);
          var rightOut := QueryCollectForValue(tree.right, childAcc, cutoff, value);
          out := leftOut + CollectLocalIds(tree.items, childAcc + tree.localAdd, cutoff, value) + rightOut;
        }
      }
    }
  }

  method QueryAccumulatedAddAtKey(tree: QueryTree, key: Score) returns (acc: int)
    decreases *
  {
    if tree.QEmpty? {
      acc := 0;
    } else if key == tree.key {
      acc := tree.add + tree.localAdd;
    } else if key < tree.key {
      var childAcc := QueryAccumulatedAddAtKey(tree.left, key);
      acc := tree.add + childAcc;
    } else {
      var childAcc := QueryAccumulatedAddAtKey(tree.right, key);
      acc := tree.add + childAcc;
    }
  }

  import opened DocsIndexModel

  import opened DocsIndexTreap

  import opened ThunderDbStack

  datatype QueryIndexEntry = QueryIndexEntry(id: QueryId, baseScore: int, maxCap: Score)

  datatype QueryState = QueryState(spec: QuerySpec, currentMatches: nat, baseScore: int)

  datatype PendingRetrieval = PendingRetrieval(docId: DocId, queryId: QueryId)

  datatype QueryTree = QEmpty | QNode(key: Score, prio: int, add: int, localAdd: int, items: seq<QueryIndexEntry>, subtreeMax: int, localMaxCap: Score, subtreeMaxCap: Score, left: QueryTree, right: QueryTree)

  datatype QueryTreePair = QueryTreePair(left: QueryTree, right: QueryTree)

  class MutableQueryIndex {
    var root: QueryTree

    constructor ()
      ensures this.root == QEmpty
    {
      this.root := QEmpty;
    }

    method RangeAddKeysGreaterThan(key: Score, delta: int)
      modifies this
      decreases *
    {
      var pair := QuerySplitByKey(this.root, key);
      var rightTree := pair.right;
      if rightTree.QNode? {
        rightTree := QNode(rightTree.key, rightTree.prio, rightTree.add + delta, rightTree.localAdd, rightTree.items, if rightTree.subtreeMax == NegInfInt then NegInfInt else rightTree.subtreeMax + delta, rightTree.localMaxCap, rightTree.subtreeMaxCap, rightTree.left, rightTree.right);
      }
      var merged := QueryMerge(pair.left, rightTree);
      this.root := merged;
    }

    method Insert(key: Score, id: QueryId, effectiveScore: int, maxCap: Score)
      modifies this
      decreases *
    {
      var nextRoot := QueryInsert(this.root, key, id, effectiveScore, maxCap, 0);
      this.root := nextRoot;
    }

    method Remove(key: Score, id: QueryId, baseScore: int, maxCap: Score)
      modifies this
      decreases *
    {
      var nextRoot := QueryRemove(this.root, key, id, baseScore, maxCap);
      this.root := nextRoot;
    }

    method CollectForValue(value: Score, cutoff: int) returns (out: seq<QueryId>)
      decreases *
    {
      out := QueryCollectForValue(this.root, 0, cutoff, value);
    }

    method AccumulatedAddAtKey(key: Score) returns (acc: int)
      decreases *
    {
      acc := QueryAccumulatedAddAtKey(this.root, key);
    }
  }

  class MutableEngine {
    var docs: Treap
    var store: map<DocId, DocState>
    var docIds: seq<DocId>
    var queryIndex: MutableQueryIndex
    var queries: map<QueryId, QueryState>
    var pendingByQuery: map<QueryId, seq<DocId>>
    var pendingByDoc: map<DocId, seq<QueryId>>
    var pendingDocs: seq<DocId>
    var pendingPairs: seq<PendingRetrieval>
    var nextQueryId: QueryId

    constructor ()
      ensures this.docs == Empty
      ensures this.store == map[]
      ensures this.docIds == []
      ensures this.queries == map[]
      ensures this.pendingByQuery == map[]
      ensures this.pendingByDoc == map[]
      ensures this.pendingDocs == []
      ensures this.pendingPairs == []
      ensures this.nextQueryId == 1
      ensures this.Ready()
    {
      this.docs := Empty;
      this.store := map[];
      this.docIds := [];
      this.queryIndex := new MutableQueryIndex();
      this.queries := map[];
      this.pendingByQuery := map[];
      this.pendingByDoc := map[];
      this.pendingDocs := [];
      this.pendingPairs := [];
      this.nextQueryId := 1;
    }

    predicate Ready()
      reads this
      decreases {this}
    {
      SumConsistent(this.docs)
    }

    method CollectQueriesForValue(value: Score, docId: DocId) returns (ids: seq<QueryId>)
      requires this.Ready()
      decreases *
    {
      var cutoff: int := TreapRank(this.docs, value, SomeDoc(docId));
      ids := this.queryIndex.CollectForValue(value, cutoff);
    }

    method RegisterPendingDocQuery(docId: DocId, queryId: QueryId)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases *
    {
      var docsForQuery := if queryId in this.pendingByQuery then this.pendingByQuery[queryId] else [];
      docsForQuery := AppendDocIdIfMissing(docsForQuery, docId);
      this.pendingByQuery := this.pendingByQuery[queryId := docsForQuery];
      var queriesForDoc := if docId in this.pendingByDoc then this.pendingByDoc[docId] else [];
      queriesForDoc := AppendQueryIdUnique(queriesForDoc, queryId);
      this.pendingByDoc := this.pendingByDoc[docId := queriesForDoc];
      this.pendingDocs := AppendDocIdIfMissing(this.pendingDocs, docId);
      this.pendingPairs := this.pendingPairs + [PendingRetrieval(docId, queryId)];
    }

    method RemovePendingDocQuery(docId: DocId, queryId: QueryId) returns (removed: bool)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases *
    {
      removed := false;
      if queryId in this.pendingByQuery {
        var docsForQuery := this.pendingByQuery[queryId];
        if ContainsId(docsForQuery, docId) {
          removed := true;
          var nextDocsForQuery := RemoveDocId(docsForQuery, docId);
          if |nextDocsForQuery| == 0 {
            this.pendingByQuery := map key: int {:trigger this.pendingByQuery[key]} {:trigger key in this.pendingByQuery} | key in this.pendingByQuery && key != queryId :: this.pendingByQuery[key];
          } else {
            this.pendingByQuery := this.pendingByQuery[queryId := nextDocsForQuery];
          }
        }
      }
      if docId in this.pendingByDoc {
        var queriesForDoc := this.pendingByDoc[docId];
        if ContainsQueryId(queriesForDoc, queryId) {
          var nextQueriesForDoc := RemoveQueryId(queriesForDoc, queryId);
          if |nextQueriesForDoc| == 0 {
            this.pendingByDoc := map key: int {:trigger this.pendingByDoc[key]} {:trigger key in this.pendingByDoc} | key in this.pendingByDoc && key != docId :: this.pendingByDoc[key];
            this.pendingDocs := RemoveDocId(this.pendingDocs, docId);
          } else {
            this.pendingByDoc := this.pendingByDoc[docId := nextQueriesForDoc];
          }
        }
      }
      if removed {
        this.pendingPairs := RemovePendingRetrieval(this.pendingPairs, docId, queryId);
      }
    }

    method ResolvePendingForDoc(docId: DocId)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases *
    {
      if docId in this.pendingByDoc {
        var queriesForDoc := this.pendingByDoc[docId];
        var i := 0;
        while i < |queriesForDoc|
          invariant 0 <= i <= |queriesForDoc|
          invariant SumConsistent(this.docs)
          decreases |queriesForDoc| - i
        {
          if queriesForDoc[i] in this.pendingByQuery {
            var docsForQuery := this.pendingByQuery[queriesForDoc[i]];
            var nextDocsForQuery := RemoveDocId(docsForQuery, docId);
            if |nextDocsForQuery| == 0 {
              this.pendingByQuery := map key: int {:trigger this.pendingByQuery[key]} {:trigger key in this.pendingByQuery} | key in this.pendingByQuery && key != queriesForDoc[i] :: this.pendingByQuery[key];
            } else {
              this.pendingByQuery := this.pendingByQuery[queriesForDoc[i] := nextDocsForQuery];
            }
          }
          i := i + 1;
        }
        this.pendingByDoc := map key: int {:trigger this.pendingByDoc[key]} {:trigger key in this.pendingByDoc} | key in this.pendingByDoc && key != docId :: this.pendingByDoc[key];
        this.pendingDocs := RemoveDocId(this.pendingDocs, docId);
        this.pendingPairs := RemovePendingRetrievalsForDoc(this.pendingPairs, docId);
      }
    }

    method CancelPendingForQuery(docId: DocId, queryId: QueryId) returns (cancelled: bool)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases *
    {
      cancelled := this.RemovePendingDocQuery(docId, queryId);
      if cancelled && queryId in this.queries {
        var state := this.queries[queryId];
        if state.currentMatches > 0 {
          this.queries := this.queries[queryId := QueryState(state.spec, state.currentMatches - 1, state.baseScore)];
        }
      }
    }

    method DrainPendingRetrievals() returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases *
    {
      events := [];
      var queued := this.pendingPairs;
      var retrievals: seq<RetrievalDoc> := [];
      var i := 0;
      while i < |queued|
        invariant 0 <= i <= |queued|
        invariant SumConsistent(this.docs)
        decreases |queued| - i
      {
        var docId := queued[i].docId;
        var queryId := queued[i].queryId;
        if docId in this.pendingByDoc && ContainsQueryId(this.pendingByDoc[docId], queryId) {
          match LookupState(this.store, docId)
          case {:split false} NoState() =>
            {
            }
          case {:split false} HasState(docState) =>
            {
              retrievals := retrievals + [RetrievalDoc(docId, docState, [queryId])];
            }
        }
        i := i + 1;
      }
      this.pendingByQuery := map[];
      this.pendingByDoc := map[];
      this.pendingDocs := [];
      this.pendingPairs := [];
      if |retrievals| > 0 {
        events := [RetrievalEvent(retrievals)];
      }
    }

    method DrainPendingRetrievalsGrouped() returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases *
    {
      events := [];
      var queued := this.pendingDocs;
      var retrievals: seq<RetrievalDoc> := [];
      var i := 0;
      while i < |queued|
        invariant 0 <= i <= |queued|
        invariant SumConsistent(this.docs)
        decreases |queued| - i
      {
        var docId := queued[i];
        if docId in this.pendingByDoc {
          var queriesForDoc := this.pendingByDoc[docId];
          match LookupState(this.store, docId)
          case {:split false} NoState() =>
            {
            }
          case {:split false} HasState(docState) =>
            {
              retrievals := retrievals + [RetrievalDoc(docId, docState, queriesForDoc)];
            }
        }
        i := i + 1;
      }
      this.pendingByQuery := map[];
      this.pendingByDoc := map[];
      this.pendingDocs := [];
      this.pendingPairs := [];
      if |retrievals| > 0 {
        events := [RetrievalEvent(retrievals)];
      }
    }

    method QueryVisible(id: QueryId) returns (visible: seq<DocId>)
      requires this.Ready()
      decreases *
    {
      if id in this.queries {
        var state := this.queries[id];
        visible := TreapCollectRange(this.docs, state.spec.minScore, state.spec.maxScore, state.spec.limit);
      } else {
        visible := [];
      }
    }

    method CountDocsInRange(spec: QuerySpec) returns (count: nat)
      requires this.Ready()
      decreases *
    {
      var upper := TreapCountAtMost(this.docs, spec.maxScore);
      var lower := TreapRank(this.docs, spec.minScore, NoDoc);
      var diff := if upper >= lower then upper - lower else 0;
      if diff <= spec.limit {
        count := diff;
      } else {
        count := spec.limit;
      }
    }

    method QueryDocAtOffset(state: QueryState, offset: nat) returns (doc: MaybeDocId)
      requires this.Ready()
      decreases *
    {
      var addAtKey := this.queryIndex.AccumulatedAddAtKey(state.spec.minScore);
      var effectiveScore := state.baseScore + addAtKey;
      var startRank := if effectiveScore >= state.spec.limit then effectiveScore - state.spec.limit else 0;
      match TreapGetAtRank(this.docs, startRank + offset)
      case {:split false} Missing() =>
        {
          doc := NoDoc;
        }
      case {:split false} Found(score, id, pos) =>
        {
          if score <= state.spec.maxScore {
            doc := SomeDoc(id);
          } else {
            doc := NoDoc;
          }
        }
    }

    method FillGap(queryId: QueryId) returns (retrievals: seq<RetrievalDoc>)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases *
    {
      retrievals := [];
      if queryId in this.queries {
        var state := this.queries[queryId];
        if state.currentMatches < state.spec.limit {
          var offset := state.currentMatches;
          var found := false;
          while !found
            invariant SumConsistent(this.docs)
          {
            var candidate := this.QueryDocAtOffset(state, offset);
            match candidate
            case {:split false} NoDoc() =>
              {
                found := true;
              }
            case {:split false} SomeDoc(docId) =>
              {
                var alreadyPending := queryId in this.pendingByQuery && ContainsId(this.pendingByQuery[queryId], docId);
                if alreadyPending {
                  offset := offset + 1;
                } else {
                  this.queries := this.queries[queryId := QueryState(state.spec, state.currentMatches + 1, state.baseScore)];
                  this.RegisterPendingDocQuery(docId, queryId);
                  retrievals := [];
                  found := true;
                }
              }
          }
        }
      }
    }

    method PickOverflowDoc(queryId: QueryId) returns (doc: seq<DocId>)
      requires this.Ready()
      decreases *
    {
      doc := [];
      if queryId in this.queries {
        var state := this.queries[queryId];
        if state.currentMatches >= state.spec.limit {
          var candidate := this.QueryDocAtOffset(state, state.spec.limit);
          match candidate
          case {:split false} NoDoc() =>
            {
            }
          case {:split false} SomeDoc(docId) =>
            {
              doc := [docId];
            }
        }
      }
    }

    method SeedDocs(input: seq<SeedDoc>)
      requires this.Ready()
      modifies this
      ensures this.Ready()
      decreases input
    {
      var i := 0;
      while i < |input|
        invariant 0 <= i <= |input|
        invariant SumConsistent(this.docs)
        decreases |input| - i
      {
        this.store := this.store[input[i].id := input[i].state];
        this.docIds := AppendDocIdIfMissing(this.docIds, input[i].id);
        this.docs := Add(this.docs, input[i].state.scoreValue, input[i].id, PriorityFor(input[i].state.scoreValue, input[i].id));
        i := i + 1;
      }
    }

    method AddQueryDeferred(spec: QuerySpec) returns (queryId: QueryId, events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      queryId := this.nextQueryId;
      this.nextQueryId := this.nextQueryId + 1;
      var visible := TreapCollectRange(this.docs, spec.minScore, spec.maxScore, spec.limit);
      var effectiveScore: int := TreapRank(this.docs, spec.minScore, NoDoc) + spec.limit;
      this.queryIndex.Insert(spec.minScore, queryId, effectiveScore, spec.maxScore);
      var accAtKey := this.queryIndex.AccumulatedAddAtKey(spec.minScore);
      var baseScore := effectiveScore - accAtKey;
      this.queries := this.queries[queryId := QueryState(spec, |visible|, baseScore)];
      var i := 0;
      while i < |visible|
        invariant 0 <= i <= |visible|
        invariant SumConsistent(this.docs)
        decreases |visible| - i
      {
        this.RegisterPendingDocQuery(visible[i], queryId);
        i := i + 1;
      }
      events := [];
    }

    method AddQuery(spec: QuerySpec) returns (queryId: QueryId, events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      queryId, events := this.AddQueryDeferred(spec);
      var retrievalEvents := this.DrainPendingRetrievals();
      events := events + retrievalEvents;
    }

    method RemoveQueryDeferred(id: QueryId) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      if id in this.queries {
        var state := this.queries[id];
        this.queryIndex.Remove(state.spec.minScore, id, state.baseScore, state.spec.maxScore);
        this.queries := map key: int {:trigger this.queries[key]} {:trigger key in this.queries} | key in this.queries && key != id :: this.queries[key];
        if id in this.pendingByQuery {
          var pendingDocs := this.pendingByQuery[id];
          var i := 0;
          while i < |pendingDocs|
            invariant 0 <= i <= |pendingDocs|
            invariant SumConsistent(this.docs)
            decreases |pendingDocs| - i
          {
            var ignored := this.RemovePendingDocQuery(pendingDocs[i], id);
            i := i + 1;
          }
        }
      }
      events := [];
    }

    method RemoveQuery(id: QueryId) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      events := this.RemoveQueryDeferred(id);
      var retrievalEvents := this.DrainPendingRetrievals();
      events := events + retrievalEvents;
    }

    method ApplyDocChangeDeferred(id: DocId, oldState: MaybeDocState, newState: MaybeDocState)
        returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      events := [];
      if oldState.HasState? && newState.HasState? && GetScore(oldState.state) == GetScore(newState.state) {
        var covering := this.CollectQueriesForValue(GetScore(oldState.state), id);
        this.store := this.store[id := newState.state];
        this.ResolvePendingForDoc(id);
        if |covering| > 0 {
          events := [MatchEvent(MatchPayload(id, oldState, newState, covering, covering, []))];
        }
        return;
      }
      var oldMatches: seq<QueryId> := [];
      var newMatches: seq<QueryId> := [];
      var blockedCandidates: seq<QueryId> := [];
      var queryIndex := this.queryIndex;
      if oldState.HasState? {
        oldMatches := this.CollectQueriesForValue(GetScore(oldState.state), id);
        this.docs := Remove(this.docs, GetScore(oldState.state), id);
        queryIndex.RangeAddKeysGreaterThan(GetScore(oldState.state), -1);
        var oi := 0;
        while oi < |oldMatches|
          invariant 0 <= oi <= |oldMatches|
          invariant SumConsistent(this.docs)
          decreases |oldMatches| - oi
        {
          if oldMatches[oi] in this.queries {
            var state := this.queries[oldMatches[oi]];
            if state.currentMatches > 0 {
              this.queries := this.queries[oldMatches[oi] := QueryState(state.spec, state.currentMatches - 1, state.baseScore)];
            }
          }
          oi := oi + 1;
        }
      }
      if newState.HasState? {
        var newScore := GetScore(newState.state);
        newMatches := this.CollectQueriesForValue(newScore, id);
        this.docs := Add(this.docs, newScore, id, PriorityFor(newScore, id));
        queryIndex.RangeAddKeysGreaterThan(newScore, 1);
        this.store := this.store[id := newState.state];
        this.docIds := AppendDocIdIfMissing(this.docIds, id);
        var ni := 0;
        while ni < |newMatches|
          invariant 0 <= ni <= |newMatches|
          invariant SumConsistent(this.docs)
          decreases |newMatches| - ni
        {
          if newMatches[ni] in this.queries {
            var state := this.queries[newMatches[ni]];
            var consumedPending := this.RemovePendingDocQuery(id, newMatches[ni]);
            if consumedPending {
            } else if state.currentMatches < state.spec.limit {
              this.queries := this.queries[newMatches[ni] := QueryState(state.spec, state.currentMatches + 1, state.baseScore)];
            } else {
              blockedCandidates := blockedCandidates + [newMatches[ni]];
            }
          }
          ni := ni + 1;
        }
      } else {
        this.store := RemoveStoredDoc(this.store, id);
        this.docIds := RemoveDocId(this.docIds, id);
      }
      var oldMatchMap: map<QueryId, bool> := map[];
      var newMatchMap: map<QueryId, bool> := map[];
      var oi := 0;
      while oi < |oldMatches|
        invariant 0 <= oi <= |oldMatches|
        decreases |oldMatches| - oi
      {
        oldMatchMap := oldMatchMap[oldMatches[oi] := true];
        oi := oi + 1;
      }
      var ni := 0;
      while ni < |newMatches|
        invariant 0 <= ni <= |newMatches|
        decreases |newMatches| - ni
      {
        newMatchMap := newMatchMap[newMatches[ni] := true];
        ni := ni + 1;
      }
      var evictions: seq<Eviction> := [];
      var retrievals: seq<RetrievalDoc> := [];
      var matchesOld := oldMatches;
      var matchesNew := newMatches;
      var lostQueries: seq<QueryId> := [];
      var li := 0;
      while li < |oldMatches|
        invariant 0 <= li <= |oldMatches|
        invariant SumConsistent(this.docs)
        decreases |oldMatches| - li
      {
        if !(oldMatches[li] in newMatchMap) {
          lostQueries := lostQueries + [oldMatches[li]];
        }
        li := li + 1;
      }
      li := 0;
      while li < |lostQueries|
        invariant 0 <= li <= |lostQueries|
        invariant SumConsistent(this.docs)
        decreases |lostQueries| - li
      {
        var gapRetrievals := this.FillGap(lostQueries[li]);
        retrievals := retrievals + gapRetrievals;
        li := li + 1;
      }
      var bi := 0;
      while bi < |blockedCandidates|
        invariant 0 <= bi <= |blockedCandidates|
        invariant SumConsistent(this.docs)
        decreases |blockedCandidates| - bi
      {
        if !(blockedCandidates[bi] in oldMatchMap) {
          var evicted := this.PickOverflowDoc(blockedCandidates[bi]);
          if |evicted| > 0 {
            evictions := evictions + [Eviction(blockedCandidates[bi], evicted[0])];
            var cancelledPending := this.CancelPendingForQuery(evicted[0], blockedCandidates[bi]);
            if cancelledPending {
              var replacement := this.FillGap(blockedCandidates[bi]);
              retrievals := retrievals + replacement;
            }
          }
        }
        bi := bi + 1;
      }
      this.ResolvePendingForDoc(id);
      var payload := MatchPayload(id, oldState, newState, matchesOld, matchesNew, evictions);
      if HasAnyMatchChange(payload) && |retrievals| > 0 {
        events := [MatchEvent(payload), RetrievalEvent(retrievals)];
      } else if HasAnyMatchChange(payload) {
        events := [MatchEvent(payload)];
      } else if |retrievals| > 0 {
        events := [RetrievalEvent(retrievals)];
      } else {
        events := [];
      }
    }

    method ApplyDocChange(id: DocId, oldState: MaybeDocState, newState: MaybeDocState)
        returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      events := this.ApplyDocChangeDeferred(id, oldState, newState);
      var retrievalEvents := this.DrainPendingRetrievals();
      events := events + retrievalEvents;
    }

    method ProcessItemDeferred(item: StreamItem) returns (events: seq<DownstreamEvent>, queryId: QueryId)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      events := [];
      queryId := 0;
      match item
      case {:split false} SeedDocsItem(docs) =>
        {
          this.SeedDocs(docs);
        }
      case {:split false} QueryAddItem(spec) =>
        {
          queryId, events := this.AddQueryDeferred(spec);
        }
      case {:split false} QueryRemoveItem(id) =>
        {
          events := this.RemoveQueryDeferred(id);
        }
      case {:split false} DocChangeItem(id, oldState, newState) =>
        {
          events := this.ApplyDocChangeDeferred(id, oldState, newState);
        }
    }

    method ProcessItem(item: StreamItem) returns (events: seq<DownstreamEvent>, queryId: QueryId)
      requires this.Ready()
      modifies this, this.queryIndex
      ensures this.Ready()
      decreases *
    {
      events, queryId := this.ProcessItemDeferred(item);
      var retrievalEvents := this.DrainPendingRetrievals();
      events := events + retrievalEvents;
    }
  }
}

module ThunderDbStack {
  function RefInsertEntry(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    decreases es, score, id
  {
    if |es| == 0 then
      [Entry(score, id)]
    else if es[0].score == score && es[0].id == id then
      es
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      [Entry(score, id)] + es
    else
      [es[0]] + RefInsertEntry(es[1..], score, id)
  }

  function RefRemoveEntry(es: seq<Entry>, score: Score, id: DocId): seq<Entry>
    decreases es, score, id
  {
    if |es| == 0 then
      es
    else if es[0].score == score && es[0].id == id then
      es[1..]
    else if score < es[0].score || (score == es[0].score && id < es[0].id) then
      es
    else
      [es[0]] + RefRemoveEntry(es[1..], score, id)
  }

  function RefCollectRangeIds(es: seq<Entry>, minScore: Score, maxScore: Score, limit: nat): seq<DocId>
    decreases es, minScore, maxScore, limit
  {
    if |es| == 0 || limit == 0 then
      []
    else if es[0].score < minScore then
      RefCollectRangeIds(es[1..], minScore, maxScore, limit)
    else if es[0].score > maxScore then
      []
    else
      [es[0].id] + RefCollectRangeIds(es[1..], minScore, maxScore, limit - 1)
  }

  function GetScore(state: DocState): Score
    decreases state
  {
    state.scoreValue
  }

  function HasDoc(store: map<DocId, DocState>, id: DocId): bool
    decreases store, id
  {
    id in store
  }

  function LookupState(store: map<DocId, DocState>, id: DocId): MaybeDocState
    decreases store, id
  {
    if id in store then
      HasState(store[id])
    else
      NoState
  }

  function PutStoredDoc(store: map<DocId, DocState>, id: DocId, state: DocState): map<DocId, DocState>
    decreases store, id, state
  {
    store[id := state]
  }

  function RemoveStoredDoc(store: map<DocId, DocState>, id: DocId): map<DocId, DocState>
    decreases store, id
  {
    map key: int {:trigger store[key]} {:trigger key in store} | key in store && key != id :: store[key]
  }

  function ContainsId(ids: seq<DocId>, id: DocId): bool
    decreases ids, id
  {
    if |ids| == 0 then
      false
    else
      ids[0] == id || ContainsId(ids[1..], id)
  }

  function ContainsQueryId(ids: seq<QueryId>, id: QueryId): bool
    decreases ids, id
  {
    if |ids| == 0 then
      false
    else
      ids[0] == id || ContainsQueryId(ids[1..], id)
  }

  function AppendQueryIdUnique(ids: seq<QueryId>, id: QueryId): seq<QueryId>
    decreases ids, id
  {
    if ContainsQueryId(ids, id) then
      ids
    else
      ids + [id]
  }

  function AppendDocIdUnique(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if ContainsId(ids, id) then
      ids
    else
      ids + [id]
  }

  function BuildEntriesFromStore(store: seq<StoredDoc>): seq<Entry>
    decreases store
  {
    if |store| == 0 then
      []
    else
      RefInsertEntry(BuildEntriesFromStore(store[1..]), GetScore(store[0].state), store[0].id)
  }

  function VisibleForSpec(entries: seq<Entry>, spec: QuerySpec): seq<DocId>
    decreases entries, spec
  {
    RefCollectRangeIds(entries, spec.minScore, spec.maxScore, spec.limit)
  }

  function PriorityFor(score: Score, id: DocId): Priority
    decreases score, id
  {
    ((score + 1) * 1103515245 + (id + 1) * 12345) % 2147483647
  }

  function VisibleForSpecInTreap(treap: Treap, spec: QuerySpec): seq<DocId>
    requires SumConsistent(treap)
    decreases treap, spec
  {
    TreapCollectRange(treap, spec.minScore, spec.maxScore, spec.limit)
  }

  function ScoreMatchesSpec(score: Score, spec: QuerySpec): bool
    decreases score, spec
  {
    spec.minScore <= score <= spec.maxScore
  }

  function EntryBefore(score1: Score, id1: DocId, score2: Score, id2: DocId): bool
    decreases score1, id1, score2, id2
  {
    score1 < score2 || (score1 == score2 && id1 < id2)
  }

  function StateMatchesSpec(state: MaybeDocState, spec: QuerySpec): bool
    decreases state, spec
  {
    match state
    case NoState() =>
      false
    case HasState(docState) =>
      ScoreMatchesSpec(GetScore(docState), spec)
  }

  function DocWouldEnterVisible(visible: seq<DocId>, limit: nat, docState: DocState, docId: DocId, store: map<DocId, DocState>): bool
    decreases visible, limit, docState, docId, store
  {
    if limit == 0 then
      false
    else if |visible| < limit then
      true
    else
      match LookupState(store, visible[|visible| - 1]) case NoState() => false case HasState(lastState) => EntryBefore(GetScore(docState), docId, GetScore(lastState), visible[|visible| - 1])
  }

  function QueryNeedsRecompute(query: QueryRuntime, store: map<DocId, DocState>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): bool
    decreases query, store, id, oldState, newState
  {
    if ContainsId(query.visible, id) then
      true
    else
      match newState case NoState() => false case HasState(docState) => ScoreMatchesSpec(GetScore(docState), query.spec) && DocWouldEnterVisible(query.visible, query.spec.limit, docState, id, store)
  }

  function RecomputeQuery(query: QueryRuntime, treap: Treap): QueryRuntime
    requires SumConsistent(treap)
    decreases query, treap
  {
    QueryRuntime(query.id, query.spec, VisibleForSpecInTreap(treap, query.spec))
  }

  function RecomputeQueries(queries: seq<QueryRuntime>, treap: Treap): seq<QueryRuntime>
    requires SumConsistent(treap)
    decreases queries, treap
  {
    if |queries| == 0 then
      []
    else
      [RecomputeQuery(queries[0], treap)] + RecomputeQueries(queries[1..], treap)
  }

  function RemoveQueryRuntime(queries: seq<QueryRuntime>, id: QueryId): seq<QueryRuntime>
    decreases queries, id
  {
    if |queries| == 0 then
      []
    else if queries[0].id == id then
      queries[1..]
    else
      [queries[0]] + RemoveQueryRuntime(queries[1..], id)
  }

  function UpdateQueriesForDocChange(queries: seq<QueryRuntime>, treap: Treap, store: map<DocId, DocState>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): seq<QueryRuntime>
    requires SumConsistent(treap)
    decreases queries, treap, store, id, oldState, newState
  {
    if |queries| == 0 then
      []
    else if QueryNeedsRecompute(queries[0], store, id, oldState, newState) then
      [RecomputeQuery(queries[0], treap)] + UpdateQueriesForDocChange(queries[1..], treap, store, id, oldState, newState)
    else
      [queries[0]] + UpdateQueriesForDocChange(queries[1..], treap, store, id, oldState, newState)
  }

  function QueryVisible(queries: seq<QueryRuntime>, id: QueryId): seq<DocId>
    decreases queries, id
  {
    if |queries| == 0 then
      []
    else if queries[0].id == id then
      queries[0].visible
    else
      QueryVisible(queries[1..], id)
  }

  function UniqueDocIds(ids: seq<DocId>): bool
    decreases ids
  {
    if |ids| == 0 then
      true
    else
      !ContainsId(ids[1..], ids[0]) && UniqueDocIds(ids[1..])
  }

  function BuildEntriesFromStateStore(store: map<DocId, DocState>, docIds: seq<DocId>): seq<Entry>
    decreases store, docIds
  {
    if |docIds| == 0 then
      []
    else if docIds[0] in store then
      RefInsertEntry(BuildEntriesFromStateStore(store, docIds[1..]), GetScore(store[docIds[0]]), docIds[0])
    else
      BuildEntriesFromStateStore(store, docIds[1..])
  }

  function AppendDocIdIfMissing(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if ContainsId(ids, id) then
      ids
    else
      ids + [id]
  }

  function RemoveDocId(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases ids, id
  {
    if |ids| == 0 then
      []
    else if ids[0] == id then
      ids[1..]
    else
      [ids[0]] + RemoveDocId(ids[1..], id)
  }

  predicate QuerysConsistent(queries: seq<QueryRuntime>, entries: seq<Entry>)
    decreases queries, entries
  {
    if |queries| == 0 then
      true
    else
      queries[0].visible == VisibleForSpec(entries, queries[0].spec) && QuerysConsistent(queries[1..], entries)
  }

  predicate ValidState(state: EngineState)
    decreases state
  {
    UniqueDocIds(state.docIds) &&
    SumConsistent(state.treap) &&
    Entries(state.treap) == BuildEntriesFromStateStore(state.store, state.docIds) &&
    QuerysConsistent(state.queries, Entries(state.treap))
  }

  function EmptyState(): EngineState
  {
    EngineState(map[], [], Empty, [], 1)
  }

  function AddRetrievalQuery(plans: seq<RetrievalDoc>, docId: DocId, state: DocState, queryId: QueryId): seq<RetrievalDoc>
    decreases plans, docId, state, queryId
  {
    if |plans| == 0 then
      [RetrievalDoc(docId, state, [queryId])]
    else if plans[0].docId == docId then
      [RetrievalDoc(docId, state, AppendQueryIdUnique(plans[0].queries, queryId))] + plans[1..]
    else
      [plans[0]] + AddRetrievalQuery(plans[1..], docId, state, queryId)
  }

  function FirstEvicted(oldVisible: seq<DocId>, newVisible: seq<DocId>, changedId: DocId): seq<DocId>
    decreases oldVisible, newVisible, changedId
  {
    if |oldVisible| == 0 then
      []
    else if oldVisible[0] != changedId && !ContainsId(newVisible, oldVisible[0]) then
      [oldVisible[0]]
    else
      FirstEvicted(oldVisible[1..], newVisible, changedId)
  }

  function FirstAddedDoc(newVisible: seq<DocId>, oldVisible: seq<DocId>, changedId: DocId): seq<DocId>
    decreases |newVisible|
  {
    if |newVisible| == 0 then
      []
    else if newVisible[0] != changedId && !ContainsId(oldVisible, newVisible[0]) then
      [newVisible[0]]
    else
      FirstAddedDoc(newVisible[1..], oldVisible, changedId)
  }

  function BuildGapRetrievalForQuery(oldQuery: QueryRuntime, newQuery: QueryRuntime, store: map<DocId, DocState>, changedId: DocId): seq<RetrievalDoc>
    decreases oldQuery, newQuery, store, changedId
  {
    var replacement: seq<DocId> := FirstAddedDoc(newQuery.visible, oldQuery.visible, changedId);
    if ContainsId(oldQuery.visible, changedId) && !ContainsId(newQuery.visible, changedId) && |replacement| > 0 then
      match LookupState(store, replacement[0])
      case NoState() =>
        []
      case HasState(state) =>
        [RetrievalDoc(replacement[0], state, [newQuery.id])]
    else
      []
  }

  function BuildRetrievalsFromQueryDiff(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, store: map<DocId, DocState>, changedId: DocId): seq<RetrievalDoc>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else
      BuildGapRetrievalForQuery(oldQueries[0], newQueries[0], store, changedId) + BuildRetrievalsFromQueryDiff(oldQueries[1..], newQueries[1..], store, changedId)
  }

  function BuildAddQueryRetrievals(visible: seq<DocId>, store: map<DocId, DocState>, queryId: QueryId): seq<RetrievalDoc>
    decreases |visible|
  {
    if |visible| == 0 then
      []
    else
      match LookupState(store, visible[0]) case NoState() => BuildAddQueryRetrievals(visible[1..], store, queryId) case HasState(docState) => AddRetrievalQuery(BuildAddQueryRetrievals(visible[1..], store, queryId), visible[0], docState, queryId)
  }

  function BuildMatchPayload(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId, oldState: MaybeDocState, newState: MaybeDocState): MatchPayload
    decreases oldQueries, newQueries, id, oldState, newState
  {
    MatchPayload(id, oldState, newState, CollectMatchesOld(oldQueries, newQueries, id), CollectMatchesNew(oldQueries, newQueries, id), CollectEvictions(oldQueries, newQueries, id))
  }

  function CollectMatchesOld(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<QueryId>
    decreases |oldQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else if ContainsId(oldQueries[0].visible, id) then
      [oldQueries[0].id] + CollectMatchesOld(oldQueries[1..], newQueries[1..], id)
    else
      CollectMatchesOld(oldQueries[1..], newQueries[1..], id)
  }

  function CollectMatchesNew(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<QueryId>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else if ContainsId(newQueries[0].visible, id) then
      [newQueries[0].id] + CollectMatchesNew(oldQueries[1..], newQueries[1..], id)
    else
      CollectMatchesNew(oldQueries[1..], newQueries[1..], id)
  }

  function CollectEvictions(oldQueries: seq<QueryRuntime>, newQueries: seq<QueryRuntime>, id: DocId): seq<Eviction>
    decreases |newQueries|
  {
    if |oldQueries| == 0 || |newQueries| == 0 then
      []
    else
      var oldVisible: seq<DocId> := oldQueries[0].visible; if !ContainsId(oldVisible, id) && ContainsId(newQueries[0].visible, id) && |FirstEvicted(oldVisible, newQueries[0].visible, id)| > 0 then [Eviction(newQueries[0].id, FirstEvicted(oldVisible, newQueries[0].visible, id)[0])] + CollectEvictions(oldQueries[1..], newQueries[1..], id) else CollectEvictions(oldQueries[1..], newQueries[1..], id)
  }

  function HasAnyMatchChange(payload: MatchPayload): bool
    decreases payload
  {
    |payload.matchesOld| > 0 || |payload.matchesNew| > 0 || |payload.evictions| > 0
  }

  method SeedDocs(state: EngineState, docs: seq<SeedDoc>) returns (next: EngineState)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
    decreases state, docs
  {
    var store := state.store;
    var docIds := state.docIds;
    var treap := state.treap;
    var i := 0;
    while i < |docs|
      invariant 0 <= i <= |docs|
      invariant SumConsistent(treap)
      decreases |docs| - i
    {
      store := PutStoredDoc(store, docs[i].id, docs[i].state);
      docIds := AppendDocIdIfMissing(docIds, docs[i].id);
      treap := Add(treap, docs[i].state.scoreValue, docs[i].id, PriorityFor(docs[i].state.scoreValue, docs[i].id));
      i := i + 1;
    }
    next := EngineState(store, docIds, treap, RecomputeQueries(state.queries, treap), state.nextQueryId);
  }

  method AddQuery(state: EngineState, spec: QuerySpec)
      returns (next: EngineState, events: seq<DownstreamEvent>, queryId: QueryId)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
    ensures queryId == state.nextQueryId
    decreases state, spec
  {
    queryId := state.nextQueryId;
    var visible := VisibleForSpecInTreap(state.treap, spec);
    var query := QueryRuntime(queryId, spec, visible);
    next := EngineState(state.store, state.docIds, state.treap, state.queries + [query], state.nextQueryId + 1);
    var retrievals := BuildAddQueryRetrievals(visible, state.store, queryId);
    if |retrievals| == 0 {
      events := [];
    } else {
      events := [RetrievalEvent(retrievals)];
    }
  }

  method RemoveQuery(state: EngineState, id: QueryId)
      returns (next: EngineState, events: seq<DownstreamEvent>)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
    decreases state, id
  {
    next := EngineState(state.store, state.docIds, state.treap, RemoveQueryRuntime(state.queries, id), state.nextQueryId);
    events := [];
  }

  method ApplyDocChange(state: EngineState, id: DocId, oldState: MaybeDocState, newState: MaybeDocState)
      returns (next: EngineState, events: seq<DownstreamEvent>)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
    decreases state, id, oldState, newState
  {
    next := state;
    events := [];
    var store := state.store;
    var docIds := state.docIds;
    var treap := state.treap;
    if oldState.HasState? {
      var oldDoc := oldState.state;
      if newState.NoState? {
        store := RemoveStoredDoc(store, id);
        docIds := RemoveDocId(docIds, id);
      }
      treap := Remove(treap, GetScore(oldDoc), id);
    }
    if newState.HasState? {
      var newDoc := newState.state;
      store := PutStoredDoc(store, id, newDoc);
      docIds := AppendDocIdIfMissing(docIds, id);
      treap := Add(treap, GetScore(newDoc), id, PriorityFor(GetScore(newDoc), id));
    }
    var newQueries := UpdateQueriesForDocChange(state.queries, treap, store, id, oldState, newState);
    next := EngineState(store, docIds, treap, newQueries, state.nextQueryId);
    var payload := BuildMatchPayload(state.queries, newQueries, id, oldState, newState);
    var retrievals := BuildRetrievalsFromQueryDiff(state.queries, newQueries, store, id);
    if HasAnyMatchChange(payload) && |retrievals| > 0 {
      events := [MatchEvent(payload), RetrievalEvent(retrievals)];
    } else if HasAnyMatchChange(payload) {
      events := [MatchEvent(payload)];
    } else if |retrievals| > 0 {
      events := [RetrievalEvent(retrievals)];
    } else {
      events := [];
    }
  }

  method ProcessItem(state: EngineState, item: StreamItem)
      returns (next: EngineState, events: seq<DownstreamEvent>, queryId: QueryId)
    requires SumConsistent(state.treap)
    ensures SumConsistent(next.treap)
    decreases state, item
  {
    next := state;
    events := [];
    queryId := 0;
    match item
    case {:split false} SeedDocsItem(docs) =>
      {
        next := SeedDocs(state, docs);
        events := [];
      }
    case {:split false} QueryAddItem(spec) =>
      {
        next, events, queryId := AddQuery(state, spec);
      }
    case {:split false} QueryRemoveItem(id) =>
      {
        next, events := RemoveQuery(state, id);
      }
    case {:split false} DocChangeItem(id, oldState, newState) =>
      {
        next, events := ApplyDocChange(state, id, oldState, newState);
      }
  }

  function SummaryZero(): WorkerRunSummary
  {
    WorkerRunSummary(0, 0, 0, 0, 0)
  }

  function CountEvictions(evictions: seq<Eviction>): nat
    decreases evictions
  {
    |evictions|
  }

  function UpdateSummary(summary: WorkerRunSummary, events: seq<DownstreamEvent>): WorkerRunSummary
    decreases summary, events
  {
    if |events| == 0 then
      WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed + 1)
    else
      UpdateSummaryOne(WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed + 1), events)
  }

  function UpdateSummaryOne(summary: WorkerRunSummary, events: seq<DownstreamEvent>): WorkerRunSummary
    decreases |events|
  {
    if |events| == 0 then
      summary
    else
      match events[0] case MatchEvent(payload) => UpdateSummaryOne(WorkerRunSummary(summary.matchEvents + 1, summary.evictions + CountEvictions(payload.evictions), summary.retrievalBatches, summary.retrievalDocs, summary.eventsProcessed), events[1..]) case RetrievalEvent(docs) => UpdateSummaryOne(WorkerRunSummary(summary.matchEvents, summary.evictions, summary.retrievalBatches + 1, summary.retrievalDocs + |docs|, summary.eventsProcessed), events[1..])
  }

  import opened DocsIndexModel

  import opened DocsIndexTreap

  type QueryId = int

  datatype DocState = DocState(scoreValue: Score)

  datatype MaybeDocState = NoState | HasState(state: DocState)

  datatype StoredDoc = StoredDoc(id: DocId, state: DocState)

  datatype SeedDoc = SeedDoc(id: DocId, state: DocState)

  datatype QuerySpec = QuerySpec(minScore: Score, maxScore: Score, limit: nat)

  datatype QueryRuntime = QueryRuntime(id: QueryId, spec: QuerySpec, visible: seq<DocId>)

  datatype Eviction = Eviction(queryId: QueryId, docId: DocId)

  datatype MatchPayload = MatchPayload(docId: DocId, oldState: MaybeDocState, newState: MaybeDocState, matchesOld: seq<QueryId>, matchesNew: seq<QueryId>, evictions: seq<Eviction>)

  datatype RetrievalDoc = RetrievalDoc(docId: DocId, state: DocState, queries: seq<QueryId>)

  datatype DownstreamEvent = MatchEvent(payload: MatchPayload) | RetrievalEvent(docs: seq<RetrievalDoc>)

  datatype StreamItem = DocChangeItem(id: DocId, oldState: MaybeDocState, newState: MaybeDocState) | QueryAddItem(spec: QuerySpec) | QueryRemoveItem(id: QueryId) | SeedDocsItem(docs: seq<SeedDoc>)

  datatype WorkerRunSummary = WorkerRunSummary(matchEvents: nat, evictions: nat, retrievalBatches: nat, retrievalDocs: nat, eventsProcessed: nat)

  datatype EngineState = EngineState(store: map<DocId, DocState>, docIds: seq<DocId>, treap: Treap, queries: seq<QueryRuntime>, nextQueryId: QueryId)
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
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
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
namespace ThunderDbStack {

  public partial class __default {
    public static Dafny.ISequence<DocsIndexModel._IEntry> RefInsertEntry(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
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
    public static Dafny.ISequence<DocsIndexModel._IEntry> RefRemoveEntry(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger score, BigInteger id)
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
    public static Dafny.ISequence<BigInteger> RefCollectRangeIds(Dafny.ISequence<DocsIndexModel._IEntry> es, BigInteger minScore, BigInteger maxScore, BigInteger limit)
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
    public static BigInteger GetScore(BigInteger state) {
      return (state);
    }
    public static bool HasDoc(Dafny.IMap<BigInteger,BigInteger> store, BigInteger id)
    {
      return (store).Contains(id);
    }
    public static ThunderDbStack._IMaybeDocState LookupState(Dafny.IMap<BigInteger,BigInteger> store, BigInteger id)
    {
      if ((store).Contains(id)) {
        return ThunderDbStack.MaybeDocState.create_HasState(Dafny.Map<BigInteger, BigInteger>.Select(store,id));
      } else {
        return ThunderDbStack.MaybeDocState.create_NoState();
      }
    }
    public static Dafny.IMap<BigInteger,BigInteger> PutStoredDoc(Dafny.IMap<BigInteger,BigInteger> store, BigInteger id, BigInteger state)
    {
      return Dafny.Map<BigInteger, BigInteger>.Update(store, id, state);
    }
    public static Dafny.IMap<BigInteger,BigInteger> RemoveStoredDoc(Dafny.IMap<BigInteger,BigInteger> store, BigInteger id)
    {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,BigInteger>, BigInteger, Dafny.IMap<BigInteger,BigInteger>>>((_0_store, _1_id) => ((System.Func<Dafny.IMap<BigInteger,BigInteger>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,BigInteger>>();
        foreach (BigInteger _compr_0 in (_0_store).Keys.Elements) {
          BigInteger _2_key = (BigInteger)_compr_0;
          if (((_0_store).Contains(_2_key)) && ((_2_key) != (_1_id))) {
            _coll0.Add(new Dafny.Pair<BigInteger,BigInteger>(_2_key, Dafny.Map<BigInteger, BigInteger>.Select(_0_store,_2_key)));
          }
        }
        return Dafny.Map<BigInteger,BigInteger>.FromCollection(_coll0);
      }))())(store, id);
    }
    public static bool ContainsId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return false;
      } else {
        return (((ids).Select(BigInteger.Zero)) == (id)) || (ThunderDbStack.__default.ContainsId((ids).Drop(BigInteger.One), id));
      }
    }
    public static bool ContainsQueryId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return false;
      } else {
        return (((ids).Select(BigInteger.Zero)) == (id)) || (ThunderDbStack.__default.ContainsQueryId((ids).Drop(BigInteger.One), id));
      }
    }
    public static Dafny.ISequence<BigInteger> AppendQueryIdUnique(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if (ThunderDbStack.__default.ContainsQueryId(ids, id)) {
        return ids;
      } else {
        return Dafny.Sequence<BigInteger>.Concat(ids, Dafny.Sequence<BigInteger>.FromElements(id));
      }
    }
    public static Dafny.ISequence<BigInteger> AppendDocIdUnique(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if (ThunderDbStack.__default.ContainsId(ids, id)) {
        return ids;
      } else {
        return Dafny.Sequence<BigInteger>.Concat(ids, Dafny.Sequence<BigInteger>.FromElements(id));
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> BuildEntriesFromStore(Dafny.ISequence<ThunderDbStack._IStoredDoc> store) {
      if ((new BigInteger((store).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
      } else {
        return ThunderDbStack.__default.RefInsertEntry(ThunderDbStack.__default.BuildEntriesFromStore((store).Drop(BigInteger.One)), ThunderDbStack.__default.GetScore(((store).Select(BigInteger.Zero)).dtor_state), ((store).Select(BigInteger.Zero)).dtor_id);
      }
    }
    public static Dafny.ISequence<BigInteger> VisibleForSpec(Dafny.ISequence<DocsIndexModel._IEntry> entries, ThunderDbStack._IQuerySpec spec)
    {
      return ThunderDbStack.__default.RefCollectRangeIds(entries, (spec).dtor_minScore, (spec).dtor_maxScore, (spec).dtor_limit);
    }
    public static BigInteger PriorityFor(BigInteger score, BigInteger id)
    {
      return Dafny.Helpers.EuclideanModulus((((score) + (BigInteger.One)) * (new BigInteger(1103515245))) + (((id) + (BigInteger.One)) * (new BigInteger(12345))), new BigInteger(2147483647));
    }
    public static Dafny.ISequence<BigInteger> VisibleForSpecInTreap(DocsIndexTreap._ITreap treap, ThunderDbStack._IQuerySpec spec)
    {
      return DocsIndexTreap.__default.TreapCollectRange(treap, (spec).dtor_minScore, (spec).dtor_maxScore, (spec).dtor_limit);
    }
    public static bool ScoreMatchesSpec(BigInteger score, ThunderDbStack._IQuerySpec spec)
    {
      return (((spec).dtor_minScore) <= (score)) && ((score) <= ((spec).dtor_maxScore));
    }
    public static bool EntryBefore(BigInteger score1, BigInteger id1, BigInteger score2, BigInteger id2)
    {
      return ((score1) < (score2)) || (((score1) == (score2)) && ((id1) < (id2)));
    }
    public static bool StateMatchesSpec(ThunderDbStack._IMaybeDocState state, ThunderDbStack._IQuerySpec spec)
    {
      ThunderDbStack._IMaybeDocState _source0 = state;
      {
        if (_source0.is_NoState) {
          return false;
        }
      }
      {
        BigInteger _0_docState = _source0.dtor_state;
        return ThunderDbStack.__default.ScoreMatchesSpec(ThunderDbStack.__default.GetScore(_0_docState), spec);
      }
    }
    public static bool DocWouldEnterVisible(Dafny.ISequence<BigInteger> visible, BigInteger limit, BigInteger docState, BigInteger docId, Dafny.IMap<BigInteger,BigInteger> store)
    {
      if ((limit).Sign == 0) {
        return false;
      } else if ((new BigInteger((visible).Count)) < (limit)) {
        return true;
      } else {
        ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(store, (visible).Select((new BigInteger((visible).Count)) - (BigInteger.One)));
        {
          if (_source0.is_NoState) {
            return false;
          }
        }
        {
          BigInteger _0_lastState = _source0.dtor_state;
          return ThunderDbStack.__default.EntryBefore(ThunderDbStack.__default.GetScore(docState), docId, ThunderDbStack.__default.GetScore(_0_lastState), (visible).Select((new BigInteger((visible).Count)) - (BigInteger.One)));
        }
      }
    }
    public static bool QueryNeedsRecompute(ThunderDbStack._IQueryRuntime query, Dafny.IMap<BigInteger,BigInteger> store, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      if (ThunderDbStack.__default.ContainsId((query).dtor_visible, id)) {
        return true;
      } else {
        ThunderDbStack._IMaybeDocState _source0 = newState;
        {
          if (_source0.is_NoState) {
            return false;
          }
        }
        {
          BigInteger _0_docState = _source0.dtor_state;
          return (ThunderDbStack.__default.ScoreMatchesSpec(ThunderDbStack.__default.GetScore(_0_docState), (query).dtor_spec)) && (ThunderDbStack.__default.DocWouldEnterVisible((query).dtor_visible, ((query).dtor_spec).dtor_limit, _0_docState, id, store));
        }
      }
    }
    public static ThunderDbStack._IQueryRuntime RecomputeQuery(ThunderDbStack._IQueryRuntime query, DocsIndexTreap._ITreap treap)
    {
      return ThunderDbStack.QueryRuntime.create((query).dtor_id, (query).dtor_spec, ThunderDbStack.__default.VisibleForSpecInTreap(treap, (query).dtor_spec));
    }
    public static Dafny.ISequence<ThunderDbStack._IQueryRuntime> RecomputeQueries(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, DocsIndexTreap._ITreap treap)
    {
      Dafny.ISequence<ThunderDbStack._IQueryRuntime> _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(ThunderDbStack.__default.RecomputeQuery((queries).Select(BigInteger.Zero), treap)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        DocsIndexTreap._ITreap _in1 = treap;
        queries = _in0;
        treap = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IQueryRuntime> RemoveQueryRuntime(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IQueryRuntime> _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements());
      } else if ((((queries).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, (queries).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements((queries).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        BigInteger _in1 = id;
        queries = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IQueryRuntime> UpdateQueriesForDocChange(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, DocsIndexTreap._ITreap treap, Dafny.IMap<BigInteger,BigInteger> store, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      Dafny.ISequence<ThunderDbStack._IQueryRuntime> _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements());
      } else if (ThunderDbStack.__default.QueryNeedsRecompute((queries).Select(BigInteger.Zero), store, id, oldState, newState)) {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(ThunderDbStack.__default.RecomputeQuery((queries).Select(BigInteger.Zero), treap)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        DocsIndexTreap._ITreap _in1 = treap;
        Dafny.IMap<BigInteger,BigInteger> _in2 = store;
        BigInteger _in3 = id;
        ThunderDbStack._IMaybeDocState _in4 = oldState;
        ThunderDbStack._IMaybeDocState _in5 = newState;
        queries = _in0;
        treap = _in1;
        store = _in2;
        id = _in3;
        oldState = _in4;
        newState = _in5;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements((queries).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in6 = (queries).Drop(BigInteger.One);
        DocsIndexTreap._ITreap _in7 = treap;
        Dafny.IMap<BigInteger,BigInteger> _in8 = store;
        BigInteger _in9 = id;
        ThunderDbStack._IMaybeDocState _in10 = oldState;
        ThunderDbStack._IMaybeDocState _in11 = newState;
        queries = _in6;
        treap = _in7;
        store = _in8;
        id = _in9;
        oldState = _in10;
        newState = _in11;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> QueryVisible(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger id)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else if ((((queries).Select(BigInteger.Zero)).dtor_id) == (id)) {
        return ((queries).Select(BigInteger.Zero)).dtor_visible;
      } else {
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (queries).Drop(BigInteger.One);
        BigInteger _in1 = id;
        queries = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool UniqueDocIds(Dafny.ISequence<BigInteger> ids) {
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return true;
      } else {
        return (!(ThunderDbStack.__default.ContainsId((ids).Drop(BigInteger.One), (ids).Select(BigInteger.Zero)))) && (ThunderDbStack.__default.UniqueDocIds((ids).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<DocsIndexModel._IEntry> BuildEntriesFromStateStore(Dafny.IMap<BigInteger,BigInteger> store, Dafny.ISequence<BigInteger> docIds)
    {
      if ((new BigInteger((docIds).Count)).Sign == 0) {
        return Dafny.Sequence<DocsIndexModel._IEntry>.FromElements();
      } else if ((store).Contains((docIds).Select(BigInteger.Zero))) {
        return ThunderDbStack.__default.RefInsertEntry(ThunderDbStack.__default.BuildEntriesFromStateStore(store, (docIds).Drop(BigInteger.One)), ThunderDbStack.__default.GetScore(Dafny.Map<BigInteger, BigInteger>.Select(store,(docIds).Select(BigInteger.Zero))), (docIds).Select(BigInteger.Zero));
      } else {
        return ThunderDbStack.__default.BuildEntriesFromStateStore(store, (docIds).Drop(BigInteger.One));
      }
    }
    public static Dafny.ISequence<BigInteger> AppendDocIdIfMissing(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      if (ThunderDbStack.__default.ContainsId(ids, id)) {
        return ids;
      } else {
        return Dafny.Sequence<BigInteger>.Concat(ids, Dafny.Sequence<BigInteger>.FromElements(id));
      }
    }
    public static Dafny.ISequence<BigInteger> RemoveDocId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (((ids).Select(BigInteger.Zero)) == (id)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, (ids).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool QuerysConsistent(Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, Dafny.ISequence<DocsIndexModel._IEntry> entries)
    {
      if ((new BigInteger((queries).Count)).Sign == 0) {
        return true;
      } else {
        return ((((queries).Select(BigInteger.Zero)).dtor_visible).Equals(ThunderDbStack.__default.VisibleForSpec(entries, ((queries).Select(BigInteger.Zero)).dtor_spec))) && (ThunderDbStack.__default.QuerysConsistent((queries).Drop(BigInteger.One), entries));
      }
    }
    public static bool ValidState(ThunderDbStack._IEngineState state) {
      return (((ThunderDbStack.__default.UniqueDocIds((state).dtor_docIds)) && (DocsIndexTreap.__default.SumConsistent((state).dtor_treap))) && ((DocsIndexTreap.__default.Entries((state).dtor_treap)).Equals(ThunderDbStack.__default.BuildEntriesFromStateStore((state).dtor_store, (state).dtor_docIds)))) && (ThunderDbStack.__default.QuerysConsistent((state).dtor_queries, DocsIndexTreap.__default.Entries((state).dtor_treap)));
    }
    public static ThunderDbStack._IEngineState EmptyState() {
      return ThunderDbStack.EngineState.create(Dafny.Map<BigInteger, BigInteger>.FromElements(), Dafny.Sequence<BigInteger>.FromElements(), DocsIndexTreap.Treap.create_Empty(), Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(), BigInteger.One);
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> AddRetrievalQuery(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> plans, BigInteger docId, BigInteger state, BigInteger queryId)
    {
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((plans).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(docId, state, Dafny.Sequence<BigInteger>.FromElements(queryId))));
      } else if ((((plans).Select(BigInteger.Zero)).dtor_docId) == (docId)) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(docId, state, ThunderDbStack.__default.AppendQueryIdUnique(((plans).Select(BigInteger.Zero)).dtor_queries, queryId))), (plans).Drop(BigInteger.One)));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements((plans).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _in0 = (plans).Drop(BigInteger.One);
        BigInteger _in1 = docId;
        BigInteger _in2 = state;
        BigInteger _in3 = queryId;
        plans = _in0;
        docId = _in1;
        state = _in2;
        queryId = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FirstEvicted(Dafny.ISequence<BigInteger> oldVisible, Dafny.ISequence<BigInteger> newVisible, BigInteger changedId)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((oldVisible).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else if ((((oldVisible).Select(BigInteger.Zero)) != (changedId)) && (!(ThunderDbStack.__default.ContainsId(newVisible, (oldVisible).Select(BigInteger.Zero))))) {
        return Dafny.Sequence<BigInteger>.FromElements((oldVisible).Select(BigInteger.Zero));
      } else {
        Dafny.ISequence<BigInteger> _in0 = (oldVisible).Drop(BigInteger.One);
        Dafny.ISequence<BigInteger> _in1 = newVisible;
        BigInteger _in2 = changedId;
        oldVisible = _in0;
        newVisible = _in1;
        changedId = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FirstAddedDoc(Dafny.ISequence<BigInteger> newVisible, Dafny.ISequence<BigInteger> oldVisible, BigInteger changedId)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((newVisible).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else if ((((newVisible).Select(BigInteger.Zero)) != (changedId)) && (!(ThunderDbStack.__default.ContainsId(oldVisible, (newVisible).Select(BigInteger.Zero))))) {
        return Dafny.Sequence<BigInteger>.FromElements((newVisible).Select(BigInteger.Zero));
      } else {
        Dafny.ISequence<BigInteger> _in0 = (newVisible).Drop(BigInteger.One);
        Dafny.ISequence<BigInteger> _in1 = oldVisible;
        BigInteger _in2 = changedId;
        newVisible = _in0;
        oldVisible = _in1;
        changedId = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildGapRetrievalForQuery(ThunderDbStack._IQueryRuntime oldQuery, ThunderDbStack._IQueryRuntime newQuery, Dafny.IMap<BigInteger,BigInteger> store, BigInteger changedId)
    {
      Dafny.ISequence<BigInteger> _0_replacement = ThunderDbStack.__default.FirstAddedDoc((newQuery).dtor_visible, (oldQuery).dtor_visible, changedId);
      if (((ThunderDbStack.__default.ContainsId((oldQuery).dtor_visible, changedId)) && (!(ThunderDbStack.__default.ContainsId((newQuery).dtor_visible, changedId)))) && ((new BigInteger((_0_replacement).Count)).Sign == 1)) {
        ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(store, (_0_replacement).Select(BigInteger.Zero));
        {
          if (_source0.is_NoState) {
            return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
          }
        }
        {
          BigInteger _1_state = _source0.dtor_state;
          return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create((_0_replacement).Select(BigInteger.Zero), _1_state, Dafny.Sequence<BigInteger>.FromElements((newQuery).dtor_id)));
        }
      } else {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildRetrievalsFromQueryDiff(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, Dafny.IMap<BigInteger,BigInteger> store, BigInteger changedId)
    {
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_0___accumulator, ThunderDbStack.__default.BuildGapRetrievalForQuery((oldQueries).Select(BigInteger.Zero), (newQueries).Select(BigInteger.Zero), store, changedId));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
        Dafny.IMap<BigInteger,BigInteger> _in2 = store;
        BigInteger _in3 = changedId;
        oldQueries = _in0;
        newQueries = _in1;
        store = _in2;
        changedId = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IRetrievalDoc> BuildAddQueryRetrievals(Dafny.ISequence<BigInteger> visible, Dafny.IMap<BigInteger,BigInteger> store, BigInteger queryId)
    {
      if ((new BigInteger((visible).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      } else {
        ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(store, (visible).Select(BigInteger.Zero));
        {
          if (_source0.is_NoState) {
            return ThunderDbStack.__default.BuildAddQueryRetrievals((visible).Drop(BigInteger.One), store, queryId);
          }
        }
        {
          BigInteger _0_docState = _source0.dtor_state;
          return ThunderDbStack.__default.AddRetrievalQuery(ThunderDbStack.__default.BuildAddQueryRetrievals((visible).Drop(BigInteger.One), store, queryId), (visible).Select(BigInteger.Zero), _0_docState, queryId);
        }
      }
    }
    public static ThunderDbStack._IMatchPayload BuildMatchPayload(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      return ThunderDbStack.MatchPayload.create(id, oldState, newState, ThunderDbStack.__default.CollectMatchesOld(oldQueries, newQueries, id), ThunderDbStack.__default.CollectMatchesNew(oldQueries, newQueries, id), ThunderDbStack.__default.CollectEvictions(oldQueries, newQueries, id));
    }
    public static Dafny.ISequence<BigInteger> CollectMatchesOld(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (ThunderDbStack.__default.ContainsId(((oldQueries).Select(BigInteger.Zero)).dtor_visible, id)) {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((oldQueries).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
        BigInteger _in2 = id;
        oldQueries = _in0;
        newQueries = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in3 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in4 = (newQueries).Drop(BigInteger.One);
        BigInteger _in5 = id;
        oldQueries = _in3;
        newQueries = _in4;
        id = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> CollectMatchesNew(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (ThunderDbStack.__default.ContainsId(((newQueries).Select(BigInteger.Zero)).dtor_visible, id)) {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((newQueries).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
        BigInteger _in2 = id;
        oldQueries = _in0;
        newQueries = _in1;
        id = _in2;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in3 = (oldQueries).Drop(BigInteger.One);
        Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in4 = (newQueries).Drop(BigInteger.One);
        BigInteger _in5 = id;
        oldQueries = _in3;
        newQueries = _in4;
        id = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbStack._IEviction> CollectEvictions(Dafny.ISequence<ThunderDbStack._IQueryRuntime> oldQueries, Dafny.ISequence<ThunderDbStack._IQueryRuntime> newQueries, BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IEviction> _0___accumulator = Dafny.Sequence<ThunderDbStack._IEviction>.FromElements();
    TAIL_CALL_START: ;
      if (((new BigInteger((oldQueries).Count)).Sign == 0) || ((new BigInteger((newQueries).Count)).Sign == 0)) {
        return Dafny.Sequence<ThunderDbStack._IEviction>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements());
      } else {
        Dafny.ISequence<BigInteger> _1_oldVisible = ((oldQueries).Select(BigInteger.Zero)).dtor_visible;
        if (((!(ThunderDbStack.__default.ContainsId(_1_oldVisible, id))) && (ThunderDbStack.__default.ContainsId(((newQueries).Select(BigInteger.Zero)).dtor_visible, id))) && ((new BigInteger((ThunderDbStack.__default.FirstEvicted(_1_oldVisible, ((newQueries).Select(BigInteger.Zero)).dtor_visible, id)).Count)).Sign == 1)) {
          _0___accumulator = Dafny.Sequence<ThunderDbStack._IEviction>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements(ThunderDbStack.Eviction.create(((newQueries).Select(BigInteger.Zero)).dtor_id, (ThunderDbStack.__default.FirstEvicted(_1_oldVisible, ((newQueries).Select(BigInteger.Zero)).dtor_visible, id)).Select(BigInteger.Zero))));
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in0 = (oldQueries).Drop(BigInteger.One);
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in1 = (newQueries).Drop(BigInteger.One);
          BigInteger _in2 = id;
          oldQueries = _in0;
          newQueries = _in1;
          id = _in2;
          goto TAIL_CALL_START;
        } else {
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in3 = (oldQueries).Drop(BigInteger.One);
          Dafny.ISequence<ThunderDbStack._IQueryRuntime> _in4 = (newQueries).Drop(BigInteger.One);
          BigInteger _in5 = id;
          oldQueries = _in3;
          newQueries = _in4;
          id = _in5;
          goto TAIL_CALL_START;
        }
      }
    }
    public static bool HasAnyMatchChange(ThunderDbStack._IMatchPayload payload) {
      return (((new BigInteger(((payload).dtor_matchesOld).Count)).Sign == 1) || ((new BigInteger(((payload).dtor_matchesNew).Count)).Sign == 1)) || ((new BigInteger(((payload).dtor_evictions).Count)).Sign == 1);
    }
    public static ThunderDbStack._IEngineState SeedDocs(ThunderDbStack._IEngineState state, Dafny.ISequence<ThunderDbStack._ISeedDoc> docs)
    {
      ThunderDbStack._IEngineState next = ThunderDbStack.EngineState.Default();
      Dafny.IMap<BigInteger,BigInteger> _0_store;
      _0_store = (state).dtor_store;
      Dafny.ISequence<BigInteger> _1_docIds;
      _1_docIds = (state).dtor_docIds;
      DocsIndexTreap._ITreap _2_treap;
      _2_treap = (state).dtor_treap;
      BigInteger _3_i;
      _3_i = BigInteger.Zero;
      while ((_3_i) < (new BigInteger((docs).Count))) {
        _0_store = ThunderDbStack.__default.PutStoredDoc(_0_store, ((docs).Select(_3_i)).dtor_id, ((docs).Select(_3_i)).dtor_state);
        _1_docIds = ThunderDbStack.__default.AppendDocIdIfMissing(_1_docIds, ((docs).Select(_3_i)).dtor_id);
        _2_treap = DocsIndexTreap.__default.Add(_2_treap, (((docs).Select(_3_i)).dtor_state), ((docs).Select(_3_i)).dtor_id, ThunderDbStack.__default.PriorityFor((((docs).Select(_3_i)).dtor_state), ((docs).Select(_3_i)).dtor_id));
        _3_i = (_3_i) + (BigInteger.One);
      }
      next = ThunderDbStack.EngineState.create(_0_store, _1_docIds, _2_treap, ThunderDbStack.__default.RecomputeQueries((state).dtor_queries, _2_treap), (state).dtor_nextQueryId);
      return next;
    }
    public static void AddQuery(ThunderDbStack._IEngineState state, ThunderDbStack._IQuerySpec spec, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events, out BigInteger queryId)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      queryId = BigInteger.Zero;
      queryId = (state).dtor_nextQueryId;
      Dafny.ISequence<BigInteger> _0_visible;
      _0_visible = ThunderDbStack.__default.VisibleForSpecInTreap((state).dtor_treap, spec);
      ThunderDbStack._IQueryRuntime _1_query;
      _1_query = ThunderDbStack.QueryRuntime.create(queryId, spec, _0_visible);
      next = ThunderDbStack.EngineState.create((state).dtor_store, (state).dtor_docIds, (state).dtor_treap, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Concat((state).dtor_queries, Dafny.Sequence<ThunderDbStack._IQueryRuntime>.FromElements(_1_query)), ((state).dtor_nextQueryId) + (BigInteger.One));
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _2_retrievals;
      _2_retrievals = ThunderDbStack.__default.BuildAddQueryRetrievals(_0_visible, (state).dtor_store, queryId);
      if ((new BigInteger((_2_retrievals).Count)).Sign == 0) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      } else {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_2_retrievals));
      }
    }
    public static void RemoveQuery(ThunderDbStack._IEngineState state, BigInteger id, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      next = ThunderDbStack.EngineState.create((state).dtor_store, (state).dtor_docIds, (state).dtor_treap, ThunderDbStack.__default.RemoveQueryRuntime((state).dtor_queries, id), (state).dtor_nextQueryId);
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
    }
    public static void ApplyDocChange(ThunderDbStack._IEngineState state, BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      next = state;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      Dafny.IMap<BigInteger,BigInteger> _0_store;
      _0_store = (state).dtor_store;
      Dafny.ISequence<BigInteger> _1_docIds;
      _1_docIds = (state).dtor_docIds;
      DocsIndexTreap._ITreap _2_treap;
      _2_treap = (state).dtor_treap;
      if ((oldState).is_HasState) {
        BigInteger _3_oldDoc;
        _3_oldDoc = (oldState).dtor_state;
        if ((newState).is_NoState) {
          _0_store = ThunderDbStack.__default.RemoveStoredDoc(_0_store, id);
          _1_docIds = ThunderDbStack.__default.RemoveDocId(_1_docIds, id);
        }
        _2_treap = DocsIndexTreap.__default.Remove(_2_treap, ThunderDbStack.__default.GetScore(_3_oldDoc), id);
      }
      if ((newState).is_HasState) {
        BigInteger _4_newDoc;
        _4_newDoc = (newState).dtor_state;
        _0_store = ThunderDbStack.__default.PutStoredDoc(_0_store, id, _4_newDoc);
        _1_docIds = ThunderDbStack.__default.AppendDocIdIfMissing(_1_docIds, id);
        _2_treap = DocsIndexTreap.__default.Add(_2_treap, ThunderDbStack.__default.GetScore(_4_newDoc), id, ThunderDbStack.__default.PriorityFor(ThunderDbStack.__default.GetScore(_4_newDoc), id));
      }
      Dafny.ISequence<ThunderDbStack._IQueryRuntime> _5_newQueries;
      _5_newQueries = ThunderDbStack.__default.UpdateQueriesForDocChange((state).dtor_queries, _2_treap, _0_store, id, oldState, newState);
      next = ThunderDbStack.EngineState.create(_0_store, _1_docIds, _2_treap, _5_newQueries, (state).dtor_nextQueryId);
      ThunderDbStack._IMatchPayload _6_payload;
      _6_payload = ThunderDbStack.__default.BuildMatchPayload((state).dtor_queries, _5_newQueries, id, oldState, newState);
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _7_retrievals;
      _7_retrievals = ThunderDbStack.__default.BuildRetrievalsFromQueryDiff((state).dtor_queries, _5_newQueries, _0_store, id);
      if ((ThunderDbStack.__default.HasAnyMatchChange(_6_payload)) && ((new BigInteger((_7_retrievals).Count)).Sign == 1)) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(_6_payload), ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_7_retrievals));
      } else if (ThunderDbStack.__default.HasAnyMatchChange(_6_payload)) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(_6_payload));
      } else if ((new BigInteger((_7_retrievals).Count)).Sign == 1) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_7_retrievals));
      } else {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      }
    }
    public static void ProcessItem(ThunderDbStack._IEngineState state, ThunderDbStack._IStreamItem item, out ThunderDbStack._IEngineState next, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events, out BigInteger queryId)
    {
      next = ThunderDbStack.EngineState.Default();
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      queryId = BigInteger.Zero;
      next = state;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      queryId = BigInteger.Zero;
      ThunderDbStack._IStreamItem _source0 = item;
      {
        if (_source0.is_SeedDocsItem) {
          Dafny.ISequence<ThunderDbStack._ISeedDoc> _0_docs = _source0.dtor_docs;
          {
            ThunderDbStack._IEngineState _out0;
            _out0 = ThunderDbStack.__default.SeedDocs(state, _0_docs);
            next = _out0;
            events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_QueryAddItem) {
          ThunderDbStack._IQuerySpec _1_spec = _source0.dtor_spec;
          {
            ThunderDbStack._IEngineState _out1;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out2;
            BigInteger _out3;
            ThunderDbStack.__default.AddQuery(state, _1_spec, out _out1, out _out2, out _out3);
            next = _out1;
            events = _out2;
            queryId = _out3;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_QueryRemoveItem) {
          BigInteger _2_id = _source0.dtor_id;
          {
            ThunderDbStack._IEngineState _out4;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out5;
            ThunderDbStack.__default.RemoveQuery(state, _2_id, out _out4, out _out5);
            next = _out4;
            events = _out5;
          }
          goto after_match0;
        }
      }
      {
        BigInteger _3_id = _source0.dtor_id;
        ThunderDbStack._IMaybeDocState _4_oldState = _source0.dtor_oldState;
        ThunderDbStack._IMaybeDocState _5_newState = _source0.dtor_newState;
        {
          ThunderDbStack._IEngineState _out6;
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out7;
          ThunderDbStack.__default.ApplyDocChange(state, _3_id, _4_oldState, _5_newState, out _out6, out _out7);
          next = _out6;
          events = _out7;
        }
      }
    after_match0: ;
    }
    public static ThunderDbStack._IWorkerRunSummary SummaryZero() {
      return ThunderDbStack.WorkerRunSummary.create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    }
    public static BigInteger CountEvictions(Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return new BigInteger((evictions).Count);
    }
    public static ThunderDbStack._IWorkerRunSummary UpdateSummary(ThunderDbStack._IWorkerRunSummary summary, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      if ((new BigInteger((events).Count)).Sign == 0) {
        return ThunderDbStack.WorkerRunSummary.create((summary).dtor_matchEvents, (summary).dtor_evictions, (summary).dtor_retrievalBatches, (summary).dtor_retrievalDocs, ((summary).dtor_eventsProcessed) + (BigInteger.One));
      } else {
        return ThunderDbStack.__default.UpdateSummaryOne(ThunderDbStack.WorkerRunSummary.create((summary).dtor_matchEvents, (summary).dtor_evictions, (summary).dtor_retrievalBatches, (summary).dtor_retrievalDocs, ((summary).dtor_eventsProcessed) + (BigInteger.One)), events);
      }
    }
    public static ThunderDbStack._IWorkerRunSummary UpdateSummaryOne(ThunderDbStack._IWorkerRunSummary summary, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((events).Count)).Sign == 0) {
        return summary;
      } else {
        ThunderDbStack._IDownstreamEvent _source0 = (events).Select(BigInteger.Zero);
        {
          if (_source0.is_MatchEvent) {
            ThunderDbStack._IMatchPayload _0_payload = _source0.dtor_payload;
            ThunderDbStack._IWorkerRunSummary _in0 = ThunderDbStack.WorkerRunSummary.create(((summary).dtor_matchEvents) + (BigInteger.One), ((summary).dtor_evictions) + (ThunderDbStack.__default.CountEvictions((_0_payload).dtor_evictions)), (summary).dtor_retrievalBatches, (summary).dtor_retrievalDocs, (summary).dtor_eventsProcessed);
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _in1 = (events).Drop(BigInteger.One);
            summary = _in0;
            events = _in1;
            goto TAIL_CALL_START;
          }
        }
        {
          Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _1_docs = _source0.dtor_docs;
          ThunderDbStack._IWorkerRunSummary _in2 = ThunderDbStack.WorkerRunSummary.create((summary).dtor_matchEvents, (summary).dtor_evictions, ((summary).dtor_retrievalBatches) + (BigInteger.One), ((summary).dtor_retrievalDocs) + (new BigInteger((_1_docs).Count)), (summary).dtor_eventsProcessed);
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _in3 = (events).Drop(BigInteger.One);
          summary = _in2;
          events = _in3;
          goto TAIL_CALL_START;
        }
      }
    }
  }

  public interface _IDocState {
    bool is_DocState { get; }
    BigInteger dtor_scoreValue { get; }
  }
  public class DocState : _IDocState {
    public readonly BigInteger _scoreValue;
    public DocState(BigInteger scoreValue) {
      this._scoreValue = scoreValue;
    }
    public static BigInteger DowncastClone(BigInteger _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DocState;
      return oth != null && this._scoreValue == oth._scoreValue;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._scoreValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DocState.DocState";
      s += "(";
      s += Dafny.Helpers.ToString(this._scoreValue);
      s += ")";
      return s;
    }
    private static readonly BigInteger theDefault = BigInteger.Zero;
    public static BigInteger Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDocState create(BigInteger scoreValue) {
      return new DocState(scoreValue);
    }
    public static _IDocState create_DocState(BigInteger scoreValue) {
      return create(scoreValue);
    }
    public bool is_DocState { get { return true; } }
    public BigInteger dtor_scoreValue {
      get {
        return this._scoreValue;
      }
    }
  }

  public interface _IMaybeDocState {
    bool is_NoState { get; }
    bool is_HasState { get; }
    BigInteger dtor_state { get; }
    _IMaybeDocState DowncastClone();
  }
  public abstract class MaybeDocState : _IMaybeDocState {
    public MaybeDocState() {
    }
    private static readonly ThunderDbStack._IMaybeDocState theDefault = create_NoState();
    public static ThunderDbStack._IMaybeDocState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState>(ThunderDbStack.MaybeDocState.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IMaybeDocState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaybeDocState create_NoState() {
      return new MaybeDocState_NoState();
    }
    public static _IMaybeDocState create_HasState(BigInteger state) {
      return new MaybeDocState_HasState(state);
    }
    public bool is_NoState { get { return this is MaybeDocState_NoState; } }
    public bool is_HasState { get { return this is MaybeDocState_HasState; } }
    public BigInteger dtor_state {
      get {
        var d = this;
        return ((MaybeDocState_HasState)d)._state;
      }
    }
    public abstract _IMaybeDocState DowncastClone();
  }
  public class MaybeDocState_NoState : MaybeDocState {
    public MaybeDocState_NoState() : base() {
    }
    public override _IMaybeDocState DowncastClone() {
      if (this is _IMaybeDocState dt) { return dt; }
      return new MaybeDocState_NoState();
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MaybeDocState_NoState;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MaybeDocState.NoState";
      return s;
    }
  }
  public class MaybeDocState_HasState : MaybeDocState {
    public readonly BigInteger _state;
    public MaybeDocState_HasState(BigInteger state) : base() {
      this._state = state;
    }
    public override _IMaybeDocState DowncastClone() {
      if (this is _IMaybeDocState dt) { return dt; }
      return new MaybeDocState_HasState(_state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MaybeDocState_HasState;
      return oth != null && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MaybeDocState.HasState";
      s += "(";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
  }

  public interface _IStoredDoc {
    bool is_StoredDoc { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_state { get; }
    _IStoredDoc DowncastClone();
  }
  public class StoredDoc : _IStoredDoc {
    public readonly BigInteger _id;
    public readonly BigInteger _state;
    public StoredDoc(BigInteger id, BigInteger state) {
      this._id = id;
      this._state = state;
    }
    public _IStoredDoc DowncastClone() {
      if (this is _IStoredDoc dt) { return dt; }
      return new StoredDoc(_id, _state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StoredDoc;
      return oth != null && this._id == oth._id && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StoredDoc.StoredDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IStoredDoc theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IStoredDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IStoredDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IStoredDoc>(ThunderDbStack.StoredDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IStoredDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStoredDoc create(BigInteger id, BigInteger state) {
      return new StoredDoc(id, state);
    }
    public static _IStoredDoc create_StoredDoc(BigInteger id, BigInteger state) {
      return create(id, state);
    }
    public bool is_StoredDoc { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
  }

  public interface _ISeedDoc {
    bool is_SeedDoc { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_state { get; }
    _ISeedDoc DowncastClone();
  }
  public class SeedDoc : _ISeedDoc {
    public readonly BigInteger _id;
    public readonly BigInteger _state;
    public SeedDoc(BigInteger id, BigInteger state) {
      this._id = id;
      this._state = state;
    }
    public _ISeedDoc DowncastClone() {
      if (this is _ISeedDoc dt) { return dt; }
      return new SeedDoc(_id, _state);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.SeedDoc;
      return oth != null && this._id == oth._id && this._state == oth._state;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.SeedDoc.SeedDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._ISeedDoc theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._ISeedDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc>(ThunderDbStack.SeedDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._ISeedDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISeedDoc create(BigInteger id, BigInteger state) {
      return new SeedDoc(id, state);
    }
    public static _ISeedDoc create_SeedDoc(BigInteger id, BigInteger state) {
      return create(id, state);
    }
    public bool is_SeedDoc { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
  }

  public interface _IQuerySpec {
    bool is_QuerySpec { get; }
    BigInteger dtor_minScore { get; }
    BigInteger dtor_maxScore { get; }
    BigInteger dtor_limit { get; }
    _IQuerySpec DowncastClone();
  }
  public class QuerySpec : _IQuerySpec {
    public readonly BigInteger _minScore;
    public readonly BigInteger _maxScore;
    public readonly BigInteger _limit;
    public QuerySpec(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      this._minScore = minScore;
      this._maxScore = maxScore;
      this._limit = limit;
    }
    public _IQuerySpec DowncastClone() {
      if (this is _IQuerySpec dt) { return dt; }
      return new QuerySpec(_minScore, _maxScore, _limit);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.QuerySpec;
      return oth != null && this._minScore == oth._minScore && this._maxScore == oth._maxScore && this._limit == oth._limit;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._minScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maxScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._limit));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.QuerySpec.QuerySpec";
      s += "(";
      s += Dafny.Helpers.ToString(this._minScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maxScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._limit);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IQuerySpec theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IQuerySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec>(ThunderDbStack.QuerySpec.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IQuerySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQuerySpec create(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      return new QuerySpec(minScore, maxScore, limit);
    }
    public static _IQuerySpec create_QuerySpec(BigInteger minScore, BigInteger maxScore, BigInteger limit) {
      return create(minScore, maxScore, limit);
    }
    public bool is_QuerySpec { get { return true; } }
    public BigInteger dtor_minScore {
      get {
        return this._minScore;
      }
    }
    public BigInteger dtor_maxScore {
      get {
        return this._maxScore;
      }
    }
    public BigInteger dtor_limit {
      get {
        return this._limit;
      }
    }
  }

  public interface _IQueryRuntime {
    bool is_QueryRuntime { get; }
    BigInteger dtor_id { get; }
    ThunderDbStack._IQuerySpec dtor_spec { get; }
    Dafny.ISequence<BigInteger> dtor_visible { get; }
    _IQueryRuntime DowncastClone();
  }
  public class QueryRuntime : _IQueryRuntime {
    public readonly BigInteger _id;
    public readonly ThunderDbStack._IQuerySpec _spec;
    public readonly Dafny.ISequence<BigInteger> _visible;
    public QueryRuntime(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<BigInteger> visible) {
      this._id = id;
      this._spec = spec;
      this._visible = visible;
    }
    public _IQueryRuntime DowncastClone() {
      if (this is _IQueryRuntime dt) { return dt; }
      return new QueryRuntime(_id, _spec, _visible);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.QueryRuntime;
      return oth != null && this._id == oth._id && object.Equals(this._spec, oth._spec) && object.Equals(this._visible, oth._visible);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._spec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visible));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.QueryRuntime.QueryRuntime";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._spec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._visible);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IQueryRuntime theDefault = create(BigInteger.Zero, ThunderDbStack.QuerySpec.Default(), Dafny.Sequence<BigInteger>.Empty);
    public static ThunderDbStack._IQueryRuntime Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IQueryRuntime> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IQueryRuntime>(ThunderDbStack.QueryRuntime.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IQueryRuntime> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryRuntime create(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<BigInteger> visible) {
      return new QueryRuntime(id, spec, visible);
    }
    public static _IQueryRuntime create_QueryRuntime(BigInteger id, ThunderDbStack._IQuerySpec spec, Dafny.ISequence<BigInteger> visible) {
      return create(id, spec, visible);
    }
    public bool is_QueryRuntime { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public ThunderDbStack._IQuerySpec dtor_spec {
      get {
        return this._spec;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_visible {
      get {
        return this._visible;
      }
    }
  }

  public interface _IEviction {
    bool is_Eviction { get; }
    BigInteger dtor_queryId { get; }
    BigInteger dtor_docId { get; }
    _IEviction DowncastClone();
  }
  public class Eviction : _IEviction {
    public readonly BigInteger _queryId;
    public readonly BigInteger _docId;
    public Eviction(BigInteger queryId, BigInteger docId) {
      this._queryId = queryId;
      this._docId = docId;
    }
    public _IEviction DowncastClone() {
      if (this is _IEviction dt) { return dt; }
      return new Eviction(_queryId, _docId);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.Eviction;
      return oth != null && this._queryId == oth._queryId && this._docId == oth._docId;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queryId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.Eviction.Eviction";
      s += "(";
      s += Dafny.Helpers.ToString(this._queryId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._docId);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IEviction theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IEviction Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IEviction> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IEviction>(ThunderDbStack.Eviction.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IEviction> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEviction create(BigInteger queryId, BigInteger docId) {
      return new Eviction(queryId, docId);
    }
    public static _IEviction create_Eviction(BigInteger queryId, BigInteger docId) {
      return create(queryId, docId);
    }
    public bool is_Eviction { get { return true; } }
    public BigInteger dtor_queryId {
      get {
        return this._queryId;
      }
    }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
  }

  public interface _IMatchPayload {
    bool is_MatchPayload { get; }
    BigInteger dtor_docId { get; }
    ThunderDbStack._IMaybeDocState dtor_oldState { get; }
    ThunderDbStack._IMaybeDocState dtor_newState { get; }
    Dafny.ISequence<BigInteger> dtor_matchesOld { get; }
    Dafny.ISequence<BigInteger> dtor_matchesNew { get; }
    Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions { get; }
    _IMatchPayload DowncastClone();
  }
  public class MatchPayload : _IMatchPayload {
    public readonly BigInteger _docId;
    public readonly ThunderDbStack._IMaybeDocState _oldState;
    public readonly ThunderDbStack._IMaybeDocState _newState;
    public readonly Dafny.ISequence<BigInteger> _matchesOld;
    public readonly Dafny.ISequence<BigInteger> _matchesNew;
    public readonly Dafny.ISequence<ThunderDbStack._IEviction> _evictions;
    public MatchPayload(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      this._docId = docId;
      this._oldState = oldState;
      this._newState = newState;
      this._matchesOld = matchesOld;
      this._matchesNew = matchesNew;
      this._evictions = evictions;
    }
    public _IMatchPayload DowncastClone() {
      if (this is _IMatchPayload dt) { return dt; }
      return new MatchPayload(_docId, _oldState, _newState, _matchesOld, _matchesNew, _evictions);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.MatchPayload;
      return oth != null && this._docId == oth._docId && object.Equals(this._oldState, oth._oldState) && object.Equals(this._newState, oth._newState) && object.Equals(this._matchesOld, oth._matchesOld) && object.Equals(this._matchesNew, oth._matchesNew) && object.Equals(this._evictions, oth._evictions);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._oldState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._newState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchesOld));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchesNew));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._evictions));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.MatchPayload.MatchPayload";
      s += "(";
      s += Dafny.Helpers.ToString(this._docId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._oldState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._newState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._matchesOld);
      s += ", ";
      s += Dafny.Helpers.ToString(this._matchesNew);
      s += ", ";
      s += Dafny.Helpers.ToString(this._evictions);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IMatchPayload theDefault = create(BigInteger.Zero, ThunderDbStack.MaybeDocState.Default(), ThunderDbStack.MaybeDocState.Default(), Dafny.Sequence<BigInteger>.Empty, Dafny.Sequence<BigInteger>.Empty, Dafny.Sequence<ThunderDbStack._IEviction>.Empty);
    public static ThunderDbStack._IMatchPayload Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload>(ThunderDbStack.MatchPayload.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IMatchPayload> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMatchPayload create(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return new MatchPayload(docId, oldState, newState, matchesOld, matchesNew, evictions);
    }
    public static _IMatchPayload create_MatchPayload(BigInteger docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState, Dafny.ISequence<BigInteger> matchesOld, Dafny.ISequence<BigInteger> matchesNew, Dafny.ISequence<ThunderDbStack._IEviction> evictions) {
      return create(docId, oldState, newState, matchesOld, matchesNew, evictions);
    }
    public bool is_MatchPayload { get { return true; } }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_oldState {
      get {
        return this._oldState;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_newState {
      get {
        return this._newState;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_matchesOld {
      get {
        return this._matchesOld;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_matchesNew {
      get {
        return this._matchesNew;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IEviction> dtor_evictions {
      get {
        return this._evictions;
      }
    }
  }

  public interface _IRetrievalDoc {
    bool is_RetrievalDoc { get; }
    BigInteger dtor_docId { get; }
    BigInteger dtor_state { get; }
    Dafny.ISequence<BigInteger> dtor_queries { get; }
    _IRetrievalDoc DowncastClone();
  }
  public class RetrievalDoc : _IRetrievalDoc {
    public readonly BigInteger _docId;
    public readonly BigInteger _state;
    public readonly Dafny.ISequence<BigInteger> _queries;
    public RetrievalDoc(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      this._docId = docId;
      this._state = state;
      this._queries = queries;
    }
    public _IRetrievalDoc DowncastClone() {
      if (this is _IRetrievalDoc dt) { return dt; }
      return new RetrievalDoc(_docId, _state, _queries);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.RetrievalDoc;
      return oth != null && this._docId == oth._docId && this._state == oth._state && object.Equals(this._queries, oth._queries);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._state));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queries));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.RetrievalDoc.RetrievalDoc";
      s += "(";
      s += Dafny.Helpers.ToString(this._docId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._state);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queries);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IRetrievalDoc theDefault = create(BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<BigInteger>.Empty);
    public static ThunderDbStack._IRetrievalDoc Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc>(ThunderDbStack.RetrievalDoc.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IRetrievalDoc> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRetrievalDoc create(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      return new RetrievalDoc(docId, state, queries);
    }
    public static _IRetrievalDoc create_RetrievalDoc(BigInteger docId, BigInteger state, Dafny.ISequence<BigInteger> queries) {
      return create(docId, state, queries);
    }
    public bool is_RetrievalDoc { get { return true; } }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
    public BigInteger dtor_state {
      get {
        return this._state;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_queries {
      get {
        return this._queries;
      }
    }
  }

  public interface _IDownstreamEvent {
    bool is_MatchEvent { get; }
    bool is_RetrievalEvent { get; }
    ThunderDbStack._IMatchPayload dtor_payload { get; }
    Dafny.ISequence<ThunderDbStack._IRetrievalDoc> dtor_docs { get; }
    _IDownstreamEvent DowncastClone();
  }
  public abstract class DownstreamEvent : _IDownstreamEvent {
    public DownstreamEvent() {
    }
    private static readonly ThunderDbStack._IDownstreamEvent theDefault = create_MatchEvent(ThunderDbStack.MatchPayload.Default());
    public static ThunderDbStack._IDownstreamEvent Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent>(ThunderDbStack.DownstreamEvent.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IDownstreamEvent> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDownstreamEvent create_MatchEvent(ThunderDbStack._IMatchPayload payload) {
      return new DownstreamEvent_MatchEvent(payload);
    }
    public static _IDownstreamEvent create_RetrievalEvent(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs) {
      return new DownstreamEvent_RetrievalEvent(docs);
    }
    public bool is_MatchEvent { get { return this is DownstreamEvent_MatchEvent; } }
    public bool is_RetrievalEvent { get { return this is DownstreamEvent_RetrievalEvent; } }
    public ThunderDbStack._IMatchPayload dtor_payload {
      get {
        var d = this;
        return ((DownstreamEvent_MatchEvent)d)._payload;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IRetrievalDoc> dtor_docs {
      get {
        var d = this;
        return ((DownstreamEvent_RetrievalEvent)d)._docs;
      }
    }
    public abstract _IDownstreamEvent DowncastClone();
  }
  public class DownstreamEvent_MatchEvent : DownstreamEvent {
    public readonly ThunderDbStack._IMatchPayload _payload;
    public DownstreamEvent_MatchEvent(ThunderDbStack._IMatchPayload payload) : base() {
      this._payload = payload;
    }
    public override _IDownstreamEvent DowncastClone() {
      if (this is _IDownstreamEvent dt) { return dt; }
      return new DownstreamEvent_MatchEvent(_payload);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DownstreamEvent_MatchEvent;
      return oth != null && object.Equals(this._payload, oth._payload);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._payload));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DownstreamEvent.MatchEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._payload);
      s += ")";
      return s;
    }
  }
  public class DownstreamEvent_RetrievalEvent : DownstreamEvent {
    public readonly Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _docs;
    public DownstreamEvent_RetrievalEvent(Dafny.ISequence<ThunderDbStack._IRetrievalDoc> docs) : base() {
      this._docs = docs;
    }
    public override _IDownstreamEvent DowncastClone() {
      if (this is _IDownstreamEvent dt) { return dt; }
      return new DownstreamEvent_RetrievalEvent(_docs);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.DownstreamEvent_RetrievalEvent;
      return oth != null && object.Equals(this._docs, oth._docs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.DownstreamEvent.RetrievalEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._docs);
      s += ")";
      return s;
    }
  }

  public interface _IStreamItem {
    bool is_DocChangeItem { get; }
    bool is_QueryAddItem { get; }
    bool is_QueryRemoveItem { get; }
    bool is_SeedDocsItem { get; }
    BigInteger dtor_id { get; }
    ThunderDbStack._IMaybeDocState dtor_oldState { get; }
    ThunderDbStack._IMaybeDocState dtor_newState { get; }
    ThunderDbStack._IQuerySpec dtor_spec { get; }
    Dafny.ISequence<ThunderDbStack._ISeedDoc> dtor_docs { get; }
    _IStreamItem DowncastClone();
  }
  public abstract class StreamItem : _IStreamItem {
    public StreamItem() {
    }
    private static readonly ThunderDbStack._IStreamItem theDefault = create_DocChangeItem(BigInteger.Zero, ThunderDbStack.MaybeDocState.Default(), ThunderDbStack.MaybeDocState.Default());
    public static ThunderDbStack._IStreamItem Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IStreamItem> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IStreamItem>(ThunderDbStack.StreamItem.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IStreamItem> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStreamItem create_DocChangeItem(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState) {
      return new StreamItem_DocChangeItem(id, oldState, newState);
    }
    public static _IStreamItem create_QueryAddItem(ThunderDbStack._IQuerySpec spec) {
      return new StreamItem_QueryAddItem(spec);
    }
    public static _IStreamItem create_QueryRemoveItem(BigInteger id) {
      return new StreamItem_QueryRemoveItem(id);
    }
    public static _IStreamItem create_SeedDocsItem(Dafny.ISequence<ThunderDbStack._ISeedDoc> docs) {
      return new StreamItem_SeedDocsItem(docs);
    }
    public bool is_DocChangeItem { get { return this is StreamItem_DocChangeItem; } }
    public bool is_QueryAddItem { get { return this is StreamItem_QueryAddItem; } }
    public bool is_QueryRemoveItem { get { return this is StreamItem_QueryRemoveItem; } }
    public bool is_SeedDocsItem { get { return this is StreamItem_SeedDocsItem; } }
    public BigInteger dtor_id {
      get {
        var d = this;
        if (d is StreamItem_DocChangeItem) { return ((StreamItem_DocChangeItem)d)._id; }
        return ((StreamItem_QueryRemoveItem)d)._id;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_oldState {
      get {
        var d = this;
        return ((StreamItem_DocChangeItem)d)._oldState;
      }
    }
    public ThunderDbStack._IMaybeDocState dtor_newState {
      get {
        var d = this;
        return ((StreamItem_DocChangeItem)d)._newState;
      }
    }
    public ThunderDbStack._IQuerySpec dtor_spec {
      get {
        var d = this;
        return ((StreamItem_QueryAddItem)d)._spec;
      }
    }
    public Dafny.ISequence<ThunderDbStack._ISeedDoc> dtor_docs {
      get {
        var d = this;
        return ((StreamItem_SeedDocsItem)d)._docs;
      }
    }
    public abstract _IStreamItem DowncastClone();
  }
  public class StreamItem_DocChangeItem : StreamItem {
    public readonly BigInteger _id;
    public readonly ThunderDbStack._IMaybeDocState _oldState;
    public readonly ThunderDbStack._IMaybeDocState _newState;
    public StreamItem_DocChangeItem(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState) : base() {
      this._id = id;
      this._oldState = oldState;
      this._newState = newState;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_DocChangeItem(_id, _oldState, _newState);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_DocChangeItem;
      return oth != null && this._id == oth._id && object.Equals(this._oldState, oth._oldState) && object.Equals(this._newState, oth._newState);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._oldState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._newState));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.DocChangeItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._oldState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._newState);
      s += ")";
      return s;
    }
  }
  public class StreamItem_QueryAddItem : StreamItem {
    public readonly ThunderDbStack._IQuerySpec _spec;
    public StreamItem_QueryAddItem(ThunderDbStack._IQuerySpec spec) : base() {
      this._spec = spec;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_QueryAddItem(_spec);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_QueryAddItem;
      return oth != null && object.Equals(this._spec, oth._spec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._spec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.QueryAddItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._spec);
      s += ")";
      return s;
    }
  }
  public class StreamItem_QueryRemoveItem : StreamItem {
    public readonly BigInteger _id;
    public StreamItem_QueryRemoveItem(BigInteger id) : base() {
      this._id = id;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_QueryRemoveItem(_id);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_QueryRemoveItem;
      return oth != null && this._id == oth._id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.QueryRemoveItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
  }
  public class StreamItem_SeedDocsItem : StreamItem {
    public readonly Dafny.ISequence<ThunderDbStack._ISeedDoc> _docs;
    public StreamItem_SeedDocsItem(Dafny.ISequence<ThunderDbStack._ISeedDoc> docs) : base() {
      this._docs = docs;
    }
    public override _IStreamItem DowncastClone() {
      if (this is _IStreamItem dt) { return dt; }
      return new StreamItem_SeedDocsItem(_docs);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.StreamItem_SeedDocsItem;
      return oth != null && object.Equals(this._docs, oth._docs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.StreamItem.SeedDocsItem";
      s += "(";
      s += Dafny.Helpers.ToString(this._docs);
      s += ")";
      return s;
    }
  }

  public interface _IWorkerRunSummary {
    bool is_WorkerRunSummary { get; }
    BigInteger dtor_matchEvents { get; }
    BigInteger dtor_evictions { get; }
    BigInteger dtor_retrievalBatches { get; }
    BigInteger dtor_retrievalDocs { get; }
    BigInteger dtor_eventsProcessed { get; }
    _IWorkerRunSummary DowncastClone();
  }
  public class WorkerRunSummary : _IWorkerRunSummary {
    public readonly BigInteger _matchEvents;
    public readonly BigInteger _evictions;
    public readonly BigInteger _retrievalBatches;
    public readonly BigInteger _retrievalDocs;
    public readonly BigInteger _eventsProcessed;
    public WorkerRunSummary(BigInteger matchEvents, BigInteger evictions, BigInteger retrievalBatches, BigInteger retrievalDocs, BigInteger eventsProcessed) {
      this._matchEvents = matchEvents;
      this._evictions = evictions;
      this._retrievalBatches = retrievalBatches;
      this._retrievalDocs = retrievalDocs;
      this._eventsProcessed = eventsProcessed;
    }
    public _IWorkerRunSummary DowncastClone() {
      if (this is _IWorkerRunSummary dt) { return dt; }
      return new WorkerRunSummary(_matchEvents, _evictions, _retrievalBatches, _retrievalDocs, _eventsProcessed);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.WorkerRunSummary;
      return oth != null && this._matchEvents == oth._matchEvents && this._evictions == oth._evictions && this._retrievalBatches == oth._retrievalBatches && this._retrievalDocs == oth._retrievalDocs && this._eventsProcessed == oth._eventsProcessed;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchEvents));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._evictions));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retrievalBatches));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retrievalDocs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._eventsProcessed));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.WorkerRunSummary.WorkerRunSummary";
      s += "(";
      s += Dafny.Helpers.ToString(this._matchEvents);
      s += ", ";
      s += Dafny.Helpers.ToString(this._evictions);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retrievalBatches);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retrievalDocs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._eventsProcessed);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IWorkerRunSummary theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbStack._IWorkerRunSummary Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IWorkerRunSummary> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IWorkerRunSummary>(ThunderDbStack.WorkerRunSummary.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IWorkerRunSummary> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWorkerRunSummary create(BigInteger matchEvents, BigInteger evictions, BigInteger retrievalBatches, BigInteger retrievalDocs, BigInteger eventsProcessed) {
      return new WorkerRunSummary(matchEvents, evictions, retrievalBatches, retrievalDocs, eventsProcessed);
    }
    public static _IWorkerRunSummary create_WorkerRunSummary(BigInteger matchEvents, BigInteger evictions, BigInteger retrievalBatches, BigInteger retrievalDocs, BigInteger eventsProcessed) {
      return create(matchEvents, evictions, retrievalBatches, retrievalDocs, eventsProcessed);
    }
    public bool is_WorkerRunSummary { get { return true; } }
    public BigInteger dtor_matchEvents {
      get {
        return this._matchEvents;
      }
    }
    public BigInteger dtor_evictions {
      get {
        return this._evictions;
      }
    }
    public BigInteger dtor_retrievalBatches {
      get {
        return this._retrievalBatches;
      }
    }
    public BigInteger dtor_retrievalDocs {
      get {
        return this._retrievalDocs;
      }
    }
    public BigInteger dtor_eventsProcessed {
      get {
        return this._eventsProcessed;
      }
    }
  }

  public interface _IEngineState {
    bool is_EngineState { get; }
    Dafny.IMap<BigInteger,BigInteger> dtor_store { get; }
    Dafny.ISequence<BigInteger> dtor_docIds { get; }
    DocsIndexTreap._ITreap dtor_treap { get; }
    Dafny.ISequence<ThunderDbStack._IQueryRuntime> dtor_queries { get; }
    BigInteger dtor_nextQueryId { get; }
    _IEngineState DowncastClone();
  }
  public class EngineState : _IEngineState {
    public readonly Dafny.IMap<BigInteger,BigInteger> _store;
    public readonly Dafny.ISequence<BigInteger> _docIds;
    public readonly DocsIndexTreap._ITreap _treap;
    public readonly Dafny.ISequence<ThunderDbStack._IQueryRuntime> _queries;
    public readonly BigInteger _nextQueryId;
    public EngineState(Dafny.IMap<BigInteger,BigInteger> store, Dafny.ISequence<BigInteger> docIds, DocsIndexTreap._ITreap treap, Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger nextQueryId) {
      this._store = store;
      this._docIds = docIds;
      this._treap = treap;
      this._queries = queries;
      this._nextQueryId = nextQueryId;
    }
    public _IEngineState DowncastClone() {
      if (this is _IEngineState dt) { return dt; }
      return new EngineState(_store, _docIds, _treap, _queries, _nextQueryId);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbStack.EngineState;
      return oth != null && object.Equals(this._store, oth._store) && object.Equals(this._docIds, oth._docIds) && object.Equals(this._treap, oth._treap) && object.Equals(this._queries, oth._queries) && this._nextQueryId == oth._nextQueryId;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._store));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docIds));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._treap));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queries));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nextQueryId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbStack.EngineState.EngineState";
      s += "(";
      s += Dafny.Helpers.ToString(this._store);
      s += ", ";
      s += Dafny.Helpers.ToString(this._docIds);
      s += ", ";
      s += Dafny.Helpers.ToString(this._treap);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queries);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nextQueryId);
      s += ")";
      return s;
    }
    private static readonly ThunderDbStack._IEngineState theDefault = create(Dafny.Map<BigInteger, BigInteger>.Empty, Dafny.Sequence<BigInteger>.Empty, DocsIndexTreap.Treap.Default(), Dafny.Sequence<ThunderDbStack._IQueryRuntime>.Empty, BigInteger.Zero);
    public static ThunderDbStack._IEngineState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbStack._IEngineState> _TYPE = new Dafny.TypeDescriptor<ThunderDbStack._IEngineState>(ThunderDbStack.EngineState.Default());
    public static Dafny.TypeDescriptor<ThunderDbStack._IEngineState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEngineState create(Dafny.IMap<BigInteger,BigInteger> store, Dafny.ISequence<BigInteger> docIds, DocsIndexTreap._ITreap treap, Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger nextQueryId) {
      return new EngineState(store, docIds, treap, queries, nextQueryId);
    }
    public static _IEngineState create_EngineState(Dafny.IMap<BigInteger,BigInteger> store, Dafny.ISequence<BigInteger> docIds, DocsIndexTreap._ITreap treap, Dafny.ISequence<ThunderDbStack._IQueryRuntime> queries, BigInteger nextQueryId) {
      return create(store, docIds, treap, queries, nextQueryId);
    }
    public bool is_EngineState { get { return true; } }
    public Dafny.IMap<BigInteger,BigInteger> dtor_store {
      get {
        return this._store;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_docIds {
      get {
        return this._docIds;
      }
    }
    public DocsIndexTreap._ITreap dtor_treap {
      get {
        return this._treap;
      }
    }
    public Dafny.ISequence<ThunderDbStack._IQueryRuntime> dtor_queries {
      get {
        return this._queries;
      }
    }
    public BigInteger dtor_nextQueryId {
      get {
        return this._nextQueryId;
      }
    }
  }
} // end of namespace ThunderDbStack
namespace ThunderDbMutable {

  public partial class __default {
    public static BigInteger MaxInt(BigInteger a, BigInteger b)
    {
      if ((a) >= (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static BigInteger MaxScore(BigInteger a, BigInteger b)
    {
      if ((a) >= (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> InsertQueryIndexEntry(Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> items, ThunderDbMutable._IQueryIndexEntry entry)
    {
      Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _0___accumulator = Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((items).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements(entry));
      } else if ((((entry).dtor_baseScore) < (((items).Select(BigInteger.Zero)).dtor_baseScore)) || ((((entry).dtor_baseScore) == (((items).Select(BigInteger.Zero)).dtor_baseScore)) && (((entry).dtor_id) < (((items).Select(BigInteger.Zero)).dtor_id)))) {
        return Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.Concat(Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements(entry), items));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements((items).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _in0 = (items).Drop(BigInteger.One);
        ThunderDbMutable._IQueryIndexEntry _in1 = entry;
        items = _in0;
        entry = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> RemoveQueryIndexEntry(Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> items, BigInteger id, BigInteger baseScore, BigInteger maxCap)
    {
      Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _0___accumulator = Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((items).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements());
      } else if ((((((items).Select(BigInteger.Zero)).dtor_id) == (id)) && ((((items).Select(BigInteger.Zero)).dtor_baseScore) == (baseScore))) && ((((items).Select(BigInteger.Zero)).dtor_maxCap) == (maxCap))) {
        return Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.Concat(_0___accumulator, (items).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements((items).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _in0 = (items).Drop(BigInteger.One);
        BigInteger _in1 = id;
        BigInteger _in2 = baseScore;
        BigInteger _in3 = maxCap;
        items = _in0;
        id = _in1;
        baseScore = _in2;
        maxCap = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger MaxBaseScore(Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> items) {
      if ((new BigInteger((items).Count)).Sign == 0) {
        return ThunderDbMutable.__default.NegInfInt;
      } else {
        return ThunderDbMutable.__default.MaxInt(((items).Select(BigInteger.Zero)).dtor_baseScore, ThunderDbMutable.__default.MaxBaseScore((items).Drop(BigInteger.One)));
      }
    }
    public static BigInteger MaxCapScore(Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> items) {
      if ((new BigInteger((items).Count)).Sign == 0) {
        return ThunderDbMutable.__default.NegInfScore;
      } else {
        return ThunderDbMutable.__default.MaxScore(((items).Select(BigInteger.Zero)).dtor_maxCap, ThunderDbMutable.__default.MaxCapScore((items).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<BigInteger> CollectLocalIds(Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> items, BigInteger accHere, BigInteger cutoff, BigInteger @value)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((items).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (((((items).Select(BigInteger.Zero)).dtor_maxCap) >= (@value)) && (((((items).Select(BigInteger.Zero)).dtor_baseScore) + (accHere)) > (cutoff))) {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements(((items).Select(BigInteger.Zero)).dtor_id));
        Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _in0 = (items).Drop(BigInteger.One);
        BigInteger _in1 = accHere;
        BigInteger _in2 = cutoff;
        BigInteger _in3 = @value;
        items = _in0;
        accHere = _in1;
        cutoff = _in2;
        @value = _in3;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _in4 = (items).Drop(BigInteger.One);
        BigInteger _in5 = accHere;
        BigInteger _in6 = cutoff;
        BigInteger _in7 = @value;
        items = _in4;
        accHere = _in5;
        cutoff = _in6;
        @value = _in7;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> UniqueConcatQueryIds(Dafny.ISequence<BigInteger> left, Dafny.ISequence<BigInteger> right)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((right).Count)).Sign == 0) {
        return left;
      } else {
        Dafny.ISequence<BigInteger> _in0 = ThunderDbStack.__default.AppendQueryIdUnique(left, (right).Select(BigInteger.Zero));
        Dafny.ISequence<BigInteger> _in1 = (right).Drop(BigInteger.One);
        left = _in0;
        right = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> RemoveQueryId(Dafny.ISequence<BigInteger> ids, BigInteger id)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ids).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (((ids).Select(BigInteger.Zero)) == (id)) {
        return Dafny.Sequence<BigInteger>.Concat(_0___accumulator, (ids).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(_0___accumulator, Dafny.Sequence<BigInteger>.FromElements((ids).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (ids).Drop(BigInteger.One);
        BigInteger _in1 = id;
        ids = _in0;
        id = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> RemovePendingRetrieval(Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> pending, BigInteger docId, BigInteger queryId)
    {
      Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> _0___accumulator = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((pending).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements());
      } else if (((((pending).Select(BigInteger.Zero)).dtor_docId) == (docId)) && ((((pending).Select(BigInteger.Zero)).dtor_queryId) == (queryId))) {
        return Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.Concat(_0___accumulator, (pending).Drop(BigInteger.One));
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements((pending).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> _in0 = (pending).Drop(BigInteger.One);
        BigInteger _in1 = docId;
        BigInteger _in2 = queryId;
        pending = _in0;
        docId = _in1;
        queryId = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> RemovePendingRetrievalsForDoc(Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> pending, BigInteger docId)
    {
      Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> _0___accumulator = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((pending).Count)).Sign == 0) {
        return Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements());
      } else if ((((pending).Select(BigInteger.Zero)).dtor_docId) == (docId)) {
        Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> _in0 = (pending).Drop(BigInteger.One);
        BigInteger _in1 = docId;
        pending = _in0;
        docId = _in1;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.Concat(_0___accumulator, Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements((pending).Select(BigInteger.Zero)));
        Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> _in2 = (pending).Drop(BigInteger.One);
        BigInteger _in3 = docId;
        pending = _in2;
        docId = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger QueryNodeCount(ThunderDbMutable._IQueryTree tree) {
      if ((tree).is_QEmpty) {
        return BigInteger.Zero;
      } else {
        return ((BigInteger.One) + (ThunderDbMutable.__default.QueryNodeCount((tree).dtor_left))) + (ThunderDbMutable.__default.QueryNodeCount((tree).dtor_right));
      }
    }
    public static BigInteger QuerySubMax(ThunderDbMutable._IQueryTree tree) {
      if ((tree).is_QEmpty) {
        return ThunderDbMutable.__default.NegInfInt;
      } else {
        return (tree).dtor_subtreeMax;
      }
    }
    public static BigInteger QuerySubCap(ThunderDbMutable._IQueryTree tree) {
      if ((tree).is_QEmpty) {
        return ThunderDbMutable.__default.NegInfScore;
      } else {
        return (tree).dtor_subtreeMaxCap;
      }
    }
    public static BigInteger QueryPriorityForKey(BigInteger key) {
      return Dafny.Helpers.EuclideanModulus((((key) + (BigInteger.One)) * (new BigInteger(1103515245))) + (new BigInteger(12345)), new BigInteger(2147483647));
    }
    public static ThunderDbMutable._IQueryTree QueryPush(ThunderDbMutable._IQueryTree tree) {
      if (((tree).dtor_add).Sign == 0) {
        return tree;
      } else {
        ThunderDbMutable._IQueryTree _0_left2 = ((((tree).dtor_left).is_QEmpty) ? (ThunderDbMutable.QueryTree.create_QEmpty()) : (ThunderDbMutable.QueryTree.create_QNode(((tree).dtor_left).dtor_key, ((tree).dtor_left).dtor_prio, (((tree).dtor_left).dtor_add) + ((tree).dtor_add), ((tree).dtor_left).dtor_localAdd, ((tree).dtor_left).dtor_items, (((((tree).dtor_left).dtor_subtreeMax) == (ThunderDbMutable.__default.NegInfInt)) ? (ThunderDbMutable.__default.NegInfInt) : ((((tree).dtor_left).dtor_subtreeMax) + ((tree).dtor_add))), ((tree).dtor_left).dtor_localMaxCap, ((tree).dtor_left).dtor_subtreeMaxCap, ((tree).dtor_left).dtor_left, ((tree).dtor_left).dtor_right)));
        ThunderDbMutable._IQueryTree _1_right2 = ((((tree).dtor_right).is_QEmpty) ? (ThunderDbMutable.QueryTree.create_QEmpty()) : (ThunderDbMutable.QueryTree.create_QNode(((tree).dtor_right).dtor_key, ((tree).dtor_right).dtor_prio, (((tree).dtor_right).dtor_add) + ((tree).dtor_add), ((tree).dtor_right).dtor_localAdd, ((tree).dtor_right).dtor_items, (((((tree).dtor_right).dtor_subtreeMax) == (ThunderDbMutable.__default.NegInfInt)) ? (ThunderDbMutable.__default.NegInfInt) : ((((tree).dtor_right).dtor_subtreeMax) + ((tree).dtor_add))), ((tree).dtor_right).dtor_localMaxCap, ((tree).dtor_right).dtor_subtreeMaxCap, ((tree).dtor_right).dtor_left, ((tree).dtor_right).dtor_right)));
        return ThunderDbMutable.QueryTree.create_QNode((tree).dtor_key, (tree).dtor_prio, BigInteger.Zero, ((tree).dtor_localAdd) + ((tree).dtor_add), (tree).dtor_items, (tree).dtor_subtreeMax, (tree).dtor_localMaxCap, (tree).dtor_subtreeMaxCap, _0_left2, _1_right2);
      }
    }
    public static ThunderDbMutable._IQueryTree QueryPull(ThunderDbMutable._IQueryTree tree) {
      BigInteger _0_localCap = ThunderDbMutable.__default.MaxCapScore((tree).dtor_items);
      BigInteger _1_localMax = (((new BigInteger(((tree).dtor_items).Count)).Sign == 0) ? (ThunderDbMutable.__default.NegInfInt) : ((ThunderDbMutable.__default.MaxBaseScore((tree).dtor_items)) + ((tree).dtor_localAdd)));
      BigInteger _2_merged = ThunderDbMutable.__default.MaxInt(_1_localMax, ThunderDbMutable.__default.MaxInt(ThunderDbMutable.__default.QuerySubMax((tree).dtor_left), ThunderDbMutable.__default.QuerySubMax((tree).dtor_right)));
      return ThunderDbMutable.QueryTree.create_QNode((tree).dtor_key, (tree).dtor_prio, (tree).dtor_add, (tree).dtor_localAdd, (tree).dtor_items, (((_2_merged) == (ThunderDbMutable.__default.NegInfInt)) ? (ThunderDbMutable.__default.NegInfInt) : (((tree).dtor_add) + (_2_merged))), _0_localCap, ThunderDbMutable.__default.MaxScore(_0_localCap, ThunderDbMutable.__default.MaxScore(ThunderDbMutable.__default.QuerySubCap((tree).dtor_left), ThunderDbMutable.__default.QuerySubCap((tree).dtor_right))), (tree).dtor_left, (tree).dtor_right);
    }
    public static ThunderDbMutable._IQueryTree QueryRotateRight(ThunderDbMutable._IQueryTree tree) {
      ThunderDbMutable._IQueryTree _0_pushed = ThunderDbMutable.__default.QueryPush(tree);
      ThunderDbMutable._IQueryTree _1_leftPushed = ThunderDbMutable.__default.QueryPush((_0_pushed).dtor_left);
      ThunderDbMutable._IQueryTree _2_demoted = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_pushed).dtor_key, (_0_pushed).dtor_prio, (_0_pushed).dtor_add, (_0_pushed).dtor_localAdd, (_0_pushed).dtor_items, BigInteger.Zero, (_0_pushed).dtor_localMaxCap, (_0_pushed).dtor_subtreeMaxCap, (_1_leftPushed).dtor_right, (_0_pushed).dtor_right));
      return ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_1_leftPushed).dtor_key, (_1_leftPushed).dtor_prio, (_1_leftPushed).dtor_add, (_1_leftPushed).dtor_localAdd, (_1_leftPushed).dtor_items, BigInteger.Zero, (_1_leftPushed).dtor_localMaxCap, (_1_leftPushed).dtor_subtreeMaxCap, (_1_leftPushed).dtor_left, _2_demoted));
    }
    public static ThunderDbMutable._IQueryTree QueryRotateLeft(ThunderDbMutable._IQueryTree tree) {
      ThunderDbMutable._IQueryTree _0_pushed = ThunderDbMutable.__default.QueryPush(tree);
      ThunderDbMutable._IQueryTree _1_rightPushed = ThunderDbMutable.__default.QueryPush((_0_pushed).dtor_right);
      ThunderDbMutable._IQueryTree _2_demoted = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_pushed).dtor_key, (_0_pushed).dtor_prio, (_0_pushed).dtor_add, (_0_pushed).dtor_localAdd, (_0_pushed).dtor_items, BigInteger.Zero, (_0_pushed).dtor_localMaxCap, (_0_pushed).dtor_subtreeMaxCap, (_0_pushed).dtor_left, (_1_rightPushed).dtor_left));
      return ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_1_rightPushed).dtor_key, (_1_rightPushed).dtor_prio, (_1_rightPushed).dtor_add, (_1_rightPushed).dtor_localAdd, (_1_rightPushed).dtor_items, BigInteger.Zero, (_1_rightPushed).dtor_localMaxCap, (_1_rightPushed).dtor_subtreeMaxCap, _2_demoted, (_1_rightPushed).dtor_right));
    }
    public static ThunderDbMutable._IQueryTreePair QuerySplitByKey(ThunderDbMutable._IQueryTree tree, BigInteger key)
    {
      ThunderDbMutable._IQueryTreePair pair = ThunderDbMutable.QueryTreePair.Default();
      if ((tree).is_QEmpty) {
        pair = ThunderDbMutable.QueryTreePair.create(ThunderDbMutable.QueryTree.create_QEmpty(), ThunderDbMutable.QueryTree.create_QEmpty());
      } else {
        ThunderDbMutable._IQueryTree _0_pushed;
        _0_pushed = ThunderDbMutable.__default.QueryPush(tree);
        if ((key) < ((_0_pushed).dtor_key)) {
          ThunderDbMutable._IQueryTreePair _1_nextPair;
          ThunderDbMutable._IQueryTreePair _out0;
          _out0 = ThunderDbMutable.__default.QuerySplitByKey((_0_pushed).dtor_left, key);
          _1_nextPair = _out0;
          pair = ThunderDbMutable.QueryTreePair.create((_1_nextPair).dtor_left, ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_pushed).dtor_key, (_0_pushed).dtor_prio, (_0_pushed).dtor_add, (_0_pushed).dtor_localAdd, (_0_pushed).dtor_items, BigInteger.Zero, (_0_pushed).dtor_localMaxCap, (_0_pushed).dtor_subtreeMaxCap, (_1_nextPair).dtor_right, (_0_pushed).dtor_right)));
        } else {
          ThunderDbMutable._IQueryTreePair _2_nextPair;
          ThunderDbMutable._IQueryTreePair _out1;
          _out1 = ThunderDbMutable.__default.QuerySplitByKey((_0_pushed).dtor_right, key);
          _2_nextPair = _out1;
          pair = ThunderDbMutable.QueryTreePair.create(ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_pushed).dtor_key, (_0_pushed).dtor_prio, (_0_pushed).dtor_add, (_0_pushed).dtor_localAdd, (_0_pushed).dtor_items, BigInteger.Zero, (_0_pushed).dtor_localMaxCap, (_0_pushed).dtor_subtreeMaxCap, (_0_pushed).dtor_left, (_2_nextPair).dtor_left)), (_2_nextPair).dtor_right);
        }
      }
      return pair;
    }
    public static ThunderDbMutable._IQueryTree QueryMerge(ThunderDbMutable._IQueryTree leftTree, ThunderDbMutable._IQueryTree rightTree)
    {
      ThunderDbMutable._IQueryTree result = ThunderDbMutable.QueryTree.Default();
      if ((leftTree).is_QEmpty) {
        result = rightTree;
      } else if ((rightTree).is_QEmpty) {
        result = leftTree;
      } else {
        ThunderDbMutable._IQueryTree _0_leftPushed;
        _0_leftPushed = ThunderDbMutable.__default.QueryPush(leftTree);
        ThunderDbMutable._IQueryTree _1_rightPushed;
        _1_rightPushed = ThunderDbMutable.__default.QueryPush(rightTree);
        if (((_0_leftPushed).dtor_prio) > ((_1_rightPushed).dtor_prio)) {
          ThunderDbMutable._IQueryTree _2_mergedRight;
          ThunderDbMutable._IQueryTree _out0;
          _out0 = ThunderDbMutable.__default.QueryMerge((_0_leftPushed).dtor_right, _1_rightPushed);
          _2_mergedRight = _out0;
          result = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_leftPushed).dtor_key, (_0_leftPushed).dtor_prio, (_0_leftPushed).dtor_add, (_0_leftPushed).dtor_localAdd, (_0_leftPushed).dtor_items, BigInteger.Zero, (_0_leftPushed).dtor_localMaxCap, (_0_leftPushed).dtor_subtreeMaxCap, (_0_leftPushed).dtor_left, _2_mergedRight));
        } else {
          ThunderDbMutable._IQueryTree _3_mergedLeft;
          ThunderDbMutable._IQueryTree _out1;
          _out1 = ThunderDbMutable.__default.QueryMerge(_0_leftPushed, (_1_rightPushed).dtor_left);
          _3_mergedLeft = _out1;
          result = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_1_rightPushed).dtor_key, (_1_rightPushed).dtor_prio, (_1_rightPushed).dtor_add, (_1_rightPushed).dtor_localAdd, (_1_rightPushed).dtor_items, BigInteger.Zero, (_1_rightPushed).dtor_localMaxCap, (_1_rightPushed).dtor_subtreeMaxCap, _3_mergedLeft, (_1_rightPushed).dtor_right));
        }
      }
      return result;
    }
    public static ThunderDbMutable._IQueryTree QueryInsert(ThunderDbMutable._IQueryTree tree, BigInteger key, BigInteger id, BigInteger effectiveScore, BigInteger maxCap, BigInteger accAdd)
    {
      ThunderDbMutable._IQueryTree result = ThunderDbMutable.QueryTree.Default();
      if ((tree).is_QEmpty) {
        result = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode(key, ThunderDbMutable.__default.QueryPriorityForKey(key), BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<ThunderDbMutable._IQueryIndexEntry>.FromElements(ThunderDbMutable.QueryIndexEntry.create(id, (effectiveScore) - (accAdd), maxCap)), BigInteger.Zero, ThunderDbMutable.__default.NegInfScore, ThunderDbMutable.__default.NegInfScore, ThunderDbMutable.QueryTree.create_QEmpty(), ThunderDbMutable.QueryTree.create_QEmpty()));
      } else if ((key) == ((tree).dtor_key)) {
        result = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((tree).dtor_key, (tree).dtor_prio, (tree).dtor_add, (tree).dtor_localAdd, ThunderDbMutable.__default.InsertQueryIndexEntry((tree).dtor_items, ThunderDbMutable.QueryIndexEntry.create(id, (((effectiveScore) - (accAdd)) - ((tree).dtor_add)) - ((tree).dtor_localAdd), maxCap)), BigInteger.Zero, (tree).dtor_localMaxCap, (tree).dtor_subtreeMaxCap, (tree).dtor_left, (tree).dtor_right));
      } else if ((key) < ((tree).dtor_key)) {
        ThunderDbMutable._IQueryTree _0_left2;
        ThunderDbMutable._IQueryTree _out0;
        _out0 = ThunderDbMutable.__default.QueryInsert((tree).dtor_left, key, id, effectiveScore, maxCap, (accAdd) + ((tree).dtor_add));
        _0_left2 = _out0;
        ThunderDbMutable._IQueryTree _1_current;
        _1_current = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((tree).dtor_key, (tree).dtor_prio, (tree).dtor_add, (tree).dtor_localAdd, (tree).dtor_items, BigInteger.Zero, (tree).dtor_localMaxCap, (tree).dtor_subtreeMaxCap, _0_left2, (tree).dtor_right));
        if (((_0_left2).is_QNode) && (((_0_left2).dtor_prio) > ((tree).dtor_prio))) {
          result = ThunderDbMutable.__default.QueryRotateRight(_1_current);
        } else {
          result = _1_current;
        }
      } else {
        ThunderDbMutable._IQueryTree _2_right2;
        ThunderDbMutable._IQueryTree _out1;
        _out1 = ThunderDbMutable.__default.QueryInsert((tree).dtor_right, key, id, effectiveScore, maxCap, (accAdd) + ((tree).dtor_add));
        _2_right2 = _out1;
        ThunderDbMutable._IQueryTree _3_current;
        _3_current = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((tree).dtor_key, (tree).dtor_prio, (tree).dtor_add, (tree).dtor_localAdd, (tree).dtor_items, BigInteger.Zero, (tree).dtor_localMaxCap, (tree).dtor_subtreeMaxCap, (tree).dtor_left, _2_right2));
        if (((_2_right2).is_QNode) && (((_2_right2).dtor_prio) > ((tree).dtor_prio))) {
          result = ThunderDbMutable.__default.QueryRotateLeft(_3_current);
        } else {
          result = _3_current;
        }
      }
      return result;
    }
    public static ThunderDbMutable._IQueryTree QueryRemove(ThunderDbMutable._IQueryTree tree, BigInteger key, BigInteger id, BigInteger baseScore, BigInteger maxCap)
    {
      ThunderDbMutable._IQueryTree result = ThunderDbMutable.QueryTree.Default();
      if ((tree).is_QEmpty) {
        result = ThunderDbMutable.QueryTree.create_QEmpty();
      } else {
        ThunderDbMutable._IQueryTree _0_pushed;
        _0_pushed = ThunderDbMutable.__default.QueryPush(tree);
        if ((key) == ((_0_pushed).dtor_key)) {
          Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _1_items2;
          _1_items2 = ThunderDbMutable.__default.RemoveQueryIndexEntry((_0_pushed).dtor_items, id, baseScore, maxCap);
          if ((new BigInteger((_1_items2).Count)).Sign == 0) {
            ThunderDbMutable._IQueryTree _out0;
            _out0 = ThunderDbMutable.__default.QueryMerge((_0_pushed).dtor_left, (_0_pushed).dtor_right);
            result = _out0;
          } else {
            result = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_pushed).dtor_key, (_0_pushed).dtor_prio, (_0_pushed).dtor_add, (_0_pushed).dtor_localAdd, _1_items2, BigInteger.Zero, (_0_pushed).dtor_localMaxCap, (_0_pushed).dtor_subtreeMaxCap, (_0_pushed).dtor_left, (_0_pushed).dtor_right));
          }
        } else if ((key) < ((_0_pushed).dtor_key)) {
          ThunderDbMutable._IQueryTree _2_left2;
          ThunderDbMutable._IQueryTree _out1;
          _out1 = ThunderDbMutable.__default.QueryRemove((_0_pushed).dtor_left, key, id, baseScore, maxCap);
          _2_left2 = _out1;
          result = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_pushed).dtor_key, (_0_pushed).dtor_prio, (_0_pushed).dtor_add, (_0_pushed).dtor_localAdd, (_0_pushed).dtor_items, BigInteger.Zero, (_0_pushed).dtor_localMaxCap, (_0_pushed).dtor_subtreeMaxCap, _2_left2, (_0_pushed).dtor_right));
        } else {
          ThunderDbMutable._IQueryTree _3_right2;
          ThunderDbMutable._IQueryTree _out2;
          _out2 = ThunderDbMutable.__default.QueryRemove((_0_pushed).dtor_right, key, id, baseScore, maxCap);
          _3_right2 = _out2;
          result = ThunderDbMutable.__default.QueryPull(ThunderDbMutable.QueryTree.create_QNode((_0_pushed).dtor_key, (_0_pushed).dtor_prio, (_0_pushed).dtor_add, (_0_pushed).dtor_localAdd, (_0_pushed).dtor_items, BigInteger.Zero, (_0_pushed).dtor_localMaxCap, (_0_pushed).dtor_subtreeMaxCap, (_0_pushed).dtor_left, _3_right2));
        }
      }
      return result;
    }
    public static Dafny.ISequence<BigInteger> QueryCollectForValue(ThunderDbMutable._IQueryTree tree, BigInteger accAdd, BigInteger cutoff, BigInteger @value)
    {
      Dafny.ISequence<BigInteger> @out = Dafny.Sequence<BigInteger>.Empty;
      if (((tree).is_QEmpty) || (((tree).dtor_subtreeMaxCap) < (@value))) {
        @out = Dafny.Sequence<BigInteger>.FromElements();
      } else {
        BigInteger _0_effSubMax;
        if (((tree).dtor_subtreeMax) == (ThunderDbMutable.__default.NegInfInt)) {
          _0_effSubMax = ThunderDbMutable.__default.NegInfInt;
        } else {
          _0_effSubMax = ((tree).dtor_subtreeMax) + (accAdd);
        }
        if (((_0_effSubMax) == (ThunderDbMutable.__default.NegInfInt)) || ((_0_effSubMax) <= (cutoff))) {
          @out = Dafny.Sequence<BigInteger>.FromElements();
        } else {
          BigInteger _1_childAcc;
          _1_childAcc = (accAdd) + ((tree).dtor_add);
          if (((tree).dtor_key) > (@value)) {
            Dafny.ISequence<BigInteger> _out0;
            _out0 = ThunderDbMutable.__default.QueryCollectForValue((tree).dtor_left, _1_childAcc, cutoff, @value);
            @out = _out0;
          } else {
            Dafny.ISequence<BigInteger> _2_leftOut;
            Dafny.ISequence<BigInteger> _out1;
            _out1 = ThunderDbMutable.__default.QueryCollectForValue((tree).dtor_left, _1_childAcc, cutoff, @value);
            _2_leftOut = _out1;
            Dafny.ISequence<BigInteger> _3_rightOut;
            Dafny.ISequence<BigInteger> _out2;
            _out2 = ThunderDbMutable.__default.QueryCollectForValue((tree).dtor_right, _1_childAcc, cutoff, @value);
            _3_rightOut = _out2;
            @out = Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.Concat(_2_leftOut, ThunderDbMutable.__default.CollectLocalIds((tree).dtor_items, (_1_childAcc) + ((tree).dtor_localAdd), cutoff, @value)), _3_rightOut);
          }
        }
      }
      return @out;
    }
    public static BigInteger QueryAccumulatedAddAtKey(ThunderDbMutable._IQueryTree tree, BigInteger key)
    {
      BigInteger acc = BigInteger.Zero;
      if ((tree).is_QEmpty) {
        acc = BigInteger.Zero;
      } else if ((key) == ((tree).dtor_key)) {
        acc = ((tree).dtor_add) + ((tree).dtor_localAdd);
      } else if ((key) < ((tree).dtor_key)) {
        BigInteger _0_childAcc;
        BigInteger _out0;
        _out0 = ThunderDbMutable.__default.QueryAccumulatedAddAtKey((tree).dtor_left, key);
        _0_childAcc = _out0;
        acc = ((tree).dtor_add) + (_0_childAcc);
      } else {
        BigInteger _1_childAcc;
        BigInteger _out1;
        _out1 = ThunderDbMutable.__default.QueryAccumulatedAddAtKey((tree).dtor_right, key);
        _1_childAcc = _out1;
        acc = ((tree).dtor_add) + (_1_childAcc);
      }
      return acc;
    }
    public static BigInteger NegInfInt { get {
      return new BigInteger(-2147483647);
    } }
    public static BigInteger NegInfScore { get {
      return new BigInteger(-2147483647);
    } }
  }

  public interface _IQueryIndexEntry {
    bool is_QueryIndexEntry { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_baseScore { get; }
    BigInteger dtor_maxCap { get; }
    _IQueryIndexEntry DowncastClone();
  }
  public class QueryIndexEntry : _IQueryIndexEntry {
    public readonly BigInteger _id;
    public readonly BigInteger _baseScore;
    public readonly BigInteger _maxCap;
    public QueryIndexEntry(BigInteger id, BigInteger baseScore, BigInteger maxCap) {
      this._id = id;
      this._baseScore = baseScore;
      this._maxCap = maxCap;
    }
    public _IQueryIndexEntry DowncastClone() {
      if (this is _IQueryIndexEntry dt) { return dt; }
      return new QueryIndexEntry(_id, _baseScore, _maxCap);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbMutable.QueryIndexEntry;
      return oth != null && this._id == oth._id && this._baseScore == oth._baseScore && this._maxCap == oth._maxCap;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseScore));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maxCap));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbMutable.QueryIndexEntry.QueryIndexEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._baseScore);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maxCap);
      s += ")";
      return s;
    }
    private static readonly ThunderDbMutable._IQueryIndexEntry theDefault = create(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbMutable._IQueryIndexEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbMutable._IQueryIndexEntry> _TYPE = new Dafny.TypeDescriptor<ThunderDbMutable._IQueryIndexEntry>(ThunderDbMutable.QueryIndexEntry.Default());
    public static Dafny.TypeDescriptor<ThunderDbMutable._IQueryIndexEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryIndexEntry create(BigInteger id, BigInteger baseScore, BigInteger maxCap) {
      return new QueryIndexEntry(id, baseScore, maxCap);
    }
    public static _IQueryIndexEntry create_QueryIndexEntry(BigInteger id, BigInteger baseScore, BigInteger maxCap) {
      return create(id, baseScore, maxCap);
    }
    public bool is_QueryIndexEntry { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_baseScore {
      get {
        return this._baseScore;
      }
    }
    public BigInteger dtor_maxCap {
      get {
        return this._maxCap;
      }
    }
  }

  public interface _IQueryState {
    bool is_QueryState { get; }
    ThunderDbStack._IQuerySpec dtor_spec { get; }
    BigInteger dtor_currentMatches { get; }
    BigInteger dtor_baseScore { get; }
    _IQueryState DowncastClone();
  }
  public class QueryState : _IQueryState {
    public readonly ThunderDbStack._IQuerySpec _spec;
    public readonly BigInteger _currentMatches;
    public readonly BigInteger _baseScore;
    public QueryState(ThunderDbStack._IQuerySpec spec, BigInteger currentMatches, BigInteger baseScore) {
      this._spec = spec;
      this._currentMatches = currentMatches;
      this._baseScore = baseScore;
    }
    public _IQueryState DowncastClone() {
      if (this is _IQueryState dt) { return dt; }
      return new QueryState(_spec, _currentMatches, _baseScore);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbMutable.QueryState;
      return oth != null && object.Equals(this._spec, oth._spec) && this._currentMatches == oth._currentMatches && this._baseScore == oth._baseScore;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._spec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._currentMatches));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseScore));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbMutable.QueryState.QueryState";
      s += "(";
      s += Dafny.Helpers.ToString(this._spec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._currentMatches);
      s += ", ";
      s += Dafny.Helpers.ToString(this._baseScore);
      s += ")";
      return s;
    }
    private static readonly ThunderDbMutable._IQueryState theDefault = create(ThunderDbStack.QuerySpec.Default(), BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbMutable._IQueryState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbMutable._IQueryState> _TYPE = new Dafny.TypeDescriptor<ThunderDbMutable._IQueryState>(ThunderDbMutable.QueryState.Default());
    public static Dafny.TypeDescriptor<ThunderDbMutable._IQueryState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryState create(ThunderDbStack._IQuerySpec spec, BigInteger currentMatches, BigInteger baseScore) {
      return new QueryState(spec, currentMatches, baseScore);
    }
    public static _IQueryState create_QueryState(ThunderDbStack._IQuerySpec spec, BigInteger currentMatches, BigInteger baseScore) {
      return create(spec, currentMatches, baseScore);
    }
    public bool is_QueryState { get { return true; } }
    public ThunderDbStack._IQuerySpec dtor_spec {
      get {
        return this._spec;
      }
    }
    public BigInteger dtor_currentMatches {
      get {
        return this._currentMatches;
      }
    }
    public BigInteger dtor_baseScore {
      get {
        return this._baseScore;
      }
    }
  }

  public interface _IPendingRetrieval {
    bool is_PendingRetrieval { get; }
    BigInteger dtor_docId { get; }
    BigInteger dtor_queryId { get; }
    _IPendingRetrieval DowncastClone();
  }
  public class PendingRetrieval : _IPendingRetrieval {
    public readonly BigInteger _docId;
    public readonly BigInteger _queryId;
    public PendingRetrieval(BigInteger docId, BigInteger queryId) {
      this._docId = docId;
      this._queryId = queryId;
    }
    public _IPendingRetrieval DowncastClone() {
      if (this is _IPendingRetrieval dt) { return dt; }
      return new PendingRetrieval(_docId, _queryId);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbMutable.PendingRetrieval;
      return oth != null && this._docId == oth._docId && this._queryId == oth._queryId;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queryId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbMutable.PendingRetrieval.PendingRetrieval";
      s += "(";
      s += Dafny.Helpers.ToString(this._docId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._queryId);
      s += ")";
      return s;
    }
    private static readonly ThunderDbMutable._IPendingRetrieval theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static ThunderDbMutable._IPendingRetrieval Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbMutable._IPendingRetrieval> _TYPE = new Dafny.TypeDescriptor<ThunderDbMutable._IPendingRetrieval>(ThunderDbMutable.PendingRetrieval.Default());
    public static Dafny.TypeDescriptor<ThunderDbMutable._IPendingRetrieval> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPendingRetrieval create(BigInteger docId, BigInteger queryId) {
      return new PendingRetrieval(docId, queryId);
    }
    public static _IPendingRetrieval create_PendingRetrieval(BigInteger docId, BigInteger queryId) {
      return create(docId, queryId);
    }
    public bool is_PendingRetrieval { get { return true; } }
    public BigInteger dtor_docId {
      get {
        return this._docId;
      }
    }
    public BigInteger dtor_queryId {
      get {
        return this._queryId;
      }
    }
  }

  public interface _IQueryTree {
    bool is_QEmpty { get; }
    bool is_QNode { get; }
    BigInteger dtor_key { get; }
    BigInteger dtor_prio { get; }
    BigInteger dtor_add { get; }
    BigInteger dtor_localAdd { get; }
    Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> dtor_items { get; }
    BigInteger dtor_subtreeMax { get; }
    BigInteger dtor_localMaxCap { get; }
    BigInteger dtor_subtreeMaxCap { get; }
    ThunderDbMutable._IQueryTree dtor_left { get; }
    ThunderDbMutable._IQueryTree dtor_right { get; }
    _IQueryTree DowncastClone();
  }
  public abstract class QueryTree : _IQueryTree {
    public QueryTree() {
    }
    private static readonly ThunderDbMutable._IQueryTree theDefault = create_QEmpty();
    public static ThunderDbMutable._IQueryTree Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbMutable._IQueryTree> _TYPE = new Dafny.TypeDescriptor<ThunderDbMutable._IQueryTree>(ThunderDbMutable.QueryTree.Default());
    public static Dafny.TypeDescriptor<ThunderDbMutable._IQueryTree> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryTree create_QEmpty() {
      return new QueryTree_QEmpty();
    }
    public static _IQueryTree create_QNode(BigInteger key, BigInteger prio, BigInteger @add, BigInteger localAdd, Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> items, BigInteger subtreeMax, BigInteger localMaxCap, BigInteger subtreeMaxCap, ThunderDbMutable._IQueryTree left, ThunderDbMutable._IQueryTree right) {
      return new QueryTree_QNode(key, prio, @add, localAdd, items, subtreeMax, localMaxCap, subtreeMaxCap, left, right);
    }
    public bool is_QEmpty { get { return this is QueryTree_QEmpty; } }
    public bool is_QNode { get { return this is QueryTree_QNode; } }
    public BigInteger dtor_key {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._key;
      }
    }
    public BigInteger dtor_prio {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._prio;
      }
    }
    public BigInteger dtor_add {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._add;
      }
    }
    public BigInteger dtor_localAdd {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._localAdd;
      }
    }
    public Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> dtor_items {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._items;
      }
    }
    public BigInteger dtor_subtreeMax {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._subtreeMax;
      }
    }
    public BigInteger dtor_localMaxCap {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._localMaxCap;
      }
    }
    public BigInteger dtor_subtreeMaxCap {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._subtreeMaxCap;
      }
    }
    public ThunderDbMutable._IQueryTree dtor_left {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._left;
      }
    }
    public ThunderDbMutable._IQueryTree dtor_right {
      get {
        var d = this;
        return ((QueryTree_QNode)d)._right;
      }
    }
    public abstract _IQueryTree DowncastClone();
  }
  public class QueryTree_QEmpty : QueryTree {
    public QueryTree_QEmpty() : base() {
    }
    public override _IQueryTree DowncastClone() {
      if (this is _IQueryTree dt) { return dt; }
      return new QueryTree_QEmpty();
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbMutable.QueryTree_QEmpty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbMutable.QueryTree.QEmpty";
      return s;
    }
  }
  public class QueryTree_QNode : QueryTree {
    public readonly BigInteger _key;
    public readonly BigInteger _prio;
    public readonly BigInteger _add;
    public readonly BigInteger _localAdd;
    public readonly Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> _items;
    public readonly BigInteger _subtreeMax;
    public readonly BigInteger _localMaxCap;
    public readonly BigInteger _subtreeMaxCap;
    public readonly ThunderDbMutable._IQueryTree _left;
    public readonly ThunderDbMutable._IQueryTree _right;
    public QueryTree_QNode(BigInteger key, BigInteger prio, BigInteger @add, BigInteger localAdd, Dafny.ISequence<ThunderDbMutable._IQueryIndexEntry> items, BigInteger subtreeMax, BigInteger localMaxCap, BigInteger subtreeMaxCap, ThunderDbMutable._IQueryTree left, ThunderDbMutable._IQueryTree right) : base() {
      this._key = key;
      this._prio = prio;
      this._add = @add;
      this._localAdd = localAdd;
      this._items = items;
      this._subtreeMax = subtreeMax;
      this._localMaxCap = localMaxCap;
      this._subtreeMaxCap = subtreeMaxCap;
      this._left = left;
      this._right = right;
    }
    public override _IQueryTree DowncastClone() {
      if (this is _IQueryTree dt) { return dt; }
      return new QueryTree_QNode(_key, _prio, _add, _localAdd, _items, _subtreeMax, _localMaxCap, _subtreeMaxCap, _left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbMutable.QueryTree_QNode;
      return oth != null && this._key == oth._key && this._prio == oth._prio && this._add == oth._add && this._localAdd == oth._localAdd && object.Equals(this._items, oth._items) && this._subtreeMax == oth._subtreeMax && this._localMaxCap == oth._localMaxCap && this._subtreeMaxCap == oth._subtreeMaxCap && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._prio));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._add));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._localAdd));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._items));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._subtreeMax));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._localMaxCap));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._subtreeMaxCap));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbMutable.QueryTree.QNode";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._prio);
      s += ", ";
      s += Dafny.Helpers.ToString(this._add);
      s += ", ";
      s += Dafny.Helpers.ToString(this._localAdd);
      s += ", ";
      s += Dafny.Helpers.ToString(this._items);
      s += ", ";
      s += Dafny.Helpers.ToString(this._subtreeMax);
      s += ", ";
      s += Dafny.Helpers.ToString(this._localMaxCap);
      s += ", ";
      s += Dafny.Helpers.ToString(this._subtreeMaxCap);
      s += ", ";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }

  public interface _IQueryTreePair {
    bool is_QueryTreePair { get; }
    ThunderDbMutable._IQueryTree dtor_left { get; }
    ThunderDbMutable._IQueryTree dtor_right { get; }
    _IQueryTreePair DowncastClone();
  }
  public class QueryTreePair : _IQueryTreePair {
    public readonly ThunderDbMutable._IQueryTree _left;
    public readonly ThunderDbMutable._IQueryTree _right;
    public QueryTreePair(ThunderDbMutable._IQueryTree left, ThunderDbMutable._IQueryTree right) {
      this._left = left;
      this._right = right;
    }
    public _IQueryTreePair DowncastClone() {
      if (this is _IQueryTreePair dt) { return dt; }
      return new QueryTreePair(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as ThunderDbMutable.QueryTreePair;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ThunderDbMutable.QueryTreePair.QueryTreePair";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
    private static readonly ThunderDbMutable._IQueryTreePair theDefault = create(ThunderDbMutable.QueryTree.Default(), ThunderDbMutable.QueryTree.Default());
    public static ThunderDbMutable._IQueryTreePair Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ThunderDbMutable._IQueryTreePair> _TYPE = new Dafny.TypeDescriptor<ThunderDbMutable._IQueryTreePair>(ThunderDbMutable.QueryTreePair.Default());
    public static Dafny.TypeDescriptor<ThunderDbMutable._IQueryTreePair> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IQueryTreePair create(ThunderDbMutable._IQueryTree left, ThunderDbMutable._IQueryTree right) {
      return new QueryTreePair(left, right);
    }
    public static _IQueryTreePair create_QueryTreePair(ThunderDbMutable._IQueryTree left, ThunderDbMutable._IQueryTree right) {
      return create(left, right);
    }
    public bool is_QueryTreePair { get { return true; } }
    public ThunderDbMutable._IQueryTree dtor_left {
      get {
        return this._left;
      }
    }
    public ThunderDbMutable._IQueryTree dtor_right {
      get {
        return this._right;
      }
    }
  }

  public partial class MutableQueryIndex {
    public MutableQueryIndex() {
      this.root = ThunderDbMutable.QueryTree.Default();
    }
    public ThunderDbMutable._IQueryTree root {get; set;}
    public void __ctor()
    {
      (this).root = ThunderDbMutable.QueryTree.create_QEmpty();
    }
    public void RangeAddKeysGreaterThan(BigInteger key, BigInteger delta)
    {
      ThunderDbMutable._IQueryTreePair _0_pair;
      ThunderDbMutable._IQueryTreePair _out0;
      _out0 = ThunderDbMutable.__default.QuerySplitByKey(this.root, key);
      _0_pair = _out0;
      ThunderDbMutable._IQueryTree _1_rightTree;
      _1_rightTree = (_0_pair).dtor_right;
      if ((_1_rightTree).is_QNode) {
        _1_rightTree = ThunderDbMutable.QueryTree.create_QNode((_1_rightTree).dtor_key, (_1_rightTree).dtor_prio, ((_1_rightTree).dtor_add) + (delta), (_1_rightTree).dtor_localAdd, (_1_rightTree).dtor_items, ((((_1_rightTree).dtor_subtreeMax) == (ThunderDbMutable.__default.NegInfInt)) ? (ThunderDbMutable.__default.NegInfInt) : (((_1_rightTree).dtor_subtreeMax) + (delta))), (_1_rightTree).dtor_localMaxCap, (_1_rightTree).dtor_subtreeMaxCap, (_1_rightTree).dtor_left, (_1_rightTree).dtor_right);
      }
      ThunderDbMutable._IQueryTree _2_merged;
      ThunderDbMutable._IQueryTree _out1;
      _out1 = ThunderDbMutable.__default.QueryMerge((_0_pair).dtor_left, _1_rightTree);
      _2_merged = _out1;
      (this).root = _2_merged;
    }
    public void Insert(BigInteger key, BigInteger id, BigInteger effectiveScore, BigInteger maxCap)
    {
      ThunderDbMutable._IQueryTree _0_nextRoot;
      ThunderDbMutable._IQueryTree _out0;
      _out0 = ThunderDbMutable.__default.QueryInsert(this.root, key, id, effectiveScore, maxCap, BigInteger.Zero);
      _0_nextRoot = _out0;
      (this).root = _0_nextRoot;
    }
    public void Remove(BigInteger key, BigInteger id, BigInteger baseScore, BigInteger maxCap)
    {
      ThunderDbMutable._IQueryTree _0_nextRoot;
      ThunderDbMutable._IQueryTree _out0;
      _out0 = ThunderDbMutable.__default.QueryRemove(this.root, key, id, baseScore, maxCap);
      _0_nextRoot = _out0;
      (this).root = _0_nextRoot;
    }
    public Dafny.ISequence<BigInteger> CollectForValue(BigInteger @value, BigInteger cutoff)
    {
      Dafny.ISequence<BigInteger> @out = Dafny.Sequence<BigInteger>.Empty;
      Dafny.ISequence<BigInteger> _out0;
      _out0 = ThunderDbMutable.__default.QueryCollectForValue(this.root, BigInteger.Zero, cutoff, @value);
      @out = _out0;
      return @out;
    }
    public BigInteger AccumulatedAddAtKey(BigInteger key)
    {
      BigInteger acc = BigInteger.Zero;
      BigInteger _out0;
      _out0 = ThunderDbMutable.__default.QueryAccumulatedAddAtKey(this.root, key);
      acc = _out0;
      return acc;
    }
  }

  public partial class MutableEngine {
    public MutableEngine() {
      this.docs = DocsIndexTreap.Treap.Default();
      this.store = Dafny.Map<BigInteger, BigInteger>.Empty;
      this.docIds = Dafny.Sequence<BigInteger>.Empty;
      this.queryIndex = default(ThunderDbMutable.MutableQueryIndex);
      this.queries = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Empty;
      this.pendingByQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty;
      this.pendingByDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty;
      this.pendingDocs = Dafny.Sequence<BigInteger>.Empty;
      this.pendingPairs = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.Empty;
      this.nextQueryId = BigInteger.Zero;
    }
    public DocsIndexTreap._ITreap docs {get; set;}
    public Dafny.IMap<BigInteger,BigInteger> store {get; set;}
    public Dafny.ISequence<BigInteger> docIds {get; set;}
    public ThunderDbMutable.MutableQueryIndex queryIndex {get; set;}
    public Dafny.IMap<BigInteger,ThunderDbMutable._IQueryState> queries {get; set;}
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByQuery {get; set;}
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> pendingByDoc {get; set;}
    public Dafny.ISequence<BigInteger> pendingDocs {get; set;}
    public Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> pendingPairs {get; set;}
    public BigInteger nextQueryId {get; set;}
    public void __ctor()
    {
      (this).docs = DocsIndexTreap.Treap.create_Empty();
      (this).store = Dafny.Map<BigInteger, BigInteger>.FromElements();
      (this).docIds = Dafny.Sequence<BigInteger>.FromElements();
      ThunderDbMutable.MutableQueryIndex _nw0 = new ThunderDbMutable.MutableQueryIndex();
      _nw0.__ctor();
      (this).queryIndex = _nw0;
      (this).queries = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.FromElements();
      (this).pendingByQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements();
      (this).pendingByDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements();
      (this).pendingDocs = Dafny.Sequence<BigInteger>.FromElements();
      (this).pendingPairs = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements();
      (this).nextQueryId = BigInteger.One;
    }
    public bool Ready() {
      return DocsIndexTreap.__default.SumConsistent(this.docs);
    }
    public Dafny.ISequence<BigInteger> CollectQueriesForValue(BigInteger @value, BigInteger docId)
    {
      Dafny.ISequence<BigInteger> ids = Dafny.Sequence<BigInteger>.Empty;
      BigInteger _0_cutoff;
      _0_cutoff = DocsIndexTreap.__default.TreapRank(this.docs, @value, DocsIndexModel.MaybeDocId.create_SomeDoc(docId));
      Dafny.ISequence<BigInteger> _out0;
      _out0 = (this.queryIndex).CollectForValue(@value, _0_cutoff);
      ids = _out0;
      return ids;
    }
    public void RegisterPendingDocQuery(BigInteger docId, BigInteger queryId)
    {
      Dafny.ISequence<BigInteger> _0_docsForQuery;
      if ((this.pendingByQuery).Contains(queryId)) {
        _0_docsForQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByQuery,queryId);
      } else {
        _0_docsForQuery = Dafny.Sequence<BigInteger>.FromElements();
      }
      _0_docsForQuery = ThunderDbStack.__default.AppendDocIdIfMissing(_0_docsForQuery, docId);
      (this).pendingByQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(this.pendingByQuery, queryId, _0_docsForQuery);
      Dafny.ISequence<BigInteger> _1_queriesForDoc;
      if ((this.pendingByDoc).Contains(docId)) {
        _1_queriesForDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByDoc,docId);
      } else {
        _1_queriesForDoc = Dafny.Sequence<BigInteger>.FromElements();
      }
      _1_queriesForDoc = ThunderDbStack.__default.AppendQueryIdUnique(_1_queriesForDoc, queryId);
      (this).pendingByDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(this.pendingByDoc, docId, _1_queriesForDoc);
      (this).pendingDocs = ThunderDbStack.__default.AppendDocIdIfMissing(this.pendingDocs, docId);
      (this).pendingPairs = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.Concat(this.pendingPairs, Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements(ThunderDbMutable.PendingRetrieval.create(docId, queryId)));
    }
    public bool RemovePendingDocQuery(BigInteger docId, BigInteger queryId)
    {
      bool removed = false;
      removed = false;
      if ((this.pendingByQuery).Contains(queryId)) {
        Dafny.ISequence<BigInteger> _0_docsForQuery;
        _0_docsForQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByQuery,queryId);
        if (ThunderDbStack.__default.ContainsId(_0_docsForQuery, docId)) {
          removed = true;
          Dafny.ISequence<BigInteger> _1_nextDocsForQuery;
          _1_nextDocsForQuery = ThunderDbStack.__default.RemoveDocId(_0_docsForQuery, docId);
          if ((new BigInteger((_1_nextDocsForQuery).Count)).Sign == 0) {
            (this).pendingByQuery = Dafny.Helpers.Id<Func<BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_2_queryId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
              var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
              foreach (BigInteger _compr_0 in (this.pendingByQuery).Keys.Elements) {
                BigInteger _3_key = (BigInteger)_compr_0;
                if (((this.pendingByQuery).Contains(_3_key)) && ((_3_key) != (_2_queryId))) {
                  _coll0.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_3_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByQuery,_3_key)));
                }
              }
              return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll0);
            }))())(queryId);
          } else {
            (this).pendingByQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(this.pendingByQuery, queryId, _1_nextDocsForQuery);
          }
        }
      }
      if ((this.pendingByDoc).Contains(docId)) {
        Dafny.ISequence<BigInteger> _4_queriesForDoc;
        _4_queriesForDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByDoc,docId);
        if (ThunderDbStack.__default.ContainsQueryId(_4_queriesForDoc, queryId)) {
          Dafny.ISequence<BigInteger> _5_nextQueriesForDoc;
          _5_nextQueriesForDoc = ThunderDbMutable.__default.RemoveQueryId(_4_queriesForDoc, queryId);
          if ((new BigInteger((_5_nextQueriesForDoc).Count)).Sign == 0) {
            (this).pendingByDoc = Dafny.Helpers.Id<Func<BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_6_docId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
              var _coll1 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
              foreach (BigInteger _compr_1 in (this.pendingByDoc).Keys.Elements) {
                BigInteger _7_key = (BigInteger)_compr_1;
                if (((this.pendingByDoc).Contains(_7_key)) && ((_7_key) != (_6_docId))) {
                  _coll1.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_7_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByDoc,_7_key)));
                }
              }
              return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll1);
            }))())(docId);
            (this).pendingDocs = ThunderDbStack.__default.RemoveDocId(this.pendingDocs, docId);
          } else {
            (this).pendingByDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(this.pendingByDoc, docId, _5_nextQueriesForDoc);
          }
        }
      }
      if (removed) {
        (this).pendingPairs = ThunderDbMutable.__default.RemovePendingRetrieval(this.pendingPairs, docId, queryId);
      }
      return removed;
    }
    public void ResolvePendingForDoc(BigInteger docId)
    {
      if ((this.pendingByDoc).Contains(docId)) {
        Dafny.ISequence<BigInteger> _0_queriesForDoc;
        _0_queriesForDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByDoc,docId);
        BigInteger _1_i;
        _1_i = BigInteger.Zero;
        while ((_1_i) < (new BigInteger((_0_queriesForDoc).Count))) {
          if ((this.pendingByQuery).Contains((_0_queriesForDoc).Select(_1_i))) {
            Dafny.ISequence<BigInteger> _2_docsForQuery;
            _2_docsForQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByQuery,(_0_queriesForDoc).Select(_1_i));
            Dafny.ISequence<BigInteger> _3_nextDocsForQuery;
            _3_nextDocsForQuery = ThunderDbStack.__default.RemoveDocId(_2_docsForQuery, docId);
            if ((new BigInteger((_3_nextDocsForQuery).Count)).Sign == 0) {
              (this).pendingByQuery = Dafny.Helpers.Id<Func<Dafny.ISequence<BigInteger>, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_4_queriesForDoc, _5_i) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
                var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
                foreach (BigInteger _compr_0 in (this.pendingByQuery).Keys.Elements) {
                  BigInteger _6_key = (BigInteger)_compr_0;
                  if (((this.pendingByQuery).Contains(_6_key)) && ((_6_key) != ((_4_queriesForDoc).Select(_5_i)))) {
                    _coll0.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_6_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByQuery,_6_key)));
                  }
                }
                return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll0);
              }))())(_0_queriesForDoc, _1_i);
            } else {
              (this).pendingByQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(this.pendingByQuery, (_0_queriesForDoc).Select(_1_i), _3_nextDocsForQuery);
            }
          }
          _1_i = (_1_i) + (BigInteger.One);
        }
        (this).pendingByDoc = Dafny.Helpers.Id<Func<BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_7_docId) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
          var _coll1 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
          foreach (BigInteger _compr_1 in (this.pendingByDoc).Keys.Elements) {
            BigInteger _8_key = (BigInteger)_compr_1;
            if (((this.pendingByDoc).Contains(_8_key)) && ((_8_key) != (_7_docId))) {
              _coll1.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_8_key, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByDoc,_8_key)));
            }
          }
          return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll1);
        }))())(docId);
        (this).pendingDocs = ThunderDbStack.__default.RemoveDocId(this.pendingDocs, docId);
        (this).pendingPairs = ThunderDbMutable.__default.RemovePendingRetrievalsForDoc(this.pendingPairs, docId);
      }
    }
    public bool CancelPendingForQuery(BigInteger docId, BigInteger queryId)
    {
      bool cancelled = false;
      bool _out0;
      _out0 = (this).RemovePendingDocQuery(docId, queryId);
      cancelled = _out0;
      if ((cancelled) && ((this.queries).Contains(queryId))) {
        ThunderDbMutable._IQueryState _0_state;
        _0_state = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,queryId);
        if (((_0_state).dtor_currentMatches).Sign == 1) {
          (this).queries = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Update(this.queries, queryId, ThunderDbMutable.QueryState.create((_0_state).dtor_spec, ((_0_state).dtor_currentMatches) - (BigInteger.One), (_0_state).dtor_baseScore));
        }
      }
      return cancelled;
    }
    public Dafny.ISequence<ThunderDbStack._IDownstreamEvent> DrainPendingRetrievals()
    {
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      Dafny.ISequence<ThunderDbMutable._IPendingRetrieval> _0_queued;
      _0_queued = this.pendingPairs;
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _1_retrievals;
      _1_retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      BigInteger _2_i;
      _2_i = BigInteger.Zero;
      while ((_2_i) < (new BigInteger((_0_queued).Count))) {
        BigInteger _3_docId;
        _3_docId = ((_0_queued).Select(_2_i)).dtor_docId;
        BigInteger _4_queryId;
        _4_queryId = ((_0_queued).Select(_2_i)).dtor_queryId;
        if (((this.pendingByDoc).Contains(_3_docId)) && (ThunderDbStack.__default.ContainsQueryId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByDoc,_3_docId), _4_queryId))) {
          ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(this.store, _3_docId);
          {
            if (_source0.is_NoState) {
              goto after_match0;
            }
          }
          {
            BigInteger _5_docState = _source0.dtor_state;
            {
              _1_retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_1_retrievals, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(_3_docId, _5_docState, Dafny.Sequence<BigInteger>.FromElements(_4_queryId))));
            }
          }
        after_match0: ;
        }
        _2_i = (_2_i) + (BigInteger.One);
      }
      (this).pendingByQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements();
      (this).pendingByDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements();
      (this).pendingDocs = Dafny.Sequence<BigInteger>.FromElements();
      (this).pendingPairs = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements();
      if ((new BigInteger((_1_retrievals).Count)).Sign == 1) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_1_retrievals));
      }
      return events;
    }
    public Dafny.ISequence<ThunderDbStack._IDownstreamEvent> DrainPendingRetrievalsGrouped()
    {
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      Dafny.ISequence<BigInteger> _0_queued;
      _0_queued = this.pendingDocs;
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _1_retrievals;
      _1_retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      BigInteger _2_i;
      _2_i = BigInteger.Zero;
      while ((_2_i) < (new BigInteger((_0_queued).Count))) {
        BigInteger _3_docId;
        _3_docId = (_0_queued).Select(_2_i);
        if ((this.pendingByDoc).Contains(_3_docId)) {
          Dafny.ISequence<BigInteger> _4_queriesForDoc;
          _4_queriesForDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByDoc,_3_docId);
          ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(this.store, _3_docId);
          {
            if (_source0.is_NoState) {
              goto after_match0;
            }
          }
          {
            BigInteger _5_docState = _source0.dtor_state;
            {
              _1_retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_1_retrievals, Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements(ThunderDbStack.RetrievalDoc.create(_3_docId, _5_docState, _4_queriesForDoc)));
            }
          }
        after_match0: ;
        }
        _2_i = (_2_i) + (BigInteger.One);
      }
      (this).pendingByQuery = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements();
      (this).pendingByDoc = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements();
      (this).pendingDocs = Dafny.Sequence<BigInteger>.FromElements();
      (this).pendingPairs = Dafny.Sequence<ThunderDbMutable._IPendingRetrieval>.FromElements();
      if ((new BigInteger((_1_retrievals).Count)).Sign == 1) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_1_retrievals));
      }
      return events;
    }
    public Dafny.ISequence<BigInteger> QueryVisible(BigInteger id)
    {
      Dafny.ISequence<BigInteger> visible = Dafny.Sequence<BigInteger>.Empty;
      if ((this.queries).Contains(id)) {
        ThunderDbMutable._IQueryState _0_state;
        _0_state = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,id);
        visible = DocsIndexTreap.__default.TreapCollectRange(this.docs, ((_0_state).dtor_spec).dtor_minScore, ((_0_state).dtor_spec).dtor_maxScore, ((_0_state).dtor_spec).dtor_limit);
      } else {
        visible = Dafny.Sequence<BigInteger>.FromElements();
      }
      return visible;
    }
    public BigInteger CountDocsInRange(ThunderDbStack._IQuerySpec spec)
    {
      BigInteger count = BigInteger.Zero;
      BigInteger _0_upper;
      _0_upper = DocsIndexTreap.__default.TreapCountAtMost(this.docs, (spec).dtor_maxScore);
      BigInteger _1_lower;
      _1_lower = DocsIndexTreap.__default.TreapRank(this.docs, (spec).dtor_minScore, DocsIndexModel.MaybeDocId.create_NoDoc());
      BigInteger _2_diff;
      if ((_0_upper) >= (_1_lower)) {
        _2_diff = (_0_upper) - (_1_lower);
      } else {
        _2_diff = BigInteger.Zero;
      }
      if ((_2_diff) <= ((spec).dtor_limit)) {
        count = _2_diff;
      } else {
        count = (spec).dtor_limit;
      }
      return count;
    }
    public DocsIndexModel._IMaybeDocId QueryDocAtOffset(ThunderDbMutable._IQueryState state, BigInteger offset)
    {
      DocsIndexModel._IMaybeDocId doc = DocsIndexModel.MaybeDocId.Default();
      BigInteger _0_addAtKey;
      BigInteger _out0;
      _out0 = (this.queryIndex).AccumulatedAddAtKey(((state).dtor_spec).dtor_minScore);
      _0_addAtKey = _out0;
      BigInteger _1_effectiveScore;
      _1_effectiveScore = ((state).dtor_baseScore) + (_0_addAtKey);
      BigInteger _2_startRank;
      if ((_1_effectiveScore) >= (((state).dtor_spec).dtor_limit)) {
        _2_startRank = (_1_effectiveScore) - (((state).dtor_spec).dtor_limit);
      } else {
        _2_startRank = BigInteger.Zero;
      }
      DocsIndexModel._IAtRank _source0 = DocsIndexTreap.__default.TreapGetAtRank(this.docs, (_2_startRank) + (offset));
      {
        if (_source0.is_Missing) {
          {
            doc = DocsIndexModel.MaybeDocId.create_NoDoc();
          }
          goto after_match0;
        }
      }
      {
        BigInteger _3_score = _source0.dtor_score;
        BigInteger _4_id = _source0.dtor_id;
        BigInteger _5_pos = _source0.dtor_position;
        {
          if ((_3_score) <= (((state).dtor_spec).dtor_maxScore)) {
            doc = DocsIndexModel.MaybeDocId.create_SomeDoc(_4_id);
          } else {
            doc = DocsIndexModel.MaybeDocId.create_NoDoc();
          }
        }
      }
    after_match0: ;
      return doc;
    }
    public Dafny.ISequence<ThunderDbStack._IRetrievalDoc> FillGap(BigInteger queryId)
    {
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Empty;
      retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      if ((this.queries).Contains(queryId)) {
        ThunderDbMutable._IQueryState _0_state;
        _0_state = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,queryId);
        if (((_0_state).dtor_currentMatches) < (((_0_state).dtor_spec).dtor_limit)) {
          BigInteger _1_offset;
          _1_offset = (_0_state).dtor_currentMatches;
          bool _2_found;
          _2_found = false;
          while (!(_2_found)) {
            DocsIndexModel._IMaybeDocId _3_candidate;
            DocsIndexModel._IMaybeDocId _out0;
            _out0 = (this).QueryDocAtOffset(_0_state, _1_offset);
            _3_candidate = _out0;
            DocsIndexModel._IMaybeDocId _source0 = _3_candidate;
            {
              if (_source0.is_NoDoc) {
                {
                  _2_found = true;
                }
                goto after_match0;
              }
            }
            {
              BigInteger _4_docId = _source0.dtor_doc;
              {
                bool _5_alreadyPending;
                _5_alreadyPending = ((this.pendingByQuery).Contains(queryId)) && (ThunderDbStack.__default.ContainsId(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByQuery,queryId), _4_docId));
                if (_5_alreadyPending) {
                  _1_offset = (_1_offset) + (BigInteger.One);
                } else {
                  (this).queries = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Update(this.queries, queryId, ThunderDbMutable.QueryState.create((_0_state).dtor_spec, ((_0_state).dtor_currentMatches) + (BigInteger.One), (_0_state).dtor_baseScore));
                  (this).RegisterPendingDocQuery(_4_docId, queryId);
                  retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
                  _2_found = true;
                }
              }
            }
          after_match0: ;
          }
        }
      }
      return retrievals;
    }
    public Dafny.ISequence<BigInteger> PickOverflowDoc(BigInteger queryId)
    {
      Dafny.ISequence<BigInteger> doc = Dafny.Sequence<BigInteger>.Empty;
      doc = Dafny.Sequence<BigInteger>.FromElements();
      if ((this.queries).Contains(queryId)) {
        ThunderDbMutable._IQueryState _0_state;
        _0_state = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,queryId);
        if (((_0_state).dtor_currentMatches) >= (((_0_state).dtor_spec).dtor_limit)) {
          DocsIndexModel._IMaybeDocId _1_candidate;
          DocsIndexModel._IMaybeDocId _out0;
          _out0 = (this).QueryDocAtOffset(_0_state, ((_0_state).dtor_spec).dtor_limit);
          _1_candidate = _out0;
          DocsIndexModel._IMaybeDocId _source0 = _1_candidate;
          {
            if (_source0.is_NoDoc) {
              goto after_match0;
            }
          }
          {
            BigInteger _2_docId = _source0.dtor_doc;
            {
              doc = Dafny.Sequence<BigInteger>.FromElements(_2_docId);
            }
          }
        after_match0: ;
        }
      }
      return doc;
    }
    public void SeedDocs(Dafny.ISequence<ThunderDbStack._ISeedDoc> input)
    {
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger((input).Count))) {
        (this).store = Dafny.Map<BigInteger, BigInteger>.Update(this.store, ((input).Select(_0_i)).dtor_id, ((input).Select(_0_i)).dtor_state);
        (this).docIds = ThunderDbStack.__default.AppendDocIdIfMissing(this.docIds, ((input).Select(_0_i)).dtor_id);
        (this).docs = DocsIndexTreap.__default.Add(this.docs, (((input).Select(_0_i)).dtor_state), ((input).Select(_0_i)).dtor_id, ThunderDbStack.__default.PriorityFor((((input).Select(_0_i)).dtor_state), ((input).Select(_0_i)).dtor_id));
        _0_i = (_0_i) + (BigInteger.One);
      }
    }
    public void AddQueryDeferred(ThunderDbStack._IQuerySpec spec, out BigInteger queryId, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      queryId = BigInteger.Zero;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      queryId = this.nextQueryId;
      (this).nextQueryId = (this.nextQueryId) + (BigInteger.One);
      Dafny.ISequence<BigInteger> _0_visible;
      _0_visible = DocsIndexTreap.__default.TreapCollectRange(this.docs, (spec).dtor_minScore, (spec).dtor_maxScore, (spec).dtor_limit);
      BigInteger _1_effectiveScore;
      _1_effectiveScore = (DocsIndexTreap.__default.TreapRank(this.docs, (spec).dtor_minScore, DocsIndexModel.MaybeDocId.create_NoDoc())) + ((spec).dtor_limit);
      (this.queryIndex).Insert((spec).dtor_minScore, queryId, _1_effectiveScore, (spec).dtor_maxScore);
      BigInteger _2_accAtKey;
      BigInteger _out0;
      _out0 = (this.queryIndex).AccumulatedAddAtKey((spec).dtor_minScore);
      _2_accAtKey = _out0;
      BigInteger _3_baseScore;
      _3_baseScore = (_1_effectiveScore) - (_2_accAtKey);
      (this).queries = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Update(this.queries, queryId, ThunderDbMutable.QueryState.create(spec, new BigInteger((_0_visible).Count), _3_baseScore));
      BigInteger _4_i;
      _4_i = BigInteger.Zero;
      while ((_4_i) < (new BigInteger((_0_visible).Count))) {
        (this).RegisterPendingDocQuery((_0_visible).Select(_4_i), queryId);
        _4_i = (_4_i) + (BigInteger.One);
      }
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
    }
    public void AddQuery(ThunderDbStack._IQuerySpec spec, out BigInteger queryId, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
      queryId = BigInteger.Zero;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      BigInteger _out0;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out1;
      (this).AddQueryDeferred(spec, out _out0, out _out1);
      queryId = _out0;
      events = _out1;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _0_retrievalEvents;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out2;
      _out2 = (this).DrainPendingRetrievals();
      _0_retrievalEvents = _out2;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Concat(events, _0_retrievalEvents);
    }
    public Dafny.ISequence<ThunderDbStack._IDownstreamEvent> RemoveQueryDeferred(BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      if ((this.queries).Contains(id)) {
        ThunderDbMutable._IQueryState _0_state;
        _0_state = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,id);
        (this.queryIndex).Remove(((_0_state).dtor_spec).dtor_minScore, id, (_0_state).dtor_baseScore, ((_0_state).dtor_spec).dtor_maxScore);
        (this).queries = Dafny.Helpers.Id<Func<BigInteger, Dafny.IMap<BigInteger,ThunderDbMutable._IQueryState>>>((_1_id) => ((System.Func<Dafny.IMap<BigInteger,ThunderDbMutable._IQueryState>>)(() => {
          var _coll0 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,ThunderDbMutable._IQueryState>>();
          foreach (BigInteger _compr_0 in (this.queries).Keys.Elements) {
            BigInteger _2_key = (BigInteger)_compr_0;
            if (((this.queries).Contains(_2_key)) && ((_2_key) != (_1_id))) {
              _coll0.Add(new Dafny.Pair<BigInteger,ThunderDbMutable._IQueryState>(_2_key, Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,_2_key)));
            }
          }
          return Dafny.Map<BigInteger,ThunderDbMutable._IQueryState>.FromCollection(_coll0);
        }))())(id);
        if ((this.pendingByQuery).Contains(id)) {
          Dafny.ISequence<BigInteger> _3_pendingDocs;
          _3_pendingDocs = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(this.pendingByQuery,id);
          BigInteger _4_i;
          _4_i = BigInteger.Zero;
          while ((_4_i) < (new BigInteger((_3_pendingDocs).Count))) {
            bool _5_ignored;
            bool _out0;
            _out0 = (this).RemovePendingDocQuery((_3_pendingDocs).Select(_4_i), id);
            _5_ignored = _out0;
            _4_i = (_4_i) + (BigInteger.One);
          }
        }
      }
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      return events;
    }
    public Dafny.ISequence<ThunderDbStack._IDownstreamEvent> RemoveQuery(BigInteger id)
    {
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out0;
      _out0 = (this).RemoveQueryDeferred(id);
      events = _out0;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _0_retrievalEvents;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out1;
      _out1 = (this).DrainPendingRetrievals();
      _0_retrievalEvents = _out1;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Concat(events, _0_retrievalEvents);
      return events;
    }
    public Dafny.ISequence<ThunderDbStack._IDownstreamEvent> ApplyDocChangeDeferred(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      if ((((oldState).is_HasState) && ((newState).is_HasState)) && ((ThunderDbStack.__default.GetScore((oldState).dtor_state)) == (ThunderDbStack.__default.GetScore((newState).dtor_state)))) {
        Dafny.ISequence<BigInteger> _0_covering;
        Dafny.ISequence<BigInteger> _out0;
        _out0 = (this).CollectQueriesForValue(ThunderDbStack.__default.GetScore((oldState).dtor_state), id);
        _0_covering = _out0;
        (this).store = Dafny.Map<BigInteger, BigInteger>.Update(this.store, id, (newState).dtor_state);
        (this).ResolvePendingForDoc(id);
        if ((new BigInteger((_0_covering).Count)).Sign == 1) {
          events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(ThunderDbStack.MatchPayload.create(id, oldState, newState, _0_covering, _0_covering, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements())));
        }
        return events;
      }
      Dafny.ISequence<BigInteger> _1_oldMatches;
      _1_oldMatches = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _2_newMatches;
      _2_newMatches = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _3_blockedCandidates;
      _3_blockedCandidates = Dafny.Sequence<BigInteger>.FromElements();
      ThunderDbMutable.MutableQueryIndex _4_queryIndex;
      _4_queryIndex = this.queryIndex;
      if ((oldState).is_HasState) {
        Dafny.ISequence<BigInteger> _out1;
        _out1 = (this).CollectQueriesForValue(ThunderDbStack.__default.GetScore((oldState).dtor_state), id);
        _1_oldMatches = _out1;
        (this).docs = DocsIndexTreap.__default.Remove(this.docs, ThunderDbStack.__default.GetScore((oldState).dtor_state), id);
        (_4_queryIndex).RangeAddKeysGreaterThan(ThunderDbStack.__default.GetScore((oldState).dtor_state), new BigInteger(-1));
        BigInteger _5_oi;
        _5_oi = BigInteger.Zero;
        while ((_5_oi) < (new BigInteger((_1_oldMatches).Count))) {
          if ((this.queries).Contains((_1_oldMatches).Select(_5_oi))) {
            ThunderDbMutable._IQueryState _6_state;
            _6_state = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,(_1_oldMatches).Select(_5_oi));
            if (((_6_state).dtor_currentMatches).Sign == 1) {
              (this).queries = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Update(this.queries, (_1_oldMatches).Select(_5_oi), ThunderDbMutable.QueryState.create((_6_state).dtor_spec, ((_6_state).dtor_currentMatches) - (BigInteger.One), (_6_state).dtor_baseScore));
            }
          }
          _5_oi = (_5_oi) + (BigInteger.One);
        }
      }
      if ((newState).is_HasState) {
        BigInteger _7_newScore;
        _7_newScore = ThunderDbStack.__default.GetScore((newState).dtor_state);
        Dafny.ISequence<BigInteger> _out2;
        _out2 = (this).CollectQueriesForValue(_7_newScore, id);
        _2_newMatches = _out2;
        (this).docs = DocsIndexTreap.__default.Add(this.docs, _7_newScore, id, ThunderDbStack.__default.PriorityFor(_7_newScore, id));
        (_4_queryIndex).RangeAddKeysGreaterThan(_7_newScore, BigInteger.One);
        (this).store = Dafny.Map<BigInteger, BigInteger>.Update(this.store, id, (newState).dtor_state);
        (this).docIds = ThunderDbStack.__default.AppendDocIdIfMissing(this.docIds, id);
        BigInteger _8_ni;
        _8_ni = BigInteger.Zero;
        while ((_8_ni) < (new BigInteger((_2_newMatches).Count))) {
          if ((this.queries).Contains((_2_newMatches).Select(_8_ni))) {
            ThunderDbMutable._IQueryState _9_state;
            _9_state = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Select(this.queries,(_2_newMatches).Select(_8_ni));
            bool _10_consumedPending;
            bool _out3;
            _out3 = (this).RemovePendingDocQuery(id, (_2_newMatches).Select(_8_ni));
            _10_consumedPending = _out3;
            if (_10_consumedPending) {
            } else if (((_9_state).dtor_currentMatches) < (((_9_state).dtor_spec).dtor_limit)) {
              (this).queries = Dafny.Map<BigInteger, ThunderDbMutable._IQueryState>.Update(this.queries, (_2_newMatches).Select(_8_ni), ThunderDbMutable.QueryState.create((_9_state).dtor_spec, ((_9_state).dtor_currentMatches) + (BigInteger.One), (_9_state).dtor_baseScore));
            } else {
              _3_blockedCandidates = Dafny.Sequence<BigInteger>.Concat(_3_blockedCandidates, Dafny.Sequence<BigInteger>.FromElements((_2_newMatches).Select(_8_ni)));
            }
          }
          _8_ni = (_8_ni) + (BigInteger.One);
        }
      } else {
        (this).store = ThunderDbStack.__default.RemoveStoredDoc(this.store, id);
        (this).docIds = ThunderDbStack.__default.RemoveDocId(this.docIds, id);
      }
      Dafny.IMap<BigInteger,bool> _11_oldMatchMap;
      _11_oldMatchMap = Dafny.Map<BigInteger, bool>.FromElements();
      Dafny.IMap<BigInteger,bool> _12_newMatchMap;
      _12_newMatchMap = Dafny.Map<BigInteger, bool>.FromElements();
      BigInteger _13_oi;
      _13_oi = BigInteger.Zero;
      while ((_13_oi) < (new BigInteger((_1_oldMatches).Count))) {
        _11_oldMatchMap = Dafny.Map<BigInteger, bool>.Update(_11_oldMatchMap, (_1_oldMatches).Select(_13_oi), true);
        _13_oi = (_13_oi) + (BigInteger.One);
      }
      BigInteger _14_ni;
      _14_ni = BigInteger.Zero;
      while ((_14_ni) < (new BigInteger((_2_newMatches).Count))) {
        _12_newMatchMap = Dafny.Map<BigInteger, bool>.Update(_12_newMatchMap, (_2_newMatches).Select(_14_ni), true);
        _14_ni = (_14_ni) + (BigInteger.One);
      }
      Dafny.ISequence<ThunderDbStack._IEviction> _15_evictions;
      _15_evictions = Dafny.Sequence<ThunderDbStack._IEviction>.FromElements();
      Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _16_retrievals;
      _16_retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.FromElements();
      Dafny.ISequence<BigInteger> _17_matchesOld;
      _17_matchesOld = _1_oldMatches;
      Dafny.ISequence<BigInteger> _18_matchesNew;
      _18_matchesNew = _2_newMatches;
      Dafny.ISequence<BigInteger> _19_lostQueries;
      _19_lostQueries = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _20_li;
      _20_li = BigInteger.Zero;
      while ((_20_li) < (new BigInteger((_1_oldMatches).Count))) {
        if (!((_12_newMatchMap).Contains((_1_oldMatches).Select(_20_li)))) {
          _19_lostQueries = Dafny.Sequence<BigInteger>.Concat(_19_lostQueries, Dafny.Sequence<BigInteger>.FromElements((_1_oldMatches).Select(_20_li)));
        }
        _20_li = (_20_li) + (BigInteger.One);
      }
      _20_li = BigInteger.Zero;
      while ((_20_li) < (new BigInteger((_19_lostQueries).Count))) {
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _21_gapRetrievals;
        Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _out4;
        _out4 = (this).FillGap((_19_lostQueries).Select(_20_li));
        _21_gapRetrievals = _out4;
        _16_retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_16_retrievals, _21_gapRetrievals);
        _20_li = (_20_li) + (BigInteger.One);
      }
      BigInteger _22_bi;
      _22_bi = BigInteger.Zero;
      while ((_22_bi) < (new BigInteger((_3_blockedCandidates).Count))) {
        if (!((_11_oldMatchMap).Contains((_3_blockedCandidates).Select(_22_bi)))) {
          Dafny.ISequence<BigInteger> _23_evicted;
          Dafny.ISequence<BigInteger> _out5;
          _out5 = (this).PickOverflowDoc((_3_blockedCandidates).Select(_22_bi));
          _23_evicted = _out5;
          if ((new BigInteger((_23_evicted).Count)).Sign == 1) {
            _15_evictions = Dafny.Sequence<ThunderDbStack._IEviction>.Concat(_15_evictions, Dafny.Sequence<ThunderDbStack._IEviction>.FromElements(ThunderDbStack.Eviction.create((_3_blockedCandidates).Select(_22_bi), (_23_evicted).Select(BigInteger.Zero))));
            bool _24_cancelledPending;
            bool _out6;
            _out6 = (this).CancelPendingForQuery((_23_evicted).Select(BigInteger.Zero), (_3_blockedCandidates).Select(_22_bi));
            _24_cancelledPending = _out6;
            if (_24_cancelledPending) {
              Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _25_replacement;
              Dafny.ISequence<ThunderDbStack._IRetrievalDoc> _out7;
              _out7 = (this).FillGap((_3_blockedCandidates).Select(_22_bi));
              _25_replacement = _out7;
              _16_retrievals = Dafny.Sequence<ThunderDbStack._IRetrievalDoc>.Concat(_16_retrievals, _25_replacement);
            }
          }
        }
        _22_bi = (_22_bi) + (BigInteger.One);
      }
      (this).ResolvePendingForDoc(id);
      ThunderDbStack._IMatchPayload _26_payload;
      _26_payload = ThunderDbStack.MatchPayload.create(id, oldState, newState, _17_matchesOld, _18_matchesNew, _15_evictions);
      if ((ThunderDbStack.__default.HasAnyMatchChange(_26_payload)) && ((new BigInteger((_16_retrievals).Count)).Sign == 1)) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(_26_payload), ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_16_retrievals));
      } else if (ThunderDbStack.__default.HasAnyMatchChange(_26_payload)) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_MatchEvent(_26_payload));
      } else if ((new BigInteger((_16_retrievals).Count)).Sign == 1) {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements(ThunderDbStack.DownstreamEvent.create_RetrievalEvent(_16_retrievals));
      } else {
        events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      }
      return events;
    }
    public Dafny.ISequence<ThunderDbStack._IDownstreamEvent> ApplyDocChange(BigInteger id, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState)
    {
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out0;
      _out0 = (this).ApplyDocChangeDeferred(id, oldState, newState);
      events = _out0;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _0_retrievalEvents;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out1;
      _out1 = (this).DrainPendingRetrievals();
      _0_retrievalEvents = _out1;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Concat(events, _0_retrievalEvents);
      return events;
    }
    public void ProcessItemDeferred(ThunderDbStack._IStreamItem item, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events, out BigInteger queryId)
    {
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      queryId = BigInteger.Zero;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.FromElements();
      queryId = BigInteger.Zero;
      ThunderDbStack._IStreamItem _source0 = item;
      {
        if (_source0.is_SeedDocsItem) {
          Dafny.ISequence<ThunderDbStack._ISeedDoc> _0_docs = _source0.dtor_docs;
          {
            (this).SeedDocs(_0_docs);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_QueryAddItem) {
          ThunderDbStack._IQuerySpec _1_spec = _source0.dtor_spec;
          {
            BigInteger _out0;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out1;
            (this).AddQueryDeferred(_1_spec, out _out0, out _out1);
            queryId = _out0;
            events = _out1;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_QueryRemoveItem) {
          BigInteger _2_id = _source0.dtor_id;
          {
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out2;
            _out2 = (this).RemoveQueryDeferred(_2_id);
            events = _out2;
          }
          goto after_match0;
        }
      }
      {
        BigInteger _3_id = _source0.dtor_id;
        ThunderDbStack._IMaybeDocState _4_oldState = _source0.dtor_oldState;
        ThunderDbStack._IMaybeDocState _5_newState = _source0.dtor_newState;
        {
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out3;
          _out3 = (this).ApplyDocChangeDeferred(_3_id, _4_oldState, _5_newState);
          events = _out3;
        }
      }
    after_match0: ;
    }
    public void ProcessItem(ThunderDbStack._IStreamItem item, out Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events, out BigInteger queryId)
    {
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
      queryId = BigInteger.Zero;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out0;
      BigInteger _out1;
      (this).ProcessItemDeferred(item, out _out0, out _out1);
      events = _out0;
      queryId = _out1;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _0_retrievalEvents;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out2;
      _out2 = (this).DrainPendingRetrievals();
      _0_retrievalEvents = _out2;
      events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Concat(events, _0_retrievalEvents);
    }
  }
} // end of namespace ThunderDbMutable
namespace ThunderDbMutablePerf {

  public partial class __default {
    public static BigInteger NextState(BigInteger state) {
      BigInteger _0_next = Dafny.Helpers.EuclideanModulus((state) * (ThunderDbMutablePerf.__default.Multiplier), ThunderDbMutablePerf.__default.Modulus);
      if ((_0_next).Sign != 1) {
        return (_0_next) + (ThunderDbMutablePerf.__default.Modulus);
      } else {
        return _0_next;
      }
    }
    public static void NextRand(BigInteger state, out BigInteger nextState, out BigInteger @value)
    {
      nextState = BigInteger.Zero;
      @value = BigInteger.Zero;
      nextState = ThunderDbMutablePerf.__default.NextState(state);
      @value = nextState;
    }
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      ThunderDbMutablePerf.MutablePerfRunner _0_runner;
      ThunderDbMutablePerf.MutablePerfRunner _nw0 = new ThunderDbMutablePerf.MutablePerfRunner();
      _nw0.__ctor();
      _0_runner = _nw0;
      (_0_runner).RunScenario(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("whole-stack-benchmark-like-mutable"), new BigInteger(123), new BigInteger(800), new BigInteger(120), new BigInteger(30), new BigInteger(35), new BigInteger(8), new BigInteger(8), new BigInteger(25), new BigInteger(10), false);
      ThunderDbMutablePerf.MutablePerfRunner _nw1 = new ThunderDbMutablePerf.MutablePerfRunner();
      _nw1.__ctor();
      _0_runner = _nw1;
      (_0_runner).RunScenario(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("whole-stack-benchmark-like-mutable-per-tick"), new BigInteger(123), new BigInteger(800), new BigInteger(120), new BigInteger(30), new BigInteger(35), new BigInteger(8), new BigInteger(8), new BigInteger(25), new BigInteger(10), true);
    }
    public static BigInteger Multiplier { get {
      return new BigInteger(48271);
    } }
    public static BigInteger Modulus { get {
      return new BigInteger(2147483647);
    } }
  }

  public partial class MutablePerfRunner {
    public MutablePerfRunner() {
      this.engine = default(ThunderDbMutable.MutableEngine);
    }
    public ThunderDbMutable.MutableEngine engine {get; set;}
    public void __ctor()
    {
      ThunderDbMutable.MutableEngine _nw0 = new ThunderDbMutable.MutableEngine();
      _nw0.__ctor();
      (this).engine = _nw0;
    }
    public void RunScenario(Dafny.ISequence<Dafny.Rune> name, BigInteger seed, BigInteger documents, BigInteger customers, BigInteger ticks, BigInteger updatesPerTick, BigInteger insertsPerTick, BigInteger deletesPerTick, BigInteger queryLimit, BigInteger density, bool drainPerTick)
    {
      ThunderDbStack._IWorkerRunSummary _0_summary;
      _0_summary = ThunderDbStack.__default.SummaryZero();
      BigInteger _1_rng;
      if ((seed).Sign != 1) {
        _1_rng = BigInteger.One;
      } else {
        _1_rng = seed;
      }
      ThunderDbStack._ISeedDoc[] _2_seedDocs;
      ThunderDbStack._ISeedDoc[] _nw0 = Dafny.ArrayHelpers.InitNewArray1<ThunderDbStack._ISeedDoc>(ThunderDbStack.SeedDoc.Default(), Dafny.Helpers.ToIntChecked(documents, "array size exceeds memory limit"));
      _2_seedDocs = _nw0;
      BigInteger _3_nextDocId;
      _3_nextDocId = documents;
      BigInteger _4_range;
      if ((density).Sign == 0) {
        _4_range = BigInteger.One;
      } else {
        _4_range = (Dafny.Helpers.EuclideanDivision(documents, density)) + (BigInteger.One);
      }
      BigInteger _5_i;
      _5_i = BigInteger.Zero;
      while ((_5_i) < (documents)) {
        BigInteger _6_nextRng;
        BigInteger _7_scoreSeed;
        BigInteger _out0;
        BigInteger _out1;
        ThunderDbMutablePerf.__default.NextRand(_1_rng, out _out0, out _out1);
        _6_nextRng = _out0;
        _7_scoreSeed = _out1;
        _1_rng = _6_nextRng;
        (_2_seedDocs)[(int)((_5_i))] = ThunderDbStack.SeedDoc.create(_5_i, Dafny.Helpers.EuclideanModulus(_7_scoreSeed, _4_range));
        _5_i = (_5_i) + (BigInteger.One);
      }
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _8_seedEvents;
      BigInteger _9_ignoredQueryId;
      Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out2;
      BigInteger _out3;
      (this.engine).ProcessItem(ThunderDbStack.StreamItem.create_SeedDocsItem(Dafny.Helpers.SeqFromArray(_2_seedDocs)), out _out2, out _out3);
      _8_seedEvents = _out2;
      _9_ignoredQueryId = _out3;
      _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _8_seedEvents);
      _5_i = BigInteger.Zero;
      while ((_5_i) < (customers)) {
        BigInteger _10_nextRng1;
        BigInteger _11_widthSeed;
        BigInteger _out4;
        BigInteger _out5;
        ThunderDbMutablePerf.__default.NextRand(_1_rng, out _out4, out _out5);
        _10_nextRng1 = _out4;
        _11_widthSeed = _out5;
        _1_rng = _10_nextRng1;
        BigInteger _12_nextRng2;
        BigInteger _13_minSeed;
        BigInteger _out6;
        BigInteger _out7;
        ThunderDbMutablePerf.__default.NextRand(_1_rng, out _out6, out _out7);
        _12_nextRng2 = _out6;
        _13_minSeed = _out7;
        _1_rng = _12_nextRng2;
        BigInteger _14_width;
        _14_width = (BigInteger.One) + (Dafny.Helpers.EuclideanModulus(_11_widthSeed, (Dafny.Helpers.EuclideanDivision(_4_range, new BigInteger(2))) + (BigInteger.One)));
        BigInteger _15_minScore;
        _15_minScore = Dafny.Helpers.EuclideanModulus(_13_minSeed, _4_range);
        BigInteger _16_maxScore;
        _16_maxScore = (_15_minScore) + (_14_width);
        ThunderDbStack._IQuerySpec _17_spec;
        _17_spec = ThunderDbStack.QuerySpec.create(_15_minScore, _16_maxScore, queryLimit);
        Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _18_events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
        BigInteger _19_queryId = BigInteger.Zero;
        if (drainPerTick) {
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out8;
          BigInteger _out9;
          (this.engine).ProcessItemDeferred(ThunderDbStack.StreamItem.create_QueryAddItem(_17_spec), out _out8, out _out9);
          _18_events = _out8;
          _19_queryId = _out9;
        } else {
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out10;
          BigInteger _out11;
          (this.engine).ProcessItem(ThunderDbStack.StreamItem.create_QueryAddItem(_17_spec), out _out10, out _out11);
          _18_events = _out10;
          _19_queryId = _out11;
        }
        _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _18_events);
        _5_i = (_5_i) + (BigInteger.One);
      }
      if (drainPerTick) {
        Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _20_retrievalEvents;
        Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out12;
        _out12 = (this.engine).DrainPendingRetrievalsGrouped();
        _20_retrievalEvents = _out12;
        _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _20_retrievalEvents);
      }
      BigInteger _21_tick;
      _21_tick = BigInteger.Zero;
      while ((_21_tick) < (ticks)) {
        BigInteger _22_update;
        _22_update = BigInteger.Zero;
        while ((_22_update) < (updatesPerTick)) {
          if ((new BigInteger((this.engine.docIds).Count)).Sign == 1) {
            BigInteger _23_nextRng3;
            BigInteger _24_pickSeed;
            BigInteger _out13;
            BigInteger _out14;
            ThunderDbMutablePerf.__default.NextRand(_1_rng, out _out13, out _out14);
            _23_nextRng3 = _out13;
            _24_pickSeed = _out14;
            _1_rng = _23_nextRng3;
            BigInteger _25_nextRng4;
            BigInteger _26_scoreSeed;
            BigInteger _out15;
            BigInteger _out16;
            ThunderDbMutablePerf.__default.NextRand(_1_rng, out _out15, out _out16);
            _25_nextRng4 = _out15;
            _26_scoreSeed = _out16;
            _1_rng = _25_nextRng4;
            BigInteger _27_picked;
            _27_picked = Dafny.Helpers.EuclideanModulus(_24_pickSeed, new BigInteger((this.engine.docIds).Count));
            BigInteger _28_docId;
            _28_docId = (this.engine.docIds).Select(_27_picked);
            ThunderDbStack._IMaybeDocState _source0 = ThunderDbStack.__default.LookupState(this.engine.store, _28_docId);
            {
              if (_source0.is_NoState) {
                goto after_match0;
              }
            }
            {
              BigInteger _29_docState = _source0.dtor_state;
              {
                BigInteger _30_updatedDocState;
                _30_updatedDocState = Dafny.Helpers.EuclideanModulus(_26_scoreSeed, _4_range);
                Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _31_events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
                BigInteger _32_ignoredQueryId2 = BigInteger.Zero;
                if (drainPerTick) {
                  Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out17;
                  BigInteger _out18;
                  (this.engine).ProcessItemDeferred(ThunderDbStack.StreamItem.create_DocChangeItem(_28_docId, ThunderDbStack.MaybeDocState.create_HasState(_29_docState), ThunderDbStack.MaybeDocState.create_HasState(_30_updatedDocState)), out _out17, out _out18);
                  _31_events = _out17;
                  _32_ignoredQueryId2 = _out18;
                } else {
                  Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out19;
                  BigInteger _out20;
                  (this.engine).ProcessItem(ThunderDbStack.StreamItem.create_DocChangeItem(_28_docId, ThunderDbStack.MaybeDocState.create_HasState(_29_docState), ThunderDbStack.MaybeDocState.create_HasState(_30_updatedDocState)), out _out19, out _out20);
                  _31_events = _out19;
                  _32_ignoredQueryId2 = _out20;
                }
                _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _31_events);
              }
            }
          after_match0: ;
          }
          _22_update = (_22_update) + (BigInteger.One);
        }
        BigInteger _33_insert;
        _33_insert = BigInteger.Zero;
        while ((_33_insert) < (insertsPerTick)) {
          BigInteger _34_nextRng5;
          BigInteger _35_scoreSeed;
          BigInteger _out21;
          BigInteger _out22;
          ThunderDbMutablePerf.__default.NextRand(_1_rng, out _out21, out _out22);
          _34_nextRng5 = _out21;
          _35_scoreSeed = _out22;
          _1_rng = _34_nextRng5;
          BigInteger _36_newDoc;
          _36_newDoc = Dafny.Helpers.EuclideanModulus(_35_scoreSeed, _4_range);
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _37_events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
          BigInteger _38_ignoredQueryId3 = BigInteger.Zero;
          if (drainPerTick) {
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out23;
            BigInteger _out24;
            (this.engine).ProcessItemDeferred(ThunderDbStack.StreamItem.create_DocChangeItem(_3_nextDocId, ThunderDbStack.MaybeDocState.create_NoState(), ThunderDbStack.MaybeDocState.create_HasState(_36_newDoc)), out _out23, out _out24);
            _37_events = _out23;
            _38_ignoredQueryId3 = _out24;
          } else {
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out25;
            BigInteger _out26;
            (this.engine).ProcessItem(ThunderDbStack.StreamItem.create_DocChangeItem(_3_nextDocId, ThunderDbStack.MaybeDocState.create_NoState(), ThunderDbStack.MaybeDocState.create_HasState(_36_newDoc)), out _out25, out _out26);
            _37_events = _out25;
            _38_ignoredQueryId3 = _out26;
          }
          _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _37_events);
          _3_nextDocId = (_3_nextDocId) + (BigInteger.One);
          _33_insert = (_33_insert) + (BigInteger.One);
        }
        BigInteger _39_delete;
        _39_delete = BigInteger.Zero;
        while ((_39_delete) < (deletesPerTick)) {
          if ((new BigInteger((this.engine.docIds).Count)).Sign == 1) {
            BigInteger _40_nextRng6;
            BigInteger _41_pickSeed;
            BigInteger _out27;
            BigInteger _out28;
            ThunderDbMutablePerf.__default.NextRand(_1_rng, out _out27, out _out28);
            _40_nextRng6 = _out27;
            _41_pickSeed = _out28;
            _1_rng = _40_nextRng6;
            BigInteger _42_picked;
            _42_picked = Dafny.Helpers.EuclideanModulus(_41_pickSeed, new BigInteger((this.engine.docIds).Count));
            BigInteger _43_docId;
            _43_docId = (this.engine.docIds).Select(_42_picked);
            ThunderDbStack._IMaybeDocState _source1 = ThunderDbStack.__default.LookupState(this.engine.store, _43_docId);
            {
              if (_source1.is_NoState) {
                goto after_match1;
              }
            }
            {
              BigInteger _44_docState = _source1.dtor_state;
              {
                Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _45_events = Dafny.Sequence<ThunderDbStack._IDownstreamEvent>.Empty;
                BigInteger _46_ignoredQueryId4 = BigInteger.Zero;
                if (drainPerTick) {
                  Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out29;
                  BigInteger _out30;
                  (this.engine).ProcessItemDeferred(ThunderDbStack.StreamItem.create_DocChangeItem(_43_docId, ThunderDbStack.MaybeDocState.create_HasState(_44_docState), ThunderDbStack.MaybeDocState.create_NoState()), out _out29, out _out30);
                  _45_events = _out29;
                  _46_ignoredQueryId4 = _out30;
                } else {
                  Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out31;
                  BigInteger _out32;
                  (this.engine).ProcessItem(ThunderDbStack.StreamItem.create_DocChangeItem(_43_docId, ThunderDbStack.MaybeDocState.create_HasState(_44_docState), ThunderDbStack.MaybeDocState.create_NoState()), out _out31, out _out32);
                  _45_events = _out31;
                  _46_ignoredQueryId4 = _out32;
                }
                _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _45_events);
              }
            }
          after_match1: ;
          }
          _39_delete = (_39_delete) + (BigInteger.One);
        }
        if (drainPerTick) {
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _47_retrievalEvents;
          Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out33;
          _out33 = (this.engine).DrainPendingRetrievalsGrouped();
          _47_retrievalEvents = _out33;
          _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _47_retrievalEvents);
        }
        _21_tick = (_21_tick) + (BigInteger.One);
      }
      if (drainPerTick) {
        Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _48_retrievalEvents;
        Dafny.ISequence<ThunderDbStack._IDownstreamEvent> _out34;
        _out34 = (this.engine).DrainPendingRetrievalsGrouped();
        _48_retrievalEvents = _out34;
        _0_summary = ThunderDbStack.__default.UpdateSummary(_0_summary, _48_retrievalEvents);
      }
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("scenario ")).ToVerbatimString(false));
      Dafny.Helpers.Print((name).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" done: events=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_0_summary).dtor_eventsProcessed));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", matches=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_0_summary).dtor_matchEvents));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", evictions=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_0_summary).dtor_evictions));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", retrievalBatches=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_0_summary).dtor_retrievalBatches));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", retrievalDocs=")).ToVerbatimString(false));
      Dafny.Helpers.Print(((_0_summary).dtor_retrievalDocs));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
    }
  }
} // end of namespace ThunderDbMutablePerf
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => ThunderDbMutablePerf.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
