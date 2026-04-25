include "ThunderDbStack.dfy"

module ThunderDbMutable {
  import opened DocsIndexModel
  import opened DocsIndexTreap
  import opened ThunderDbStack

  const NegInfInt: int := -2147483647
  const NegInfScore: Score := -2147483647

  datatype QueryIndexEntry = QueryIndexEntry(id: QueryId, baseScore: int, maxCap: Score)
  datatype QueryState = QueryState(spec: QuerySpec, currentMatches: nat, baseScore: int)

  datatype QueryTree =
    | QEmpty
    | QNode(
        key: Score,
        prio: int,
        add: int,
        localAdd: int,
        items: seq<QueryIndexEntry>,
        subtreeMax: int,
        localMaxCap: Score,
        subtreeMaxCap: Score,
        left: QueryTree,
        right: QueryTree)

  datatype QueryTreePair = QueryTreePair(left: QueryTree, right: QueryTree)

  function MaxInt(a: int, b: int): int {
    if a >= b then a else b
  }

  function MaxScore(a: Score, b: Score): Score {
    if a >= b then a else b
  }

  function InsertQueryIndexEntry(items: seq<QueryIndexEntry>, entry: QueryIndexEntry): seq<QueryIndexEntry> {
    if |items| == 0 then [entry]
    else if entry.baseScore < items[0].baseScore || (entry.baseScore == items[0].baseScore && entry.id < items[0].id) then [entry] + items
    else [items[0]] + InsertQueryIndexEntry(items[1..], entry)
  }

  function RemoveQueryIndexEntry(items: seq<QueryIndexEntry>, id: QueryId, baseScore: int, maxCap: Score): seq<QueryIndexEntry> {
    if |items| == 0 then []
    else if items[0].id == id && items[0].baseScore == baseScore && items[0].maxCap == maxCap then items[1..]
    else [items[0]] + RemoveQueryIndexEntry(items[1..], id, baseScore, maxCap)
  }

  function MaxBaseScore(items: seq<QueryIndexEntry>): int {
    if |items| == 0 then NegInfInt else MaxInt(items[0].baseScore, MaxBaseScore(items[1..]))
  }

  function MaxCapScore(items: seq<QueryIndexEntry>): Score {
    if |items| == 0 then NegInfScore else MaxScore(items[0].maxCap, MaxCapScore(items[1..]))
  }

  function CollectLocalIds(items: seq<QueryIndexEntry>, accHere: int, cutoff: int, value: Score): seq<QueryId>
    decreases |items|
  {
    if |items| == 0 then []
    else if items[0].maxCap >= value && items[0].baseScore + accHere > cutoff
      then [items[0].id] + CollectLocalIds(items[1..], accHere, cutoff, value)
      else CollectLocalIds(items[1..], accHere, cutoff, value)
  }

  function UniqueConcatQueryIds(left: seq<QueryId>, right: seq<QueryId>): seq<QueryId>
    decreases |right|
  {
    if |right| == 0 then left
    else UniqueConcatQueryIds(AppendQueryIdUnique(left, right[0]), right[1..])
  }

  function QueryNodeCount(tree: QueryTree): nat {
    if tree.QEmpty? then 0 else 1 + QueryNodeCount(tree.left) + QueryNodeCount(tree.right)
  }

  function QuerySubMax(tree: QueryTree): int {
    if tree.QEmpty? then NegInfInt else tree.subtreeMax
  }

  function QuerySubCap(tree: QueryTree): Score {
    if tree.QEmpty? then NegInfScore else tree.subtreeMaxCap
  }

  function QueryPriorityForKey(key: Score): int {
    ((key + 1) * 1103515245 + 12345) % 2147483647
  }

  function QueryPush(tree: QueryTree): QueryTree
    requires tree.QNode?
  {
    if tree.add == 0 then tree else
      var left2 :=
        if tree.left.QEmpty? then QEmpty
        else QNode(tree.left.key, tree.left.prio, tree.left.add + tree.add, tree.left.localAdd, tree.left.items,
                   if tree.left.subtreeMax == NegInfInt then NegInfInt else tree.left.subtreeMax + tree.add,
                   tree.left.localMaxCap, tree.left.subtreeMaxCap, tree.left.left, tree.left.right);
      var right2 :=
        if tree.right.QEmpty? then QEmpty
        else QNode(tree.right.key, tree.right.prio, tree.right.add + tree.add, tree.right.localAdd, tree.right.items,
                   if tree.right.subtreeMax == NegInfInt then NegInfInt else tree.right.subtreeMax + tree.add,
                   tree.right.localMaxCap, tree.right.subtreeMaxCap, tree.right.left, tree.right.right);
      QNode(tree.key, tree.prio, 0, tree.localAdd + tree.add, tree.items, tree.subtreeMax, tree.localMaxCap, tree.subtreeMaxCap, left2, right2)
  }

  function QueryPull(tree: QueryTree): QueryTree
    requires tree.QNode?
  {
    var localCap := MaxCapScore(tree.items);
    var localMax := if |tree.items| == 0 then NegInfInt else MaxBaseScore(tree.items) + tree.localAdd;
    var merged := MaxInt(localMax, MaxInt(QuerySubMax(tree.left), QuerySubMax(tree.right)));
    QNode(tree.key, tree.prio, tree.add, tree.localAdd, tree.items,
          if merged == NegInfInt then NegInfInt else tree.add + merged,
          localCap,
          MaxScore(localCap, MaxScore(QuerySubCap(tree.left), QuerySubCap(tree.right))),
          tree.left, tree.right)
  }

  function QueryRotateRight(tree: QueryTree): QueryTree
    requires tree.QNode? && tree.left.QNode?
  {
    var pushed := QueryPush(tree);
    var leftPushed := QueryPush(pushed.left);
    var demoted := QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, leftPushed.right, pushed.right));
    QueryPull(QNode(leftPushed.key, leftPushed.prio, leftPushed.add, leftPushed.localAdd, leftPushed.items, 0, leftPushed.localMaxCap, leftPushed.subtreeMaxCap, leftPushed.left, demoted))
  }

  function QueryRotateLeft(tree: QueryTree): QueryTree
    requires tree.QNode? && tree.right.QNode?
  {
    var pushed := QueryPush(tree);
    var rightPushed := QueryPush(pushed.right);
    var demoted := QueryPull(QNode(pushed.key, pushed.prio, pushed.add, pushed.localAdd, pushed.items, 0, pushed.localMaxCap, pushed.subtreeMaxCap, pushed.left, rightPushed.left));
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

  method QueryInsert(tree: QueryTree, key: Score, id: QueryId, effectiveScore: int, maxCap: Score, accAdd: int) returns (result: QueryTree)
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

  method QueryRemove(tree: QueryTree, key: Score, id: QueryId, baseScore: int, maxCap: Score) returns (result: QueryTree)
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

  method QueryCollectForValue(tree: QueryTree, accAdd: int, cutoff: int, value: Score) returns (out: seq<QueryId>)
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
        rightTree := QNode(rightTree.key, rightTree.prio, rightTree.add + delta, rightTree.localAdd, rightTree.items,
                           if rightTree.subtreeMax == NegInfInt then NegInfInt else rightTree.subtreeMax + delta,
                           rightTree.localMaxCap, rightTree.subtreeMaxCap, rightTree.left, rightTree.right);
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
    var nextQueryId: QueryId

    constructor ()
      ensures this.docs == Empty
      ensures this.store == map[]
      ensures this.docIds == []
      ensures this.queries == map[]
      ensures this.nextQueryId == 1
      ensures this.Ready()
    {
      this.docs := Empty;
      this.store := map[];
      this.docIds := [];
      this.queryIndex := new MutableQueryIndex();
      this.queries := map[];
      this.nextQueryId := 1;
    }

    predicate Ready()
      reads this
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

    method SeedDocs(input: seq<SeedDoc>)
      requires this.Ready()
      ensures this.Ready()
      modifies this
    {
      var i := 0;
      while i < |input|
        invariant 0 <= i <= |input|
        invariant SumConsistent(this.docs)
      {
        this.store := this.store[input[i].id := input[i].state];
        this.docIds := AppendDocIdIfMissing(this.docIds, input[i].id);
        this.docs := Add(this.docs, input[i].state.scoreValue, input[i].id, PriorityFor(input[i].state.scoreValue, input[i].id));
        i := i + 1;
      }
    }

    method AddQuery(spec: QuerySpec) returns (queryId: QueryId, events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      modifies this, this.queryIndex
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
      var retrievals := BuildAddQueryRetrievals(visible, this.store, queryId);
      if |retrievals| == 0 {
        events := [];
      } else {
        events := [RetrievalEvent(retrievals)];
      }
    }

    method RemoveQuery(id: QueryId) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      modifies this, this.queryIndex
      decreases *
    {
      if id in this.queries {
        var state := this.queries[id];
        this.queryIndex.Remove(state.spec.minScore, id, state.baseScore, state.spec.maxScore);
        this.queries := map key | key in this.queries && key != id :: this.queries[key];
      }
      events := [];
    }

    method ApplyDocChange(id: DocId, oldState: MaybeDocState, newState: MaybeDocState) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      ensures this.Ready()
      modifies this, this.queryIndex
      decreases *
    {
      events := [];
      if oldState.HasState? && newState.HasState? && GetScore(oldState.state) == GetScore(newState.state) {
        var covering := this.CollectQueriesForValue(GetScore(oldState.state), id);
        this.store := this.store[id := newState.state];
        if |covering| > 0 {
          events := [MatchEvent(MatchPayload(id, oldState, newState, covering, covering, []))];
        }
        return;
      }

      var oldMatches: seq<QueryId> := [];
      var newMatches: seq<QueryId> := [];
      var queryIndex := this.queryIndex;
      var docsBefore := this.docs;
      
      if oldState.HasState? {
        oldMatches := this.CollectQueriesForValue(GetScore(oldState.state), id);
      }

      if oldState.HasState? {
        this.docs := Remove(this.docs, GetScore(oldState.state), id);
        queryIndex.RangeAddKeysGreaterThan(GetScore(oldState.state), -1);
      }

      if newState.HasState? {
        var newScore := GetScore(newState.state);
        newMatches := this.CollectQueriesForValue(newScore, id);
        this.docs := Add(this.docs, newScore, id, PriorityFor(newScore, id));
        queryIndex.RangeAddKeysGreaterThan(newScore, 1);
        this.store := this.store[id := newState.state];
        this.docIds := AppendDocIdIfMissing(this.docIds, id);
      } else {
        this.store := RemoveStoredDoc(this.store, id);
        this.docIds := RemoveDocId(this.docIds, id);
      }

      var affected := UniqueConcatQueryIds(oldMatches, newMatches);
      var oldMatchMap: map<QueryId, bool> := map[];
      var newMatchMap: map<QueryId, bool> := map[];
      var oi := 0;
      while oi < |oldMatches|
        invariant 0 <= oi <= |oldMatches|
      {
        oldMatchMap := oldMatchMap[oldMatches[oi] := true];
        oi := oi + 1;
      }
      var ni := 0;
      while ni < |newMatches|
        invariant 0 <= ni <= |newMatches|
      {
        newMatchMap := newMatchMap[newMatches[ni] := true];
        ni := ni + 1;
      }

      var evictions: seq<Eviction> := [];
      var retrievals: seq<RetrievalDoc> := [];
      var matchesOld: seq<QueryId> := [];
      var matchesNew: seq<QueryId> := [];
      var i := 0;
      while i < |affected|
        invariant 0 <= i <= |affected|
        invariant SumConsistent(this.docs)
      {
        if affected[i] in this.queries {
          var state := this.queries[affected[i]];
          var oldContains := affected[i] in oldMatchMap;
          var newContains := affected[i] in newMatchMap;
          var newCount := state.currentMatches;
          if oldContains {
            matchesOld := matchesOld + [affected[i]];
          }
          if newContains {
            matchesNew := matchesNew + [affected[i]];
          }

          if oldContains != newContains {
            var oldVisible := TreapCollectRange(docsBefore, state.spec.minScore, state.spec.maxScore, state.spec.limit);
            var newVisible := TreapCollectRange(this.docs, state.spec.minScore, state.spec.maxScore, state.spec.limit);
            newCount := |newVisible|;
            var oldRuntime := QueryRuntime(affected[i], state.spec, oldVisible);
            var newRuntime := QueryRuntime(affected[i], state.spec, newVisible);
            retrievals := retrievals + BuildGapRetrievalForQuery(oldRuntime, newRuntime, this.store, id);
            var evicted := FirstEvicted(oldVisible, newVisible, id);
            if !oldContains && newContains && |evicted| > 0 {
              evictions := evictions + [Eviction(affected[i], evicted[0])];
            }
          }
          this.queries := this.queries[affected[i] := QueryState(state.spec, newCount, state.baseScore)];
        }
        i := i + 1;
      }

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

    method ProcessItem(item: StreamItem) returns (events: seq<DownstreamEvent>, queryId: QueryId)
      requires this.Ready()
      ensures this.Ready()
      modifies this, this.queryIndex
      decreases *
    {
      events := [];
      queryId := 0;
      match item
      case SeedDocsItem(docs) => {
        this.SeedDocs(docs);
      }
      case QueryAddItem(spec) => {
        queryId, events := this.AddQuery(spec);
      }
      case QueryRemoveItem(id) => {
        events := this.RemoveQuery(id);
      }
      case DocChangeItem(id, oldState, newState) => {
        events := this.ApplyDocChange(id, oldState, newState);
      }
    }
  }
}
