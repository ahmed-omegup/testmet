# Dafny vs TypeScript Performance Gap Analysis

## Update: Current Mutable Engine

The mutable Dafny engine no longer uses the original eager `visible`-sequence recomputation path on document updates.

- `specs/dafny/ThunderDbMutable.dfy` now keeps counter-only `QueryState` and handles updates with the same high-level flow as the TS engine: decrement/increment per-query counts, `fillGap` for lost queries, and overflow selection for newly blocked queries.
- Gap-fill and overflow candidate selection now use treap rank access directly, and the latest revision derives the query start boundary from `baseScore + AccumulatedAddAtKey(minScore)` instead of recomputing `TreapRank(minScore)`.
- The engine now also has persistent pending registries: `pendingByQuery`, `pendingByDoc`, and an ordered `pendingPairs` queue used by `DrainPendingRetrievals`.
- Behavioral parity was revalidated with `ThunderDbMutableParity.dfy` on both the small and benchmark-like scenarios.

## Update: Deferred Drain Experiment

The missing TS-style pending lifecycle was partially ported into the mutable engine, then measured in two execution modes:

- Compatibility path: `ProcessItem` still drains pending retrievals immediately after each logical item using the original pair-ordered retrieval shape.
- Experimental deferred path: `ProcessItemDeferred` leaves pending work queued and the harness drains it once per tick with grouped-by-doc delivery.

Current rebuilt-code results:

- Fast driver immediate: `1510.48 ms`
- Fast driver grouped per-tick drain: `2120.79 ms`
- Canonical release harness running both modes: `3.13 s`

The grouped per-tick drain is materially better than the first naive deferred attempt, but it is still slower than the compatibility path and it still does not preserve exact event totals:

- Immediate canonical summary: events=`1651`, matches=`1502`, evictions=`4159`, retrievalBatches=`1344`, retrievalDocs=`7381`
- Grouped per-tick canonical summary: events=`1683`, matches=`1502`, evictions=`4158`, retrievalBatches=`31`, retrievalDocs=`3203`

That narrows the problem: the deferred path no longer needs another batching rewrite, but it still is not a faithful mirror of the TS retrieval worker lifecycle.

## Current Measurements

Validated release binary timings for the benchmark-like mutable scenario (`800 docs, 120 queries, 30 ticks, 35 updates/tick, 8 inserts/tick, 8 deletes/tick, limit 25, density 10`):

- Historical eager baseline: `1.86s` to `1.95s`
- Current counter/gap-fill port: `1.30s` to `1.36s`
- Improvement: about `30%`

Observed summary is unchanged:

- events=`1651`
- matches=`1502`
- evictions=`4159`
- retrievalBatches=`1344`
- retrievalDocs=`7381`

## Revised Conclusion

The earlier conclusion in this document is outdated. The architectural rewrite did materially reduce runtime while preserving correctness. The remaining gap to TypeScript is still large, but it is no longer accurate to say the mutable Dafny engine "cannot be fixed without redesign" because that redesign has now been implemented in the hot update path.

The current next constraint is narrower: grouped per-tick deferred delivery reduced the experimental cost, but it still changes retrieval semantics and remains slower than immediate draining. The remaining work is to mirror TS delivery/cancellation timing more faithfully and to reduce the constant-factor cost of the pending bookkeeping itself.

## Executive Summary
Dafny implementation is **~15x slower** than TypeScript (2.0s vs 52ms for equivalent ~1650 event scenario). Root cause is **algorithmic, not implementation detail** - cannot be fixed with micro-optimizations.

## Performance Measurements

### Default Scenario (800 docs, 120 queries, 30 ticks, 35 updates/tick = 1050 update events)
- **Dafny**: 1.9-2.0 seconds
- **TypeScript**: ~52 milliseconds  
- **Ratio**: 36-38x in default scenario
- **Events/sec**: Dafny ~850 events/s vs TS ~15,400 events/s

### Bottleneck Analysis

**Dafny Hot Path (ApplyDocChange loop, line 467-478)**
```
For each affected query (typically 80-120 per update):
  1. Compute oldVisible = state.visible (stored in QueryState)
  2. Compute newVisible = TreapCollectRange() - O(log D + k) 
     where D = documents (800), k = query limit (25)
  3. Store newVisible back in QueryState
  4. Detect gaps and evictions by comparing oldVisible vs newVisible
  5. Build gap retrieval requests
```

**Cost per update**: 
- 100 affected queries × O(log 800 + 25) ≈ 100 × 80 = 8,000 treap operations
- 30 ticks × 35 updates = 1,050 total updates
- **Total: ~8.4 million treap traversals**

**TypeScript Equivalent (LimitQueries.ts, lines 152-247)**
```
For each affected query:
  1. Check if doc crossed query range boundary
  2. Increment/decrement counter - O(1)
  3. No full visible list recomputation
  4. Gap-filling is deferred and lazy
```

**Cost per update**:
- 100 affected queries × O(1) = O(100) simple operations
- 1,050 total updates
- **Total: ~100,000 simple counter operations** (840x fewer expensive ops)

## Why Attempted Fixes Failed

### 1. Full Counter Refactoring (Removed `visible` field)
- **Attempted**: Replace `visible: seq<DocId>` with lazy computation
- **Result**: Broken correctness (zero evictions, wrong match counts)
- **Why**: After treap modification, both old and new visible computed from same state
  - Doc removed → treap state A
  - Doc added → treap state B
  - Computing oldVisible from B = same as newVisible from B
  - Delta detection impossible

### 2. List-Based Accumulation (Event batching)
- **Attempted**: Use `List.Add()` instead of sequence concatenation
- **Result**: No measurable improvement (1.93s → 1.96s, within noise)
- **Why**: Sequence concatenation wasn't the bottleneck; TreeCollectRange is

### 3. Boundary-Crossing Optimization (Rank-based skip)
- **Attempted**: Skip recomputation if doc doesn't cross query range boundary  
- **Result**: Broken correctness (match count 1502 → 1264, evictions 4159 → 97)
- **Why**: Rank doesn't consider docs outside [minScore, maxScore] that shift results

### 4. Memoization Cache (Visible list caching)
- **Attempted**: Cache TreapCollectRange results by (minScore, maxScore, limit)
- **Result**: No improvement (1.94s → 1.94s)
- **Why**: Default scenario has zero duplicate query ranges - all 120 queries have unique (min, max, limit)

## Architectural Constraint - Why This Exists

The Dafny algorithm fundamentally requires:
1. Storing full `visible: seq<DocId>` in each QueryState
2. Recomputing on every doc change that affects the query
3. Comparing old vs new to detect gap-filling needs

This is correct but expensive. TS avoids it through:
1. Tracking only `currentMatches: nat` counter (not the full list)
2. Using explicit `pendingByQuery`/`pendingByDoc` sets for gap-filling
3. Gap-fill computation is lazy and deferred, not on update hot path

## What Would Actually Fix This

**Option 1: Lazy Gap-Filling (Best)**
- Remove `visible` field - keep only counter
- Add `pendingByQuery` and `pendingByDoc` maps to track needs
- On document changes: just update counters O(1)
- On gap-fill phase: compute visible lists explicitly, not implicitly
- Estimated effort: 200+ lines of algorithm redesign
- Expected improvement: 10-15x (matching TS performance)

**Option 2: Accept the Gap (Pragmatic)**
- Document Dafny as reference/formal verification implementation
- Use TS for production performance requirements
- Gap is architecture-driven, not a bug

## Validation

All attempted fixes preserved correctness OR broke it. This proves the constraint is real:
- Conservative fixes (memoization, accumulation) had zero impact
- Aggressive fixes (counter tracking, boundary skips) all broke metrics
- Correctness always requires full visible list recomputation

## Conclusion

The 15x performance gap is **not a bug** - it's an architectural design trade-off. The Dafny implementation prioritizes simplicity and correctness-by-construction, while TS optimizes for runtime performance through explicit lazy gap-filling. Closing this gap requires algorithm restructuring, which is beyond incremental optimization scope.

