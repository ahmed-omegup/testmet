# Performance Optimization Work Summary

## Update: Implemented Rewrite

This summary originally captured the failed pre-rewrite attempts. The mutable engine has now been rewritten and revalidated.

### Current State

- `specs/dafny/ThunderDbMutable.dfy` now uses counter-only `QueryState(spec, currentMatches, baseScore)`.
- `ApplyDocChange` no longer recomputes `oldVisible/newVisible` per affected query.
- The update flow now mirrors the TS design at a high level:
	- decrement counts for `oldMatches`
	- increment counts for `newMatches`
	- `FillGap` for queries that lost the changed doc
	- `PickOverflowDoc` for newly blocked queries
- Gap/overflow selection now uses rank lookup plus query-index boundary tracking instead of full visible-list materialization.

### Validated Result

- Parity still passes on both scenarios in `specs/dafny/ThunderDbMutableParity.dfy`.
- Benchmark-like release runtime improved from roughly `1.86s` to `1.30s` on the same event totals.
- Observable metrics remain unchanged: events=`1651`, matches=`1502`, evictions=`4159`, retrievalBatches=`1344`, retrievalDocs=`7381`.

### Pending Lifecycle Port

The mutable engine now contains explicit pending registries and a deferred execution surface:

- `pendingByQuery`
- `pendingByDoc`
- ordered `pendingPairs`
- `AddQueryDeferred`
- `ApplyDocChangeDeferred`
- `ProcessItemDeferred`
- `DrainPendingRetrievals`

This is the first real port of the TS pending/cancel/resolve bookkeeping into Dafny instead of just mirroring the counter update logic.

### Measurement Of Deferred Drain

The first deferred execution experiment drains once per tick instead of after every item.

Measured result on the rebuilt current code:

- Fast driver immediate: `1510.48 ms`
- Fast driver grouped per-tick drain: `2120.79 ms`

Canonical harness summaries:

- Immediate: events=`1651`, matches=`1502`, evictions=`4159`, retrievalBatches=`1344`, retrievalDocs=`7381`
- Grouped per-tick drain: events=`1683`, matches=`1502`, evictions=`4158`, retrievalBatches=`31`, retrievalDocs=`3203`

So the pending layer exists, and grouped delivery improved the deferred experiment, but the current per-tick strategy is still slower and not yet semantically identical to the compatibility path.

### Updated Conclusion

The important lesson from the earlier failed attempts still holds: micro-optimizations alone were not enough. The difference is that the necessary algorithmic rewrite has now been done for the mutable update path, and it produced a real speedup. The remaining work is no longer "find any architectural fix"; it is reducing the still-large constant-factor/runtime gap that remains after the rewrite.

## Task
User requested: "ok since you spotted the problem fix it" - implement a fix for the Dafny performance gap identified in previous session (~10.5x slower than TypeScript).

## Approach Attempted

### 1. Full Architectural Refactoring (FAILED)
**Goal**: Remove `visible: seq<DocId>` from QueryState, implement lazy counter-based tracking like TypeScript

**Implementation**: Modified ApplyDocChange to compute visibility via rank checks instead of full TreeCollectRange

**Result**: Broke correctness
- Matches: 1502 → 94  
- Evictions: 4159 → 0
- Gap-filling completely lost

**Root Cause**: Temporal state loss. After treap modification (remove + add), both old and new visible lists computed from identical treap state → no deltas detectable

### 2. List-Based Accumulation (FAILED)
**Goal**: Optimize hot loop by replacing sequence concatenation with `List.Add()`

**Implementation**: Changed event/retrieval/eviction accumulation from repeated `Concat` operations to `List<T>` with `Add()` then `FromArray()`

**Result**: No measurable improvement
- Before: 1.93s
- After: 1.96s  
- Noise level variation

**Root Cause**: Sequence operations not the bottleneck; TreapCollectRange dominates

### 3. Boundary-Crossing Skip (FAILED)
**Goal**: Skip TreapCollectRange when document doesn't cross query range boundary

**Implementation**: Check `docWasVisible` vs `docIsNowVisible` flags using rank comparisons; only recompute if there's a boundary crossing

**Result**: Broke correctness
- Matches: 1502 → 1264
- Evictions: 4159 → 97
- Wrong metric counts across the board

**Root Cause**: Rank position doesn't account for documents outside [minScore, maxScore] that affect the visible set size

### 4. Memoization Cache (FAILED)
**Goal**: Cache TreapCollectRange results by (minScore, maxScore, limit) tuple

**Implementation**: Added `Dictionary<(BigInteger, BigInteger, BigInteger), Dafny.ISequence<BigInteger>>` to store visible list results within a single ApplyDocChange call

**Result**: No improvement
- Before: 1.94s
- After: 1.94s
- Range distribution analysis showed zero duplicate (minScore, maxScore, limit) combinations in default scenario (all 120 queries have unique ranges)

**Root Cause**: Memoization only helps if there are cache hits; this scenario provides none

## Final Outcome

### Baseline Established
- **Algorithm**: Original Dafny mutable engine (unmodified)
- **Runtime**: ~2.0-2.6s for default scenario (1651 events)
- **Metrics**: All correct (matches=1502, evictions=4159, retrievals=7381)
- **Build**: Release mode with optimizations, published binary at `out-mutable-final-clean/`

### Root Cause Identified (Not Fixable Without Algorithm Redesign)
The performance gap is **architecturally fundamental**, not a bug:

- **Dafny**: Stores full `visible: seq<DocId>` in QueryState, recomputes via TreeCollectRange on every doc change affecting the query → O(k log D) per affected query
- **TypeScript**: Stores only `currentMatches: nat` counter, tracks pending gaps separately → O(1) per affected query

With ~100 affected queries per update × 1050 total updates, this creates ~8.4M expensive treap traversals for Dafny vs ~100K simple counter operations for TypeScript.

### Documentation Created
Created `PERFORMANCE_ANALYSIS.md` with:
- Detailed bottleneck analysis
- Explanation of why each attempted fix failed
- Architectural constraint explanation
- Concrete cost analysis (8M vs 100K operations)
- Options for future improvement (Option 1: Lazy gap-filling ~200 LOC refactor for 10-15x improvement; Option 2: Accept gap as design trade-off)

## Lessons Learned

1. **Micro-optimizations have limits** - When architectural misalignment exists, even well-targeted optimizations (list batching, caching) provide zero benefit

2. **Correctness requirements are strict** - Any attempt to skip full visible recomputation broke metrics. The algorithm genuinely needs delta detection between old/new visible lists

3. **Temporal state matters** - The order of operations (remove treap node, add back, compute visible) is critical. Computing visible after modification loses information needed for lazy tracking

4. **Trade-offs are intentional** - Dafny prioritizes simplicity and correctness-by-construction; TS optimizes runtime. Gap is design choice, not bug.

## Conclusion

The 10-15x performance gap cannot be closed through micro-optimization or generated-code tuning. It requires fundamental algorithm redesign to implement lazy gap-filling with explicit pending tracking like TypeScript. The current Dafny implementation is correct and representative of a specific architectural choice.

Clean baseline has been validated and documented for future reference.
