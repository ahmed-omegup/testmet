# Top-K (Limit) Selection & Demand-Aware Buffer

## 1. Goal
Maintain up to `limit` (default 50) documents per query range with minimal recomputation when documents enter/leave due to score changes, inserts, or deletes.

## 2. Problem Statement
When a document leaves the selected set (e.g., score exits range or document deleted), we must "fill the hole" efficiently without rescanning the entire range or re-requesting candidates that are no longer wanted.

## 3. Core Concepts
- Selected Set: The current chosen documents for a query (<= limit).
- Deficit: `limit - selected.len()`; number of additional docs required.
- Cursor: (score, id) tuple marking the last position scanned for this query.
- Demand Buffer (Global): Map<DocId, { score, refcount }>, tracking how many queries still consider the ID a candidate.
- Query Buffer (Local): FIFO queue of candidate DocIds awaiting promotion into Selected.

## 4. Workflow
### Subscription
1. Initial scan from range start populates Selected until limit or exhaustion.
2. Additional candidates (buffer size target = 2 * limit) pushed into Query Buffer; DemandBuffer refcounts incremented.

### Change Event Handling
For each query in addedToQueries / removedFromQueries:
- Entering doc:
  - If Selected not full → add directly.
  - Else ignore (hole-filling only in v1).
- Leaving doc:
  - If in Selected → remove; increment Deficit; schedule refill if not already inflight.
  - If only buffered → drop; decrement DemandBuffer refcount; remove from local buffer.

### Refill Job (Per Query)
While Deficit > 0:
1. Fetch next batch via `iterate_range(min,max,cursor,batch_size)`.
2. For each candidate:
   - Skip if already in Selected.
   - Add to Query Buffer (update DemandBuffer refcount).
3. Promote from Query Buffer front:
   - If still matches range & not selected → move to Selected; decrement refcount (consumed).
   - Else drop & decrement refcount.
4. Advance cursor; repeat until Deficit = 0 or no more candidates.
5. Mark inflight=false.

## 5. Data Structures
```rust
struct QueryState {
  id: QueryId,
  min_score: f64,
  max_score: f64,
  limit: usize,
  selected: HashSet<DocId>,
  buffer: VecDeque<DocId>,
  cursor: Option<(f64, DocId)>,
  deficit: usize,
  inflight: bool,
}

struct CandidateInfo {
  score: f64,
  refcount: u32,
}

struct DemandBuffer {
  map: HashMap<DocId, CandidateInfo>,
}
```

## 6. Invariants (MUST)
- refcount == sum over queries whose local buffer contains the doc and which have not promoted it.
- Selected ∩ Query Buffer = Ø per query.
- refcount == 0 → candidate removed from DemandBuffer immediately.
- Promotion cleans up immediately: when a query promotes a candidate, it is removed from that query’s local buffer and waiting set, the DemandBuffer refcount is decremented, and if the new refcount is 0 the candidate is removed from DemandBuffer at once. Therefore the state "promoted but still present with refcount=0" cannot occur.

## 7. Complexity
- Hole fill: O(b + p) where b = batch size fetched, p = number of promotions (<= deficit).
- Memory: O(Q * limit + C) where Q = queries, C = total distinct candidates buffered.

## 8. Edge Cases
| Case | Handling |
|------|----------|
| No more candidates | Selected size < limit; acceptable (exhaustion). |
| Candidate stale (score changed out of range) | Drop during promotion scan. |
| Simultaneous large removals | Single refill job covers all resulting deficit. |
| Duplicate candidate across queries | Separate refcount increments; consumption decrements accordingly. |

## 9. Future Extensions (MAY)
- Ranking replacement: If doc enters with better score than worst selected.
- Adaptive batch_size based on historical hit rate.
- Multi-field ordering (score + secondary field).
- Persistent cursor after restart.

## 10. API Additions (MUST Implement)
`iterate_range(min: f64, max: f64, start_after: Option<(f64, DocId)>, limit: usize) -> Vec<(DocId, f64)>`
- Ordered ascending by (score, id).
- If start_after == None → begin at first doc >= min.
- Excludes docs with score > max.

## 11. Failure Modes & Recovery
- Panic inside refill job: log, set inflight=false, retry next change event.
- Oversized buffer growth: enforce upper bound (e.g., 4 * limit) per query.

## 12. References
- decisions.md: D004, D005, D006, D007
- change-events.md for integration points

## 13. Buffer Generations & Sharding (SHOULD)

To smooth load and reduce contention, we process candidates in generations and shard the DemandBuffer:

- Generations: Refill work uses the current snapshot of demand; new demand builds the next snapshot. When advancing the generation, each query clears its local waiting set tied to the prior generation. Candidates with refcount>0 persist; candidates that reached refcount==0 are already removed (see invariants).

- Sharding: Partition DemandBuffer by docId hash into N stripes (e.g., 64). Each stripe maintains its own candidate map and a queue of refcount deltas. Structural changes occur under the stripe’s lightweight lock, reducing global contention when many queries reference the same candidates.

## 14. Concurrency & Decrement Strategy (SHOULD)

- Per-candidate state: { score, refcount: AtomicU32 } with a small enum for lifecycle in implementations that adopt sharding.
- Queries enqueue refcount deltas (+1/-1) to their stripe rather than performing synchronous atomics on every event. A periodic flusher applies batched deltas, preserving refcount ≥ 0.
- Change events for a given docId are coalesced over a short tick (e.g., 5–10 ms) so waiting sets and refcounts reflect the net effect of bursty changes.
- Promotion path is atomic with respect to the promoting query: remove from local buffer → decrement refcount → if zero, remove candidate from DemandBuffer.

## 15. Aging, Eviction, and Bounds (SHOULD)

- Each candidate tracks lastTouchedTick; evict the oldest zero-refcount candidates first.
- Enforce hard bounds:
  - Per-query local buffer ≤ 4 × limit (soft cap, drop tail if exceeded).
  - Global candidate count cap; when exceeded, evict zero-count first, then lowest-interest stripes.
- During generation advance, optionally allow a short spillover grace window for still-interesting candidates; otherwise drop them. Promotion already cleans related local entries.

## 16. Metrics & Observability (SHOULD)

Expose counters/gauges/timers to validate behavior and guide tuning:
- total_holes, open_holes
- refill_jobs_started, refill_jobs_failed
- filled_holes_rate/s
- demandbuffer_candidates_total (by stripe)
- avg_waiting_set_size, max_waiting_set_size
- stripe_contention_time_ms
- promotion_latency_ms (first seen → promoted)
- wasted_candidates_per_generation (fetched but never promoted)
