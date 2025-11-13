# Future Extensions (Preview)

This document elaborates on planned features not scheduled for current phases. They are captured in decisions D013–D019.

## 1. LMDB-Based Multiplexing (D013)
Goal: Avoid emitting multiple identical ChangeEvents to a user when one document affects many of their active queries.

### Concept
Maintain per-user multiplex state: user -> { doc_id -> set(query_id) }. When a change arrives:
1. Compute added/removed per query as today.
2. Group by user; collapse into one ChangeEvent envelope containing arrays of addedToQueries / removedFromQueries (numeric IDs).
3. Persist updated mapping for differential emission next time.

### Storage Shape
```
user:{id}:doc:{doc_id} => bitset / varint-packed list of query_ids
```
Bitset chosen for dense query sets; fallback to delta-encoded list for sparse sets.

### Benefits
- Bandwidth reduction for users with many overlapping ranges.
- Lower serialization CPU.

### Open Questions
- TTL for inactive doc entries.
- Bitset vs RoaringBitmap trade-offs.

## 2. Column Families / Selective Field Materialization (D014)
Goal: Limit payload fields to those a subscription declares.

### Approach
Define field families (core: id, score; temporal: timestamp; extended: name, tags, etc.). Subscription includes `fields: ["core", "temporal"]`.
ChangeEvent builder hydrates only requested families from replication tuples.

### Benefits
- Reduced network and allocation overhead.
- Clear contract for forward-compatible field additions.

### Edge Cases
- Missing requested family -> emit with `"partial": true` flag? (TBD)

## 3. Aggregate Query Layer (D015, D019)
Goal: Provide derived metrics (count, sum, min, max) instead of raw document lists when desired.

### Data Structures
Maintain per-query aggregate state:
```
AggState { count: u64, sum_score: f64, min_score: f64, max_score: f64 }
```
On update/delete/insert adjust aggregates incrementally. Emit `AggregateEvent`:
```
{
  "type": "aggregateEvent",
  "queryId": 42,
  "delta": { "count": +1, "sumScore": +57.3 },
  "current": { "count": 1200, "sumScore": 55321.8 }
}
```
### Benefits
- Lower downstream compute, push-based analytics.

### Considerations
- Consistency under partitioned index (see section 6).

## 4. Query Shrink/Grow (D016)
Goal: Mutate existing query coverage without treating it as a cold-start.

### Mechanics
- Shrink: remove upper/lower value ranges; adjust internal prefix sums; mark removed docs for potential Removed events.
- Grow: extend range; schedule hole-filling job seeded from in-memory index (no immediate DB full scan).

### Invariants
- Existing selected set preserved; only newly covered area triggers fill.
- No duplicate events during mutation window.

## 5. Hierarchical Query Anatomy (D017)
Layered model:
1. IndexQuery: Base range (min, max, num_docs).
2. FilteredQuery: Adds predicates (customer_id, tag, etc.).
3. AggregateQuery: Derives metrics from upstream (Index or Filtered).
4. UserQuery: Binds connection(s) + delivery format (raw vs aggregate).

### Benefits
- Reuse underlying range coverage and candidate buffers.
- Modular evolution (add new predicate types without changing index core).

## 6. Parallel Index Partitioning (D018)
Goal: Scale update throughput with core count.

### Partition Strategy
Hash(doc_id) % N -> shard. Each shard owns a DocsTreap + QueriesTreap segment.
Global queries spanning shards maintain per-shard partial prefix sums aggregated on read.

### Concurrency
- Shard-local locks only.
- Cross-shard query mutation orchestrator uses batched RPC-like calls.

### Metrics
- per_shard_update_latency
- cross_shard_query_mutation_latency

## Acceptance Targets (Future)
| Feature | Target |
|---------|--------|
| Multiplex dedup | >50% reduction duplicate per-user events |
| Aggregate overhead | <10% vs raw ChangeEvent path |
| Query mutation latency | p95 < 25ms |
| Partition scaling | ~linear until memory bandwidth saturation |

## Compatibility & Versioning
Each introduced feature increments a spec minor version; breaking payload changes require major version bump and dual emission (old + new) during transition.

## Next Steps
1. Prototype multiplexing bitset in LMDB behind feature flag.
2. Define field family registry and subscription syntax.
3. Introduce AggregateEvent type & integration tests.
4. Implement shrink/grow mutation operations + tests.
5. Shard index; benchmark update throughput.

---
Status: DOCUMENTED (no implementation started). Update decisions table if scope changes.
