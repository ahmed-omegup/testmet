# Implementation Roadmap

## Phase 0 (Current)
- Basic replication ingestion
- RangeQueryIndex provides added_to / removed_from sets for score changes
- WebSocket notifications (added/updated/removed)

## Phase 1: ChangeEvent Emission
MUST:
- Introduce Document struct (id, score, timestamp, name?)
- Compute matches(old), matches(new) once; diff sets
- Emit JSON ChangeEvent payload
- Add spec version stub (implicit v1)

SHOULD:
- Strip quotes from column names
- Log extraction latency

## Phase 2: QueryState & Demand Buffer
MUST:
- Introduce QueryState with selected/buffer/cursor/deficit fields
- Implement DemandBuffer (HashMap<DocId, CandidateInfo>)
- Add iterate_range API to doc index
- Initial subscription fill + buffer prefetch
- Hole-filling refill job (single async task per query)

SHOULD:
- Metrics counters (refill_jobs_started, deficits_filled)
- Debug dump endpoint (e.g., /debug/query/{id})
 - Optional: Coalesce change events per docId over a short tick
 - Optional: Shard DemandBuffer into stripes and batch deltas if contention observed

## Phase 3: Robustness & Observability
MUST:
- Panic-safe refill (catch/ log/ retry)
- Enforce buffer size cap (4 * limit)
- Remove candidates promptly when refcount==0

SHOULD:
- Histogram of refill duration
- WAL position tagging (meta.lsn)
 - Stripe contention metrics and delta-queue backlog gauges

## Phase 4: Ranking Improvement (Optional)
MAY:
- Replace worst selected doc if better candidate arrives (heap of selected)
- Configurable ordering direction (ascending/descending score)

## Phase 5: Multi-Field Extensions
MAY:
- Secondary ordering (timestamp)
- Compound filters (score in range AND timestamp in range)

## Phase 6: Persistence & Recovery
MAY:
- Serialize QueryState on shutdown
- WAL resume to reconstruct selected/buffers

## Phase 7: Performance Optimizations
MAY:
- Numeric id mapping (String -> u32)
- Arena allocation for doc storage
- Adaptive batch_size
- Parallel refill jobs under sharded index

## Success Metrics (Tracking)
| Metric | Target |
|--------|--------|
| Refill latency (p95) | < 50ms |
| Deficit duration (p95) | < 100ms |
| Candidate discard rate | < 30% wasted fetches |
| Memory per 100K docs | < 15MB |

## Deferred / Revisit
- Block partitioning (superseded by demand buffer approach unless ranking hotspots emerge)
- Cross-query candidate sharing beyond refcount (e.g., query groups)

## Future Extensions (Not in current phases)
MAY (Planned after Phase 7, detailed in decisions D013–D019):
1. LMDB Multiplexing (D013)
	- Maintain per-user multiplex records so a document's change affecting multiple of the user's queries is serialized once.
	- Dedup logic: union added_to/removed_from across that user's active queries; send single ChangeEvent envelope with arrays of numeric query ids.
	- Storage: LMDB column keyed by user:doc_id -> bitset / compressed list of query ids.
2. Column Families / Selective Field Materialization (D014)
	- Document fields segmented; subscriptions declare needed families.
	- Emission path only hydrates requested families → reduces heap allocations & network payload size.
3. Aggregate Query Layer (D015, D019)
	- Define AggregateEvent variant with sum/count/min/max fields.
	- Maintain incremental aggregates in memory, diff on update, emit delta.
	- Coexist with raw ChangeEvent (client chooses type on subscribe).
4. Query Shrink/Grow (D016)
	- In-place mutation of (min_value, max_value, num_docs) without re-querying historical docs.
	- Recompute only affected suffix/prefix; hole-filling job updated rather than recreated.
5. Hierarchical Query Anatomy (D017)
	- Levels: IndexQuery (range definition) → FilteredQuery (additional predicate) → AggregateQuery (aggregation spec) → UserQuery (connection binding & delivery format).
	- Sharing: Multiple FilteredQuery nodes attach to one IndexQuery; Aggregates attach under filtered leaves.
6. Parallel Index Partitioning (D018)
	- Shard RangeQueryIndex (e.g., consistent hash of doc id) into N partitions.
	- Cross-partition orchestration for queries spanning partitions; each shard maintains local prefix sums.
	- Lock minimization: queries route updates to shard(s) holding affected value ranges.

Acceptance Criteria (Future):
- Multiplexing reduces duplicate per-user ChangeEvent count by >50% on multi-query workloads.
- Aggregate events throughput comparable to raw events (<10% overhead) at 100K updates/min.
- Query mutation latency < 25ms p95 without full re-fetch.
- Parallel partitions scale near-linearly up to number of physical cores for update ingestion.

## References
- decisions.md D001–D012
- change-events.md
- top-k-selection.md
- memory-and-scaling.md

## Progress Snapshot (2025-11-13)

- Phase 0: Baseline ingestion + notifications — in place (verified small-scale).
- Spec groundwork: decisions, change events, top-K design — complete.
- Phase 1: Pending (next to implement).
- Phase 2: Pending design-ready. Sharding/delta batching marked as optional, to be enabled upon contention.

## Status Update (2025-11-15)
- Notifications are connection-centric and include full old/new DocState as agreed.
- Query limits on WebSocket default to `u32::MAX`; no proactive hole-filling yet.
- Hole-filling remains planned in Phase 2; current behavior: deletions reduce counts and emit `removed`, replacements are not fetched proactively.
