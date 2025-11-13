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
