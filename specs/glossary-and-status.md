# Glossary & Current Status (2025-11-13)

## Glossary
| Term | Definition |
|------|------------|
| Document | Logical row replicated from Postgres (id, score, timestamp, optional name). Represented in Rust as a struct; used for old/new in ChangeEvents. |
| ChangeEvent | Emitted JSON describing a logical INSERT/UPDATE/DELETE with old/new Documents and query membership diffs. |
| Query | A subscription defined by (min_score, max_score, limit). Will have `QueryState` in memory once Phase 2 lands. |
| Selected Set | The current top-K (<= limit) Document IDs for a query. Hole filling only (no ranking replacement yet). |
| Hole / Deficit | limit - selected.len(). Number of additional documents needed. |
| Query Buffer (local) | Per-query FIFO of candidate doc IDs that might fill holes soon. |
| DemandBuffer (global) | Shared map from docId -> candidate metadata (score, refcount). Refcount counts queries still considering the candidate. |
| Refcount | Number of queries whose local buffers include the candidate and have not yet promoted it. Zero triggers removal. |
| Promotion | Moving a candidate from a query's local buffer to its Selected Set; immediate cleanup of candidate's presence for that query. If refcount becomes zero, candidate removed from DemandBuffer. |
| iterate_range | Planned API to scan documents in ordered (score,id) ascending order within a range, starting after a cursor. |
| Cursor | (score, id) tuple marking last scanned position for a query's range iteration. |
| Generation | Optional concept: a snapshot cycle of refill work; per-query waiting sets reset at generation change. |
| Stripe | Shard of the DemandBuffer keyed by hashing docId to reduce contention; each stripe batches refcount deltas. |
| Delta Queue | Per-stripe queue of (+1/-1) refcount updates applied in batches. |
| Spillover | Short-lived set of still-interesting candidates retained temporarily during generation switch. |
| Hole-Filling Strategy | v1 approach: only replace removed items; do not reorder existing Selected documents. |
| Ranking Replacement | Future (Phase 4) optional feature: replacing worst Selected doc if a better candidate arrives. |
| Metrics | Instrumented counters/gauges/histograms providing observability (holes, refill latency, contention). |
| Spec Version | Implicit v1 for ChangeEvents; future breaking changes add a `version` field. |

## Agreed Invariants
- Promotion and zero-count in buffer do not coexist; promotion path decrements and cleans immediately.
- Selected ∩ Query Buffer = Ø per query.
- Refcount == sum of queries whose local buffers still hold the candidate.
- Refcount never negative; zero triggers removal.
- ChangeEvent addedToQueries / removedFromQueries exclude intersection.

## Acceptance Criteria (Summarized)
### Phase 1 (ChangeEvent Emission)
MUST PASS:
- Emit correct JSON for INSERT/UPDATE/DELETE with old/new translation.
- Correct diff sets for addedToQueries and removedFromQueries using one membership computation pass.
- Handle quoted column names (e.g., "timestamp").
- Skip events with missing id or unparsable score safely.
- No panics on malformed replication tuples.

### Phase 2 (QueryState & DemandBuffer)
MUST PASS:
- Subscription initial fill populates Selected up to limit or exhaustion.
- Deficit decreases to zero after refill job completes when enough candidates exist.
- DemandBuffer refcount increments/decrements align with local buffer add/remove/promote.
- Promotion deletes candidate from local buffer; removes from DemandBuffer if refcount reaches zero.
- iterate_range respects min/max bounds and cursor ordering.

### Observability (Phases 2–3)
- Metrics surface: total_holes, refill_jobs_started, promotion_latency_ms.
- Log entry containing Phase and success metrics at startup.

## Module Touchpoints (Implementation Guide)
| Phase | Files Likely Modified | Notes |
|-------|-----------------------|-------|
| 1 | `replication.rs`, `connection_registry.rs`, `websocket.rs`, new `document.rs` | Define Document struct; produce & send ChangeEvents through existing WebSocket pipeline. |
| 2 | `btree_index/range_query_index.rs`, new `query_state.rs`, maybe `btree_index/mod.rs` | Implement iterate_range; introduce QueryState & DemandBuffer, integrate with change handling. |
| 3 | `metrics.rs` (new), `connection_registry.rs`, `replication.rs` | Add instrumentation hooks, latency timing, error counters. |
| 4 | `query_state.rs` | Add ranking replacement (heap) feature. |
| 5+ | Additional modules for persistence & multi-field queries as needed. |

## Test Plan (High-Level)
| Test | Purpose |
|------|---------|
| Insert Event → Added Queries | Validate correct addedToQueries set. |
| Update Score Out of Range | Ensure removedFromQueries contains prior matches. |
| Update Score In Range (no membership change) | addedToQueries & removedFromQueries empty. |
| Delete Document | removedFromQueries lists all affected queries. |
| Subscription Initial Fill | Selected size <= limit; cursor ends at last scanned doc. |
| Hole Fill After Removal | Deficit returns to zero; DemandBuffer cleans candidate. |
| Refcount Zero Removal | Candidate removed promptly; not present next scan. |
| Promotion Path | Candidate moves to Selected; refcount decremented; buffer no stale entry. |
| iterate_range Ordering | Ascending (score,id) sequence without gaps beyond range. |

## Current State Snapshot
- Specs & decisions (D001–D012) finalized for initial implementation.
- Architectural direction: hole-filling model, no ranking replacement yet.
- Pending implementation: Document struct, ChangeEvent emission, iterate_range, QueryState, DemandBuffer, metrics.
- Known future optimizations: sharding, delta queues, ranking replacement, persistence.

## Risks & Mitigations Recap
| Risk | Mitigation |
|------|------------|
| Contention on global DemandBuffer | Stripe sharding (D009) & batched deltas (D010). |
| Candidate churn causing wasted work | Coalesce change events; cap buffer sizes. |
| Large allocation spikes at generation switch | Spillover grace & pooling. |
| Memory overhead for strings | Numeric ID mapping (roadmap Phase 7). |
| Slow hole filling under heavy removal | Adaptive batch_size & early stop once deficit satisfied. |

## Next Steps Guidance (For New Session)
1. Implement Phase 1 acceptance criteria; add `Document` struct and ChangeEvent emission path.
2. Add basic unit tests for ChangeEvent diff logic.
3. Proceed to Phase 2: introduce QueryState and DemandBuffer (single-threaded first).
4. Add metrics counters (holes, refill jobs) before optimizing with stripes.
5. Revisit decisions log when enabling optional features (ranking, sharding).

## References
- `decisions.md` D001–D012
- `change-events.md`
- `top-k-selection.md`
- `implementation-roadmap.md`
- `memory-and-scaling.md`
