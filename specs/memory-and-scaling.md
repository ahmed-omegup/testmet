# Memory & Scaling Considerations

## 1. Baseline Assumptions
- Document fields stored in memory: id (String or u32), score (f64), timestamp (i32), optional name.
- RangeQueryIndex already maintains balanced trees (treaps) for queries & docs.

## 2. Approximate Per-Document Footprint
| Component | Bytes (Estimate) |
|-----------|------------------|
| id (String ~12–16 chars) | 24–32 (including allocator overhead) |
| score (f64) | 8 |
| timestamp (i32) | 4 |
| Treap node overhead | 40–72 |
| HashMap entry (id -> score/doc) | 24–32 |
| TOTAL per doc | ~100–150 |

## 3. Scale Examples
| Doc Count | Approx Memory |
|-----------|---------------|
| 10K       | 1–1.5 MB |
| 1M        | 100–150 MB |
| 5M        | 500–750 MB (pressure begins) |
| 10M       | 1–1.5 GB (requires tuning) |

## 4. Optimization Levers
| Lever | Effect |
|-------|--------|
| Intern numeric IDs (u32) | Replace heap Strings with compact Vec<String> lookup |
| f32 score if precision ok | Save 4 bytes per doc |
| Packed struct (repr(C)) | Reduce padding |
| Slab allocator / arenas | Lower per-node overhead |
| Compression for cold docs | Trade CPU for memory; not v1 |

## 5. DemandBuffer Bounds
- At worst: queries all buffer distinct candidates → memory ~ Q * limit.
- Practical: overlapping ranges share candidate IDs; refcount reduces duplicates.
- Enforce soft cap: if QueryState.buffer > 4 * limit → truncate tail (older candidates).

## 6. Garbage Collection of Candidates
- Trigger when refcount == 0 → immediate removal.
- Periodic sweep MAY (future) to handle pathological leftover entries.

## 7. Concurrency Model
- Initial: Single-threaded mutation under async mutex for RangeQueryIndex and DemandBuffer (MUST to avoid race complexity initially). Reads (iterate_range) may take immutable lock.
- Scaling path (SHOULD when needed): Shard DemandBuffer (see top-k-selection.md §13). Use per-stripe delta queues to batch refcount updates and minimize atomic contention. Promote under the promoting query's context; enforce invariants that promotion triggers immediate cleanup.

## 8. Backpressure & Throughput
- Large removal bursts cause refill spikes; batch_size adaptation prevents thundering herd.
- Suggested initial batch_size: 256.
- Monitor: refill job count/sec, average deficit duration.

## 9. Observability (SHOULD Add)
Metrics (counter/gauge):
- documents_total, queries_active
- demandbuffer_candidates
- refill_jobs_started, refill_jobs_failed
- avg_deficit_fill_ms
 - stripe_contention_time_ms, delta_queue_backlog

## 10. Risks
| Risk | Mitigation |
|------|------------|
| OOM at very high doc counts | Numeric IDs + struct packing early |
| Long refill latency | Increase batch_size adaptively |
| Lock contention | Later: shard index or use lock-free skiplist |

## 11. Roadmap Hooks
See implementation-roadmap.md for phased memory optimizations.

## 12. References
- decisions.md D002, D004
