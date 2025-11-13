# Decision Log

Chronological record of significant architectural and implementation decisions.

| Date (UTC) | ID | Decision | Rationale | Alternatives | Status |
|-----------|----|----------|-----------|--------------|--------|
| 2025-11-13 | D001 | Adopt spec-oriented development workflow | Preserve intent & guide incremental evolution | Ad-hoc notes in PR descriptions | ACTIVE |
| 2025-11-13 | D002 | Represent change events as full Documents (not just score) | Future-proof for multi-field queries & richer diffs | Minimal score-only delta | ACTIVE |
| 2025-11-13 | D003 | Exclude intersection from addedTo/removedFrom | Clients care about net movement among queries | Include intersection with a flag | ACTIVE |
| 2025-11-13 | D004 | Use demand-aware candidate buffer (id + refcount) for top-K refill | Avoid re-fetching unused candidates across queries | Block partitioning; full rescans | ACTIVE |
| 2025-11-13 | D005 | Initial top-K fill uses hole-filling only (no ranking replacement) | Simplicity & fast delivery; ranking can be additive later | Immediate heap-based reordering | ACTIVE |
| 2025-11-13 | D006 | Shared iterate_range(min,max,cursor,batch) API | Enables deterministic pagination over ordered docs | Random sampling; full range scans | ACTIVE |
| 2025-11-13 | D007 | Refcount reaches zero → candidate discarded | Prevents stale re-introduction | Time-based eviction | ACTIVE |
| 2025-11-13 | D008 | Promotion cleans buffer entry immediately; zero-count + promoted state impossible | Promotion decrements refcount and removes DemandBuffer entry if it reaches zero, and clears local references | Lazy cleanup after promotion | ACTIVE |
| 2025-11-13 | D009 | Shard DemandBuffer into stripes | Reduce contention on hot candidates and parallelize delta application | Single global lock | ACTIVE |
| 2025-11-13 | D010 | Batch refcount updates via per-stripe delta queues | Lower atomic contention and cache thrash under bursts | Per-event atomic inc/dec | ACTIVE |
| 2025-11-13 | D011 | Optional buffer generations with spillover grace | Smoothen generation switches; avoid allocation storms | Hard reset only | ACTIVE |
| 2025-11-13 | D012 | Introduce core metrics for refill and contention | Enable data-driven tuning and regression detection | Rely on logs only | ACTIVE |
| 2025-11-13 | D013 | Plan LMDB-backed multiplexing of multi-query subscriptions | Deduplicate change event emission when a doc affects many of a user's queries | Per-query independent emission | FUTURE |
| 2025-11-13 | D014 | Column family style selective field materialization | Avoid loading/sending unused document fields to reduce bandwidth & memory | Always send full Document | FUTURE |
| 2025-11-13 | D015 | Aggregate query layer (sum/count instead of raw docs) | Serve analytic subscriptions efficiently; reduce downstream compute | Client-side aggregation of raw events | FUTURE |
| 2025-11-13 | D016 | Mutable queries: shrink/grow without full re-fetch | Reuse in-memory coverage & avoid cold-start hole filling on size/range adjustments | Treat updates as new query registrations | FUTURE |
| 2025-11-13 | D017 | Hierarchical query anatomy (index → filtered → aggregate → user) | Share index slots & avoid duplicating underlying range tracking across derived queries | Flat per-user query registration | FUTURE |
| 2025-11-13 | D018 | Parallel index partitioning by document-id hash | Enable concurrent mutation & lookup; improve scalability on multi-core | Single global treap instance | FUTURE |
| 2025-11-13 | D019 | Non-doc change event variants for aggregates | Emit computed aggregate deltas rather than per-document payloads | Always wrap aggregates in full Document | FUTURE |

## Change Process
- New decision: Append a row with new ID (D###).
- Amendment: Add new row referencing prior ID ("Amends D004") – original row stays.
- Reversal: New row with Status=REVOKED referencing original.

## Pending / Candidate Decisions
- Heap ranking for replacement
- Multi-field composite ordering
- Query state persistence across restarts

