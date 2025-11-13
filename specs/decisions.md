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

## Change Process
- New decision: Append a row with new ID (D###).
- Amendment: Add new row referencing prior ID ("Amends D004") – original row stays.
- Reversal: New row with Status=REVOKED referencing original.

## Pending / Candidate Decisions
- Heap ranking for replacement
- Multi-field composite ordering
- Query state persistence across restarts

