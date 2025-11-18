# Specification Index

This directory captures specification-oriented development artifacts for the real-time benchmark and the custom B-Tree PubSub server.

## Files
- decisions.md – Time-ordered decision log (architecture & trade-offs)
- change-events.md – Canonical shape of replication-driven change events
- top-k-selection.md – Limit (top-K) maintenance & demand-aware buffer design
- memory-and-scaling.md – Memory model, sizing estimates, optimization levers
- implementation-roadmap.md – Phased plan to evolve toward full change-aware top-K subscriptions
- glossary-and-status.md – Central glossary, acceptance criteria, risks, and progress snapshot for future sessions
 - working-instructions.md – Persistent user instructions and working agreements

## Goals
1. Persist architectural intent and rationale.
2. Enable incremental implementation (no large refactors without prior spec updates).
3. Provide a stable contract for any client consuming change events.
4. Support future benchmarking comparisons with alternative approaches (e.g., block partitioning, heap-based ranking).

## Conventions
- MUST: Required for correctness.
- SHOULD: Recommended for performance or maintainability.
- MAY: Optional / deferred until needed.
- Decision entries are immutable; corrections are additive with cross-references.

## Update Workflow
1. Propose change → Add/extend spec file section.
2. Get agreement → Implement in code referencing spec section IDs.
3. Log decision in decisions.md.
4. If reverted later → Append a reversal entry; never delete.

## Versioning
Specs tracked in Git; each significant implementation PR should reference spec file + section headers.

## Current Status Snapshot (2025-11-13)

- Agreed concepts captured in specs (D001–D012). Key points:
	- Change events carry full Documents; addedTo/removedFrom exclude intersection.
	- Hole-filling only for top-K (no ranking replacement yet).
	- DemandBuffer stores candidate ids + refcount; promotion decrements and cleans immediately (no zero-count-in-buffer after promotion).
	- iterate_range API planned for deterministic pagination.

- Completed (code):
	- Rust index modularization; small-scale end-to-end flow verified.
	- Timestamp extraction fixes in replication; tester exit reliability improvements.

- Next up (code):
	- Implement ChangeEvent emission (Document struct + diff to queries).
	- Add iterate_range and QueryState + DemandBuffer per top-k-selection.md.
	- Basic metrics counters for refill and buffer sizes.

## How to Continue (for future sessions)

1. Implement Phase 1 in `replication.rs` and `connection_registry.rs` per `implementation-roadmap.md`.
2. Implement `iterate_range` and `QueryState` with local buffer/deficit mechanics per `top-k-selection.md`.
3. Introduce DemandBuffer with refcount and enforce invariants (Section 6), then add optional sharding and delta batching (Sections 13–16) if contention appears.
4. Instrument metrics listed in Sections 16 and memory counters in `memory-and-scaling.md`.

Refer to `implementation-roadmap.md` for acceptance criteria and success metrics.

## Glossary & Acceptance Criteria
See `glossary-and-status.md` for:
- Definitions (Document, QueryState, DemandBuffer, Promotion, Generation, Stripe, etc.)
- Phase acceptance criteria & test plan
- Risks & mitigations, next steps guidance
