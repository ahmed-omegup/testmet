# Specification Index

This directory captures specification-oriented development artifacts for the real-time benchmark and the custom B-Tree PubSub server.

## Files
- decisions.md – Time-ordered decision log (architecture & trade-offs)
- change-events.md – Canonical shape of replication-driven change events
- top-k-selection.md – Limit (top-K) maintenance & demand-aware buffer design
- memory-and-scaling.md – Memory model, sizing estimates, optimization levers
- implementation-roadmap.md – Phased plan to evolve toward full change-aware top-K subscriptions

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
