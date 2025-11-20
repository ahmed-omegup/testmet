# ThunderDB Limit Stream Layer

Minimal reference implementation of a limit-enforcing stream operator. The layer consumes two asynchronous streams:

1. **Document changes** (upserts / deletions)
2. **Query updates** (registrations / removals with per-query limits)

It emits a third stream describing how each document moves across queries using the shape `{ id, addedTo, removedFrom, evictions }`.

## Quick Start

```bash
cargo test
```

The tests exercise the in-memory `RangeLimitIndex`, showing how the operator reacts to document churn, query updates, and strict-cap evictions. The crate stays tidy by splitting responsibilities across three small modules:

- `src/events.rs` – lightweight data types for the three streams plus an event collector helper
- `src/limit_layer.rs` – `LimitIndex` trait and the `spawn_limit_layer` mux
- `src/range_index.rs` – the default thread-safe implementation (swap this with another tree by re-implementing `LimitIndex`)

Feel free to swap `RangeLimitIndex` with any structure that implements `LimitIndex` (e.g., Treap, B-Tree) to experiment with different indexing strategies.
