# ThunderDB Limit Stream Layer

Minimal reference implementation of a limit-enforcing stream operator. The layer consumes two asynchronous streams:

1. **Document changes** (upserts / deletions)
2. **Query updates** (registrations / removals with per-query limits)

It emits a third stream describing how each document moves across queries using the shape `{ id, addedTo, removedFrom, evictions }`.

## Quick Start

```bash
cargo test
```

The tests exercise the in-memory `RangeLimitIndex`, showing how the operator reacts to document churn, query updates, and strict-cap evictions. The core pieces live in `src/lib.rs`:

- `LimitIndex` trait abstracts the document index / membership logic
- `spawn_limit_layer` wires change + query streams into an output receiver
- `RangeLimitIndex` is a thread-safe reference implementation using sharded maps

Feel free to swap `RangeLimitIndex` with any structure that implements `LimitIndex` (e.g., Treap, B-Tree) to experiment with different indexing strategies.
