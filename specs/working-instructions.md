# Working Instructions (Persistent)

Last updated: 2025-11-15

This document persists user instructions and our operating agreements. It is authoritative for how we build, communicate, and evolve the system.

## Transparency & Communication
- MUST: Clearly state what is implemented vs. what is planned or not implemented yet. No silent omissions.
- MUST: When a feature is discussed but deferred, record it here and in the roadmap with status.
- MUST: Summarize protocol or behavior changes in PRs/commits and reference the relevant spec section.

## Instruction Retention
- MUST: Persist any instruction given by the user into this file promptly (with date) and adjust specs/roadmap as needed.
- MUST: Keep this file up to date and link it from `specs/README.md`.

## Protocol Agreements
- Notifications over WebSocket (connection-centric):
  - added: `{ type: "added", id, new: { score?, timestamp? } }`
  - updated: `{ type: "updated", id, old: { score?, timestamp? }, new: { score?, timestamp? } }`
  - removed: `{ type: "removed", id, old: { score?, timestamp? } }`
- Subscribed/Unsubscribed server messages include `query_id`; other notifications do not carry `query_id`.
- Keep `waitRegistered`, `rankResult`, and `rangeCountResult` message types for ad-hoc queries and tests.

## Internal Representation & Storage
- Connection IDs are `u64` internally; encoded as fixed 8-byte big-endian in LMDB keys. JSON boundary may expose connection_id as string.
- LMDB map size is configurable via env: `LMDB_MAP_SIZE_BYTES` or `LMDB_MAP_SIZE_MB` (default 10GB).
- Timestamp is a normal field; no special-casing in notifications beyond inclusion in DocState.
- Default subscription limit for tests uses `u32::MAX` unless explicitly specified.

## Multiplexing & Notification Semantics
- Authoritative state: two LMDB maps track (conn,query,doc) transitions and per-(doc,conn) counts.
- Notifications are driven strictly by per-connection counts (0↔>0) rather than per-query payloads.
- Overlapping queries per connection are correctly handled; counts verified by unit tests.

## Hole-Filling (Top-K / Limited Queries)
- Current status: proactive backfill for limited queries is NOT implemented yet.
  - Initial subscribe seeds documents from DB.
  - Inserts/updates add when they cross into a query; deletes emit removed but do not proactively fetch replacements.
- Planned (Roadmap Phase 2): implement a refill job to fill holes for queries with finite `num_docs`.
  - First approach: DB-driven backfill on deficit (fetch next candidates and apply via state machine).
  - Optional: In-memory successor/k-th selection for faster local backfills.

## This Instruction (2025-11-15)
- “Please don’t let me be unaware; make it clear in your instructions. Store every instruction I give.”
  - Actioned: This file created; commitment to update on each new instruction. Transparency rules added above.
