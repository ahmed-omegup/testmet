# Connection-Centric Change Notifications (Current Spec)

This document describes the current, connection-centric event model used by the B-Tree PubSub worker. It supersedes earlier query-centric “ChangeEvent” drafts.

## Goals
- Notify each connection about document changes it cares about.
- Keep queries as internal routing state only; they MUST NOT appear in the payload.
- Scale via LMDB multiplexing and binary keys; support u32 document IDs end-to-end.

## Payloads (WebSocket)
- added: `{ "type": "added", "id": u32, "score": i32, "timestamp": i32 }`
- updated: `{ "type": "updated", "id": u32, "score": i32, "timestamp": i32 }`
- removed: `{ "type": "removed", "id": u32 }`

Notes:
- `timestamp = -1` is used as a cleanup signal (e.g., final drain); otherwise timestamp reflects the latest DB value when available.
- No `query_id` is included. A connection may have multiple queries; the server deduplicates per-connection and emits a single event per document change.

## Semantics
- Insert: emit `added` to every connection that has at least one query matching the new document.
- Update: for every connection, compute before/after membership across all its queries for this document:
  - If it transitions from not-watched → watched: emit `added`.
  - If it stays watched: emit `updated` (with new score/timestamp).
  - If it transitions from watched → not-watched: emit `removed`.
- Delete: emit `removed` to every connection that was watching the document.

## Routing and Multiplexing
- In-memory index: `RangeQueryIndex` tracks query definitions and which documents they match; it also maps `query_id -> {connections}`.
- LMDB:
  - `connection_documents` (Bytes → I8): key `[conn][0x00][query_id:BE u32][doc_id:BE u32]` → state (-1,0,1)
  - `document_connections` (Bytes → U32): key `[doc_id:BE u32][0x00][conn]` → per-connection refcount
  - State machine: replication inserts/updates set state→1; DB backfill applies -1→0, 0→1, 1→1; deletions drop the key or set -1 and decrement counts.
  - Keys are binary for performance; IDs are `u32`.

## Type Discipline
- Document IDs: `u32` everywhere (DB INTEGER, replication decode, indexes, LMDB keys, notifications).
- Query IDs: internal only (u32); never exposed in notifications.

## Ordering & Idempotency
- Events follow logical replication order; per-connection dedup ensures at most one event per document change.
- Clients can treat `updated` idempotently and recompute view state.

## Backfill / Subscription
- On subscribe, the server queries the DB and applies results to LMDB using the state machine, then sends `{ type: "subscribed", initial_count }`.
- Subsequent replication changes drive `added`/`updated`/`removed`.

## Implementation Notes
- WebSocket sender forwards `Notification` from `ConnectionRegistry` directly; these are already connection-scoped payloads.
- `broadcast_timestamp_update` emits `updated` with current timestamp and `score=0` when only timestamp changes.
- Retrieval-job arrivals (waitForDoc) also emit `added` per connection watching queries that reference the arrived doc.

## Open Items
- Optional: expose a debug/admin endpoint to list LMDB entries per connection.
- Optional: batch multiple doc events into a single frame if needed.
