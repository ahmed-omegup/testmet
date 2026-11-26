# Implementation Roadmap

## Phase 0 (Current)
- Basic replication ingestion
- RangeQueryIndex provides added_to / removed_from sets for score changes
- WebSocket notifications (added/updated/removed)

## Phase 1: ChangeEvent Emission
MUST:
- Introduce Document struct (id, score, timestamp, name?)
- Compute matches(old), matches(new) once; diff sets
- Emit JSON ChangeEvent payload
- Add spec version stub (implicit v1)

SHOULD:
- Strip quotes from column names
- Log extraction latency

## Phase 2: QueryState & Demand Buffer
MUST:
- Introduce QueryState with selected/buffer/cursor/deficit fields
- Implement DemandBuffer (HashMap<DocId, CandidateInfo>)
- Add iterate_range API to doc index
- Initial subscription fill + buffer prefetch
- Hole-filling refill job (single async task per query)

SHOULD:
- Metrics counters (refill_jobs_started, deficits_filled)
- Debug dump endpoint (e.g., /debug/query/{id})
 - Optional: Coalesce change events per docId over a short tick
 - Optional: Shard DemandBuffer into stripes and batch deltas if contention observed

## Phase 3: Robustness & Observability
MUST:
- Panic-safe refill (catch/ log/ retry)
- Enforce buffer size cap (4 * limit)
- Remove candidates promptly when refcount==0

SHOULD:
- Histogram of refill duration
- WAL position tagging (meta.lsn)
 - Stripe contention metrics and delta-queue backlog gauges

## Phase 4: Ranking Improvement (Optional)
MAY:
- Replace worst selected doc if better candidate arrives (heap of selected)
- Configurable ordering direction (ascending/descending score)

## Phase 5: Multi-Field Extensions
MAY:
- Secondary ordering (timestamp)
- Compound filters (score in range AND timestamp in range)

## Phase 6: Persistence & Recovery
MAY:
- Serialize QueryState on shutdown
- WAL resume to reconstruct selected/buffers

## Phase 7: Performance Optimizations
MAY:
- Numeric id mapping (String -> u32)
- Arena allocation for doc storage
- Adaptive batch_size
- Parallel refill jobs under sharded index

## Success Metrics (Tracking)
| Metric | Target |
|--------|--------|
| Refill latency (p95) | < 50ms |
| Deficit duration (p95) | < 100ms |
| Candidate discard rate | < 30% wasted fetches |
| Memory per 100K docs | < 15MB |

## Deferred / Revisit
- Block partitioning (superseded by demand buffer approach unless ranking hotspots emerge)
- Cross-query candidate sharing beyond refcount (e.g., query groups)

## Future Extensions (Not in current phases)
MAY (Planned after Phase 7, detailed in decisions D013–D019):
1. LMDB Multiplexing (D013)
	- Maintain per-user multiplex records so a document's change affecting multiple of the user's queries is serialized once.
	- Dedup logic: union added_to/removed_from across that user's active queries; send single ChangeEvent envelope with arrays of numeric query ids.
	- Storage: LMDB column keyed by user:doc_id -> bitset / compressed list of query ids.
2. Column Families / Selective Field Materialization (D014)
	- Document fields segmented; subscriptions declare needed families.
	- Emission path only hydrates requested families → reduces heap allocations & network payload size.
3. Aggregate Query Layer (D015, D019)
	- Define AggregateEvent variant with sum/count/min/max fields.
	- Maintain incremental aggregates in memory, diff on update, emit delta.
	- Coexist with raw ChangeEvent (client chooses type on subscribe).
4. Query Shrink/Grow (D016)
	- In-place mutation of (min_value, max_value, num_docs) without re-querying historical docs.
	- Recompute only affected suffix/prefix; hole-filling job updated rather than recreated.
5. Hierarchical Query Anatomy (D017)
	- Levels: IndexQuery (range definition) → FilteredQuery (additional predicate) → AggregateQuery (aggregation spec) → UserQuery (connection binding & delivery format).
	- Sharing: Multiple FilteredQuery nodes attach to one IndexQuery; Aggregates attach under filtered leaves.
6. Parallel Index Partitioning (D018)
	- Shard RangeQueryIndex (e.g., consistent hash of doc id) into N partitions.
	- Cross-partition orchestration for queries spanning partitions; each shard maintains local prefix sums.
	- Lock minimization: queries route updates to shard(s) holding affected value ranges.

Acceptance Criteria (Future):
- Multiplexing reduces duplicate per-user ChangeEvent count by >50% on multi-query workloads.
- Aggregate events throughput comparable to raw events (<10% overhead) at 100K updates/min.
- Query mutation latency < 25ms p95 without full re-fetch.
- Parallel partitions scale near-linearly up to number of physical cores for update ingestion.

## References
- decisions.md D001–D012
- change-events.md
- top-k-selection.md
- memory-and-scaling.md

## Progress Snapshot (2025-11-13)

- Phase 0: Baseline ingestion + notifications — in place (verified small-scale).
- Spec groundwork: decisions, change events, top-K design — complete.
- Phase 1: Pending (next to implement).
- Phase 2: Pending design-ready. Sharding/delta batching marked as optional, to be enabled upon contention.

## Status Update (2025-11-15)
- Notifications are connection-centric and include full old/new DocState as agreed.
- Query limits on WebSocket default to `u32::MAX`; no proactive hole-filling yet.
- Hole-filling remains planned in Phase 2; current behavior: deletions reduce counts and emit `removed`, replacements are not fetched proactively.

## Dafny Integration (2026-11-25)

- The `dafny-integration` branch starts from `main3` and includes the `origin/binclean` Dafny reference, TypeScript-shaped, and clean deferred-engine tracks. The current branch's query-index and SpacetimeDB work is retained.
- `origin/ww` retains an earlier pending-retrieval implementation and handwritten C# benchmark drivers; its generated binaries and host-specific project paths are not incorporated. The clean Dafny engine retains a pending registry, while the newer TypeScript-shaped model uses numbered batches. These lifecycles must be reconciled, including cancellation of an evicted or removed query's in-flight retrieval, before claiming whole-stack parity.
- Local `main2` only moves a binary-search helper in `dynqueries.ts`; it does not change the algorithm. The RethinkDB retest branch changes workload behavior, including upserting missing documents on updates, and removes imports needed by the other backends; it was not adopted as the common benchmark baseline. Its history and results remain on `rethink-retest`.
- The pure Dafny models are reference and proof scaffolding, not a complete replacement for the network, storage, replication, and connection layers. The clean engine's deferred path and the TypeScript batch lifecycle still require cross-implementation tests and contracts for pending and processing races, query removal, and evictions.
- Some smoke and performance harnesses use `assume {:axiom}` or `{:verify false}`. A passing executable parity scenario is not a proof of all behavior.
- Dafny 4.11 verification now runs in a container. With included files checked, the mutable engine, clean pending lemmas, clean parity harness, and TypeScript-shaped retrieval and stream lemmas pass their stated obligations. The mutable engine has no `decreases *` methods: gap filling, query-tree updates, and stream processing now have checked termination. Its current `Ready()` invariant only covers treap sums and is not a full correctness contract.
- The document reference model now verifies sortedness and exact membership for insertion and removal. Treap rank lookup is proved to return the indexed entry or missing, but its full bucket-position and range refinements and update invariants remain open. Clean pending registration is proved to populate both indexes and be idempotent; cancellation preserves unrelated index entries. A complete registry consistency invariant is still needed.
- The TypeScript-shaped retrieval model forbids re-registering a pair currently being processed, unlike the TypeScript worker. A stale nonzero batch hint can resolve a different batch in both implementations; the intended behavior is not yet established. The prior lemma claiming that resolution always removes a document from both batches was false and has been replaced with checked one-batch properties.
- Mutable small and benchmark-like parity scenarios, clean small and medium parity scenarios, retrieval smoke, and document-index lockstep tests ran successfully. The mutable parity harness disables verification; the clean and mutable runs compare finite scenarios, not every execution.
- One release-mode clean benchmark in a container took about 1.31 seconds for 1,651 events, reporting 1,502 matches, 4,159 evictions, 1,344 retrieval batches, and 5,455 retrieval docs. The mutable benchmark runs both immediate and per-tick scenarios in about 3.56 seconds before and 3.19 seconds after the proof changes, with unchanged event summaries but different retrieval counts from the clean engine. These single runs are not a controlled comparison or evidence of an optimization.
- Next: establish a shared whole-stack behavioral contract; resolve the batch registration and stale-hint semantics; prove registry consistency, treap update and range refinements, and whole-engine refinement; remove remaining unproved termination and harness assumptions; then benchmark equivalent workloads before optimizing.

## Dafny Performance Update (2026-11-25)

- Profiling identified recursive sequence slicing and document-map reconstruction as major costs. Equivalent native membership, iterative indexed search/removal, and keyed map removal now have checked Dafny equivalence guarantees. Pending-registry removals use the same keyed map operation.
- The clean engine now verifies without `decreases *`, and its visibility collector has an ordered-filter postcondition. Its readiness predicate and full subscription/delivery semantics are still not proved sufficient for whole-engine correctness.
- Three release-mode clean-engine runs on the same local workload had median wall time 1.253 seconds before and 0.451 seconds after the optimizations, with identical summaries. See `clean-dafny/README.md` for workload, samples, and caveats. The comparison does not establish parity or relative performance against TypeScript.
- Next performance gate: run a shared, identical event stream through both implementations and compare event contents and retrieval timing before interpreting throughput; then profile on larger datasets. Next proof gate: establish the registry invariant and prove treap and whole-engine refinement, including asynchronous delivery races.

## Shared Replay Update (2026-11-25)

- The Dafny cross-trace harness and TypeScript replay now compare identical inputs and per-step match and retrieval contents. The 15-step fixture matches exactly; the 1,651-step workload has zero content mismatches and 1,086 ordering-only differences after sorting IDs within each event for the content comparison. Ordering differences remain observable and are not resolved.
- The shared trace exposed a TypeScript query-difference lower-bound bug, missing notifications for score changes that remain visible, and mishandling of document ID zero. Focused regressions now cover these paths. Match payloads carry full before/after membership so retained subscriptions can receive updates; net added/removed sets must still exclude their intersection as specified by D003.
- A warmed, in-memory replay measured roughly 20.9 ms median in TypeScript versus 227.6 ms in Dafny on this host. These are directional measurements, not a controlled end-to-end ratio: language-specific replay, asynchronous scheduling, and marker delivery differ. See `clean-dafny/README.md` for exact samples and methodology.
- Pending work remains: define event ordering and async retrieval semantics, use a shared persisted trace and equivalent timing boundaries, prove the query-index and whole-engine refinements, and profile larger workloads. Passing this trace is not a proof of all behavior.
