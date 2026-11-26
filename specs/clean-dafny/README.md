# Clean Dafny

This folder is a fresh sibling implementation surface for the next Dafny rewrite.

Goals:

- keep the executable runtime small and direct
- separate proof lemmas from runtime code
- build the new engine bottom-up instead of retrofitting the existing mutable engine
- keep the old `specs/dafny` implementation as the semantic oracle

Current files:

- `CleanPendingRuntime.dfy`: minimal pending-registry runtime with grouped retrieval draining by `docId`
- `CleanPendingLemmas.dfy`: small proof file reserved for pending-registry facts
- `CleanPendingSmoke.dfy`: executable smoke harness for the pending lifecycle
- `CleanLimitEngine.dfy`: first clean deferred engine using the treap plus the pending runtime
- `CleanLimitSmoke.dfy`: executable smoke harness for the clean deferred engine

The intent is to grow this folder in layers:

1. pending lifecycle
2. clean deferred engine
3. whole-stream parity harness
4. proof/refinement layers

## Performance and Verification

On 2026-11-25, three isolated release-mode container runs of `CleanLimitPerf.dfy` took 1.280, 1.230, and 1.253 seconds before the sequence/map changes, and 0.457, 0.451, and 0.448 seconds after them. Median wall time decreased from 1.253 to 0.451 seconds, about 64%. Times include process startup and use the same direct `ProcessItem` benchmark path, Dafny 4.11, C# release build, and .NET 9 runtime. This is a small local sample, not a comparison with TypeScript or a networked service.

All six runs reported 1,651 events, 1,502 matches, 4,159 evictions, 1,344 retrieval batches, and 5,455 retrieval documents. The benchmark uses 800 seeded documents, 120 queries, 30 ticks, 35 updates, 8 inserts, and 8 deletes per tick, with limit 25 and density 10.

- Native sequence membership, indexed document removal, indexed rank search, and keyed map removal are proved equivalent to their previous definitions. Their iterative implementations avoid recursion-depth failures on long sequences.
- The clean engine's methods verify for termination, and its visible-query collector is proved to return the ordered result of its visibility predicate. The predicate itself and the whole engine are not yet proved to implement the complete top-k or delivery contract.
- The small and medium parity scenarios and a 100,000-element sequence smoke test pass. These executable tests do not establish parity for all inputs.

## Correctness Status

- The pending registry's two indexes agree, its lists are nonempty and duplicate-free, and its drain order matches the document index. Registration, cancellation, and resolution preserve these properties.
- The engine establishes and preserves a combined query-registry, pending-registry, document-store, and valid-treap invariant for stream items whose old document state matches the store. This is a proof precondition, not runtime input validation.
- A grouped drain emits only stored pending documents, emits each eligible pending document exactly once with its registered query IDs, and clears the pending registry. A direct quantified per-query delivery postcondition remains unproved.
- Query views are proved equal to the reference top-k range query and contain only stored, in-range documents within the requested limit. Full notification and refill semantics, query match-count correctness, and asynchronous transport behavior remain unproved.
- Repeated seeding of a document replaces its previous tree entry. Seeding after queries are active still lacks a proved policy for updating match counts and notifications.

## Cross-Language Replay

`CleanLimitCrossTrace.dfy` emits JSON lines containing each input, query ID, and downstream events. Its default fixture covers 15 steps, including zero-ID eviction and refill; `workload` emits the 1,651-step benchmark-shaped trace. `thunderdb-ts/scripts/compare-dafny.ts` replays those exact inputs through the TypeScript stream and its actual retrieval worker with an in-memory document source, allowing a drain after each input.

The comparator checks event sequence and batch boundaries and compares query IDs, document IDs, scores, and evictions. It separately counts ordering-only differences inside match arrays and retrieval batches; it does not claim that ordering is unobservable. Query IDs on the TypeScript side are inferred from sequential query-adds because the stream does not return them. A nonzero content-mismatch count causes a failing exit status.

With Dafny 4.11 and .NET available, build and run from the repository root:

```bash
mkdir -p specs/clean-dafny/dist
dafny verify specs/clean-dafny/CleanLimitCrossTrace.dfy --verify-included-files
dafny build specs/clean-dafny/CleanLimitCrossTrace.dfy --no-verify -o specs/clean-dafny/dist/CrossTrace
dotnet build specs/clean-dafny/dist/CrossTrace.csproj -c Release -o specs/clean-dafny/dist/release
npm --prefix thunderdb-ts run compare:dafny -- "$PWD/specs/clean-dafny/dist/release/CrossTrace"
npm --prefix thunderdb-ts run compare:dafny -- --benchmark "$PWD/specs/clean-dafny/dist/release/CrossTrace" workload --timed "$PWD/specs/clean-dafny/dist/release/CrossTrace" benchmark
```

The `benchmark` mode first warms the Dafny engine and captures inputs, then replays them on a fresh engine between output markers. The TypeScript timing runs three replays after its validation pass, without event normalization. In one local run, the 1,651-step trace had zero content mismatches and 1,086 ordering-only differences; TypeScript took 20.21, 28.08, and 20.89 ms, and Dafny took 228.97, 227.57, and 225.00 ms. This indicates a substantial remaining gap, not a definitive ratio: Dafny timing includes marker-delivery overhead through Docker and replays Dafny objects, while TypeScript converts JSON inputs and yields to its asynchronous retrieval worker. Neither includes LMDB or networking, and one trace cannot establish general correctness or asynchronous interleaving parity.

Run the smoke harness with:

```bash
DAFNY_DLL=/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll

/bin/mkdir -p specs/clean-dafny/dist
/usr/bin/dotnet "$DAFNY_DLL" build specs/clean-dafny/CleanPendingSmoke.dfy --no-verify --allow-warnings -o specs/clean-dafny/dist/CleanPendingSmoke
./specs/clean-dafny/dist/CleanPendingSmoke
```