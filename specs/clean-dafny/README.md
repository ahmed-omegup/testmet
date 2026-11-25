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

Run the smoke harness with:

```bash
DAFNY_DLL=/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll

/bin/mkdir -p specs/clean-dafny/dist
/usr/bin/dotnet "$DAFNY_DLL" build specs/clean-dafny/CleanPendingSmoke.dfy --no-verify --allow-warnings -o specs/clean-dafny/dist/CleanPendingSmoke
./specs/clean-dafny/dist/CleanPendingSmoke
```