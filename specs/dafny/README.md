# Dafny Models

This directory contains Dafny models/proofs for kernel components.

## Current status

- `DocsIndexModel.dfy`: verified reference model for `thunderdb-ts` docs index semantics.
  - Ordering is lexicographic by `(score, docId)`.
  - `rank(score, null)` = count of entries with `entry.score < score`.
  - `rank(score, id)` = insertion position among entries ordered by `(score, id)`.
  - `countAtMost(score)` counts entries with `entry.score <= score`.
  - `getAtRank(rank)` returns `(score, id, positionWithinScoreBucket)`.
  - `collectRange(min, max, limit)` returns ordered `docId`s in score range, bounded by `limit`.

- `DocsIndexTreap.dfy`: first verified treap implementation layer for docs index.
  - Concrete treap node includes `(score, ids, prio, sum, left, right)`.
  - Includes `add`, `remove`, rotations, and join-based delete behavior.
  - Includes treap query functions: rank / countAtMost / getAtRank / collectRange.
  - Proves core structural obligations for cached subtree sizes (`sum`).
  - Exposes bridge functions to compare treap-entry view against `DocsIndexModel`.
  - Constructively proves refinement for `rank` and `countAtMost` against `DocsIndexModel`.
  - Remaining work is to extend the same style of proof to `getAtRank`, `collectRange`, and update-preservation facts strong enough to show the full `ValidTreap` invariant is preserved by `add`/`remove`.

- `DocsIndexBench.dfy`: executable lockstep harness for runtime testing and benchmark-style runs.
  - Seeds a docs index, then applies update/insert/delete mixes similar in shape to `thunderdb-ts/src/perf.ts`.
  - Checks `Entries`, `ValidTreap`, `rank`, `countAtMost`, `getAtRank`, and `collectRange` against an independent reference sequence model.

- `ThunderDbStack.dfy`: executable whole-stack Dafny reimplementation of the in-process `thunderdb-ts` worker path.
  - Models `seed-docs`, `query-add`, `query-remove`, and `doc-change` stream items.
  - Maintains authoritative doc storage, ordered entries, query visibility caches, retrieval batching, and worker summary accounting.
  - Uses simpler correctness-first state transitions instead of reproducing the TS treap/query-index internals.

- `ThunderDbStackBench.dfy`: pure Dafny end-to-end harness for the full worker stack.
  - Seeds documents, registers queries, runs update/insert/delete ticks, and consumes emitted match/retrieval events.
  - Validates that the externally observed query contents still match the worker's final query views.

This is an executable/spec reference model and proof scaffold. It is intentionally tree-agnostic (sequence-based) so we can first stabilize semantics, then prove treap refinement against this model.

## Verify

Using the VS Code extension-bundled Dafny runtime:

```bash
DAFNY_DLL=/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll

/usr/bin/dotnet "$DAFNY_DLL" verify specs/dafny/DocsIndexModel.dfy
/usr/bin/dotnet "$DAFNY_DLL" verify specs/dafny/DocsIndexTreap.dfy
/usr/bin/dotnet "$DAFNY_DLL" verify specs/dafny/DocsIndexBench.dfy --verify-included-files
/usr/bin/dotnet "$DAFNY_DLL" verify specs/dafny/ThunderDbStack.dfy
/usr/bin/dotnet "$DAFNY_DLL" verify specs/dafny/ThunderDbStackBench.dfy
```

Build the whole-stack harness into `specs/dafny/dist/` and run it from there so generated files stay out of the source tree:

```bash
/bin/mkdir -p specs/dafny/dist
/usr/bin/dotnet "$DAFNY_DLL" build specs/dafny/ThunderDbStackBench.dfy --no-verify -o specs/dafny/dist/ThunderDbStackBench
/usr/bin/time -f 'elapsed=%E user=%U sys=%S maxrss_kb=%M' \
  ./specs/dafny/dist/ThunderDbStackBench
```

Recorded result on this workspace:

```text
scenario whole-stack-small passed: events=311, matches=191, evictions=292, retrievalBatches=191, retrievalDocs=637
scenario whole-stack-benchmark-like passed: events=1651, matches=1048, evictions=3422, retrievalBatches=1105, retrievalDocs=6479
real 64.08
user 60.33
sys 1.54
```

If you prefer your local archive install, replace the `DAFNY_DLL` path accordingly.
