# Dafny TS

This folder is a fresh migration track that mirrors the TypeScript structure bottom-up.

Rules for this track:

- migrate one TS component at a time
- keep each component executable and testable in isolation
- verify the component before composing it with the next layer
- prefer faithful naming and state shape over early global optimization
- compose the full engine only after the smaller parts are stable

Planned migration order:

1. `thunderdb-ts/src/retrievalJob.ts`
2. `thunderdb-ts/src/limit-index/LimitQueries.ts`
3. `thunderdb-ts/src/limit-index/limitStream.ts`
4. parity and benchmark harnesses for the composed pipeline

Current component:

- `TsRetrievalRuntime.dfy`: pure Dafny state machine for the retrieval batching worker
- `TsRetrievalLemmas.dfy`: small local facts about the retrieval worker state transitions
- `TsRetrievalSmoke.dfy`: isolated smoke test for the migrated retrieval component
- `TsQueriesRuntime.dfy`: pure Dafny model of the TS `QueriesIndex` behavior
- `TsQueriesLemmas.dfy`: local facts for the query-index state transitions
- `TsQueriesSmoke.dfy`: isolated smoke test for the migrated query-index component
- `TsDocsRuntime.dfy`: pure Dafny model of the TS `DocsIndex` behavior
- `TsDocsLemmas.dfy`: local facts for the docs-index state transitions
- `TsDocsSmoke.dfy`: isolated smoke test for the migrated docs-index component
- `TsLimitQueriesRuntime.dfy`: composed bottom-up port of `LimitQueries.ts`
- `TsLimitQueriesLemmas.dfy`: local facts for the composed limit-queries state transitions
- `TsLimitQueriesSmoke.dfy`: isolated smoke test for the migrated `LimitQueries` component
- `TsLimitStreamRuntime.dfy`: composed bottom-up port of `limitStream.ts`
- `TsLimitStreamLemmas.dfy`: local facts for the stream orchestration state transitions
- `TsLimitStreamSmoke.dfy`: isolated smoke test for the migrated `limitStream` component
- `TsLimitStreamPerfSurface.dfy`: mutable perf-facing shell over the spec stream runtime
- `TsLimitStreamPerfParity.dfy`: bounded parity harness comparing the perf surface against direct spec execution
- `TsLimitStreamPerf.dfy`: runtime benchmark harness for the generated Dafny/C# stream model

## Execution Model

This track now has two distinct goals:

1. Spec model

- The `Ts*Runtime.dfy`, `Ts*Lemmas.dfy`, and `Ts*Smoke.dfy` files are the proof-oriented model.
- These files optimize for clarity, exact state transitions, and verification.
- They are the source of truth for logical behavior.

2. Runtime measurement

- `TsLimitStreamPerf.dfy` is not a proof harness; it is an execution harness for the generated code.
- It exists to answer: how fast is the extracted Dafny runtime on a TS-like workload?
- It is allowed to use build-only assumptions to drive large workloads through the spec runtime.
- `TsLimitStreamPerfSurface.dfy` is the API boundary where a later runtime-oriented implementation can replace the pure model without changing the surrounding harness shape.
- `TsLimitStreamPerfParity.dfy` is the first bounded parity check for that split.

This split is intentional. The pure Dafny state-machine model is appropriate for proving behavior, but it is not the right surface to optimize directly for runtime parity with the mutable TypeScript implementation.

## Current Status

- The proof-oriented stream/query/retrieval layers verify and the smoke harnesses run.
- The generated smoke executables run quickly.
- The generated large-workload benchmark is much slower than the TS perf path, so runtime parity will require a separate runtime-oriented implementation surface instead of further tuning the pure model.

Build smoke harnesses into `specs/dafny-ts/dist/` so generated outputs stay out of the source file list:

```bash
DAFNY_DLL=/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll

/bin/mkdir -p specs/dafny-ts/dist
/usr/bin/dotnet "$DAFNY_DLL" build specs/dafny-ts/TsLimitStreamSmoke.dfy --no-verify --allow-warnings -o specs/dafny-ts/dist/TsLimitStreamSmoke
./specs/dafny-ts/dist/TsLimitStreamSmoke
```

Build and run the generated perf harness the same way:

```bash
DAFNY_DLL=/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll

/bin/mkdir -p specs/dafny-ts/dist
/usr/bin/dotnet "$DAFNY_DLL" build specs/dafny-ts/TsLimitStreamPerf.dfy --no-verify --allow-warnings -o specs/dafny-ts/dist/TsLimitStreamPerf
/usr/bin/time -p ./specs/dafny-ts/dist/TsLimitStreamPerf
```

The current perf harness uses fixed workload constants inside `TsLimitStreamPerf.dfy`, chosen to mirror the large TS run shape rather than command-line arguments or environment variables.