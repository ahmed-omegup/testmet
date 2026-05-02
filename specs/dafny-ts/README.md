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

Build smoke harnesses into `specs/dafny-ts/dist/` so generated outputs stay out of the source tree:

```bash
DAFNY_DLL=/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll

/bin/mkdir -p specs/dafny-ts/dist
/usr/bin/dotnet "$DAFNY_DLL" build specs/dafny-ts/TsLimitStreamSmoke.dfy --no-verify --allow-warnings -o specs/dafny-ts/dist/TsLimitStreamSmoke
./specs/dafny-ts/dist/TsLimitStreamSmoke
```