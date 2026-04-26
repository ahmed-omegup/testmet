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