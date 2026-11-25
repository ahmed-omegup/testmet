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

Run the smoke harness with:

```bash
DAFNY_DLL=/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll

/bin/mkdir -p specs/clean-dafny/dist
/usr/bin/dotnet "$DAFNY_DLL" build specs/clean-dafny/CleanPendingSmoke.dfy --no-verify --allow-warnings -o specs/clean-dafny/dist/CleanPendingSmoke
./specs/clean-dafny/dist/CleanPendingSmoke
```