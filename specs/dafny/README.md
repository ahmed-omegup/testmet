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
  - Proves core structural obligations currently focused on cached-sum consistency (`sum`).
  - Exposes bridge functions to compare treap-entry view against `DocsIndexModel`.
  - Declares explicit refinement bridge lemmas (`TreapRankRefinesModel`, `TreapCountAtMostRefinesModel`) that are currently axiomatized to make the contract visible now; these are the next targets for constructive proofs.

This is an executable/spec reference model and proof scaffold. It is intentionally tree-agnostic (sequence-based) so we can first stabilize semantics, then prove treap refinement against this model.

## Verify

Using the VS Code extension-bundled Dafny runtime:

```bash
/usr/bin/dotnet /home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.2/out/resources/4.11.0/github/dafny/Dafny.dll verify specs/dafny/DocsIndexModel.dfy
/usr/bin/dotnet /home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.2/out/resources/4.11.0/github/dafny/Dafny.dll verify specs/dafny/DocsIndexTreap.dfy
```

If you prefer your local archive install, replace the `Dafny.dll` path accordingly.
