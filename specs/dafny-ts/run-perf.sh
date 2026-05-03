#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
DAFNY_DLL_DEFAULT="/home/asus/.vscode-server/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny.dll"
DAFNY_DLL="${DAFNY_DLL:-$DAFNY_DLL_DEFAULT}"
OUT_DIR="$ROOT_DIR/specs/dafny-ts/dist/TsLimitStreamPerf"

mkdir -p "$ROOT_DIR/specs/dafny-ts/dist"
/usr/bin/dotnet "$DAFNY_DLL" build "$ROOT_DIR/specs/dafny-ts/TsLimitStreamPerf.dfy" --no-verify --allow-warnings -o "$OUT_DIR"
/usr/bin/time -p "$OUT_DIR"