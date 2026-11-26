#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
RUN_ID="$(date +%s)"
OUTPUT_DIR="/tmp/thunderdb-dafny-benchmark-$RUN_ID"
OUTPUT_NAME="CleanLimitMutablePerf400k"
mkdir -p "$OUTPUT_DIR"

docker run --rm \
  -v "$ROOT:/work" \
  -v "$OUTPUT_DIR:/output" \
  -w /work \
  xtrm0/dafny:4.11.0 \
  dafny build specs/dafny-ts/CleanLimitMutablePerf400k.dfy --no-verify --allow-warnings -o "/output/$OUTPUT_NAME"

start_ns="$(date +%s%N)"
RESULT_FILE="$OUTPUT_DIR/result.txt"
start_ns="$(date +%s%N)"
docker run --rm --memory=3g --cpus=2 \
  -v "$OUTPUT_DIR:/output" \
  xtrm0/dafny:4.11.0 \
  dotnet "/output/$OUTPUT_NAME.dll" | tee "$RESULT_FILE"
bench_status="${PIPESTATUS[0]}"
end_ns="$(date +%s%N)"
bench_output="$(cat "$RESULT_FILE")"
if [[ "$bench_status" -ne 0 ]]; then
  exit "$bench_status"
fi

wall_seconds="$(awk -v start="$start_ns" -v end="$end_ns" 'BEGIN { printf "%.3f", (end-start)/1000000000 }')"

if [[ "$bench_output" =~ 350000 ]] && [[ "$bench_output" =~ docs:\ ([0-9]+) ]]; then
  documents=400000
  customers=10000
  changes=350000
  retrieval_docs="${BASH_REMATCH[1]}"
else
  printf '%s\n' "$bench_output" >&2
  echo "Unable to parse Dafny benchmark output" >&2
  exit 1
fi

awk -v seconds="$wall_seconds" \
    -v documents="$documents" \
    -v customers="$customers" \
    -v changes="$changes" \
    -v retrieval_docs="$retrieval_docs" 'BEGIN {
      if (seconds <= 0) seconds = 1
      throughput = changes * 60 / seconds
      reads_per_customer = retrieval_docs * 60 / seconds / customers
      printf "## Dafny Clean Limit Engine\n\n"
      printf "it was able to handle under 3GB memory and 2 vCores:\n"
      printf "* a throughput of %.0f change / minute\n", throughput
      printf "* %d active customer\n", customers
      printf "* %.0f read per customer / minute\n", reads_per_customer
      printf "\n"
      printf "Benchmark: %d documents, %d changes, %d retrieval documents, %.3f seconds\n", documents, changes, retrieval_docs, seconds
    }'
printf '%s\n' "$bench_output"
