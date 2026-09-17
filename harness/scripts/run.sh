#!/bin/sh
# Replays every scenario under harness/scripts/ and diffs against the recorded
# trace in harness/scripts/expected/.  `./run.sh --record` overwrites them.
set -eu
cd "$(dirname "$0")/../.."
: "${ASAN_OPTIONS:=detect_leaks=0}"
export ASAN_OPTIONS
rc=0
for f in harness/scripts/*.txt; do
  b=$(basename "$f" .txt)
  out=harness/scripts/expected/$b.trace
  if [ "${1:-}" = "--record" ]; then
    ./out/conn_trace --script "$f" > "$out" 2>&1
    echo "recorded $b"
  else
    ./out/conn_trace --script "$f" > "/tmp/$b.trace" 2>&1
    if diff -u "$out" "/tmp/$b.trace" > /dev/null; then
      echo "ok   $b"
    else
      echo "FAIL $b"
      diff -u "$out" "/tmp/$b.trace" || true
      rc=1
    fi
  fi
done
exit $rc
