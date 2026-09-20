#!/usr/bin/env bash
# Build coverage variants using already-built engine libraries.  First run
# build_harness.sh / build_quiche_harness.sh / build_gquiche_harness.sh for the
# engines wanted.  Usage: ./build_cov.sh [endpoint_diff quiche_diff gquiche_diff]
# Lean-generated C carries both model coverage and libFuzzer instrumentation.
set -euo pipefail
cd "$(dirname "$0")"
NGTCP2=$(cd "${NGTCP2:-../ngtcp2}" && pwd)
LEAN_PREFIX=$(lean --print-prefix)
timeout 300 lake build QuicModel
mkdir -p out/obj-cov
objs=()
while IFS= read -r c; do
  o="out/obj-cov/${c//\//_}.o"
  if [[ ! -f "$o" || "$c" -nt "$o" ]]; then
    clang -c -O1 -g -fsanitize=fuzzer-no-link -fprofile-instr-generate \
      -fcoverage-mapping -I"$LEAN_PREFIX/include" "$c" -o "$o"
  fi
  objs+=("$o")
done < <(find .lake/build/ir/QuicModel .lake/build/ir/QuicModel.c -name '*.c' | sort)
if [[ $# == 0 ]]; then set -- endpoint_diff quiche_diff gquiche_diff; fi
for engine in "$@"; do
  extra=()
  case "$engine" in
    endpoint_diff) ;;
    quiche_diff)
      [[ -n "${QUICHE:-}" || ! -d ../quiche-fuzz-mock-clock ]] || QUICHE=../quiche-fuzz-mock-clock
      QUICHE=$(cd "${QUICHE:-../quiche}" && pwd)
      extra=(-DDRIVER_QUICHE -I"$QUICHE/quiche/include"
        "$QUICHE/target-fuzz/${TRIPLE:-x86_64-unknown-linux-gnu}/release/libquiche.a"
        -lpthread -ldl -lm -lstdc++) ;;
    gquiche_diff)
      extra=(-DDRIVER_GQUICHE -Iharness -Lout -lgquiche_shim
        -Wl,-rpath,"$PWD/out" -lpthread -ldl -lm -lstdc++) ;;
    *) echo "unknown engine: $engine" >&2; exit 2 ;;
  esac
  clang -g -O1 -fsanitize=address,fuzzer -fprofile-instr-generate \
    -fcoverage-mapping -DHAVE_CONFIG_H -Ibuild-c -I"$NGTCP2/lib" \
    -I"$NGTCP2/lib/includes" -Ibuild-c/lib/includes -I"$LEAN_PREFIX/include" \
    -Wno-unused-function harness/endpoint_diff.c "${objs[@]}" \
    build-c/lib/libngtcp2.a "${extra[@]}" \
    -L"$LEAN_PREFIX/lib/lean" -lleanshared -Wl,-rpath,"$LEAN_PREFIX/lib/lean" \
    -o "out/${engine}_cov"
done
