#!/bin/sh
# Builds out/quiche_diff: harness/endpoint_diff.c with the quiche engine
# (-DDRIVER_QUICHE, harness/quiche_driver.h) instead of the ngtcp2 one.
#
# QUICHE points at a quiche checkout on the `fuzz-mock-clock` branch (the
# clock::CLOCK patch).  Its static library is built with the `fuzzing` and `ffi`
# features and libFuzzer's coverage instrumentation; --target keeps RUSTFLAGS
# off the build scripts.  libngtcp2 is still linked: the driver builds the
# peer's packets and parses headers with it.
set -eu
cd "$(dirname "$0")"
NGTCP2=$(cd "${NGTCP2:-../ngtcp2}" && pwd)
QUICHE=$(cd "${QUICHE:-../quiche}" && pwd)
TRIPLE=${TRIPLE:-x86_64-unknown-linux-gnu}
( cd "$QUICHE" &&
  RUSTFLAGS="-Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=4 -Cllvm-args=-sanitizer-coverage-inline-8bit-counters -Cllvm-args=-sanitizer-coverage-pc-table -Cllvm-args=-sanitizer-coverage-trace-compares -Ccodegen-units=1" \
  CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true \
  CARGO_TARGET_DIR=target-fuzz \
  cargo build -p quiche --release --features fuzzing,ffi --target "$TRIPLE" )
lake build QuicModel
LEAN_PREFIX=$(lean --print-prefix)
mkdir -p out/obj
objs=""
for c in $(find .lake/build/ir/QuicModel .lake/build/ir/QuicModel.c -name '*.c'); do
  o=out/obj/$(echo "$c" | tr '/' '_').o
  if [ ! -f "$o" ] || [ "$c" -nt "$o" ]; then
    clang -c -O1 -g -fsanitize=fuzzer-no-link -I"$LEAN_PREFIX/include" "$c" -o "$o"
  fi
  objs="$objs $o"
done
clang -g -O1 -fsanitize=address,fuzzer -DDRIVER_QUICHE \
  -DHAVE_CONFIG_H -Ibuild-c -I"$NGTCP2/lib" -I"$NGTCP2/lib/includes" -Ibuild-c/lib/includes \
  -I"$QUICHE/quiche/include" -I"$LEAN_PREFIX/include" -Wno-unused-function \
  harness/endpoint_diff.c $objs build-c/lib/libngtcp2.a \
  "$QUICHE/target-fuzz/$TRIPLE/release/libquiche.a" \
  -L"$LEAN_PREFIX/lib/lean" -lleanshared -Wl,-rpath,"$LEAN_PREFIX/lib/lean" \
  -lpthread -ldl -lm -lstdc++ \
  -o out/quiche_diff
