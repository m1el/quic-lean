#!/bin/sh
# Links the Lean model with libngtcp2 (ASan + libFuzzer instrumented, see
# build-c/) into harness binaries under out/.  The C that Lean emits is compiled
# here with coverage instrumentation too, so libFuzzer is guided by branches in
# the model as well as in ngtcp2.
set -eu
cd "$(dirname "$0")"
NGTCP2=$(cd "${NGTCP2:-../ngtcp2}" && pwd)
lake build QuicModel
LEAN_PREFIX=$(lean --print-prefix)
mkdir -p out/obj
objs=""
for c in $(find .lake/build/ir/QuicModel .lake/build/ir/QuicModel.c -name '*.c'); do
  o=out/obj/$(echo "$c" | tr '/' '_').o
  clang -c -O1 -g -fsanitize=fuzzer-no-link -I"$LEAN_PREFIX/include" "$c" -o "$o"
  objs="$objs $o"
done
for h in "$@"; do
  clang -g -O1 -fsanitize=address,fuzzer \
    -DHAVE_CONFIG_H -Ibuild-c -I"$NGTCP2/lib" -I"$NGTCP2/lib/includes" -Ibuild-c/lib/includes \
    -I"$LEAN_PREFIX/include" \
    harness/$h.c $objs build-c/lib/libngtcp2.a \
    -L"$LEAN_PREFIX/lib/lean" -lleanshared -Wl,-rpath,"$LEAN_PREFIX/lib/lean" \
    -o out/$h
done
