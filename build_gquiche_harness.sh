#!/bin/sh
# Builds out/gquiche_diff: harness/endpoint_diff.c with Google QUICHE -- the QUIC
# implementation of Chrome -- as the engine (-DDRIVER_GQUICHE,
# harness/gquiche_driver.h) instead of ngtcp2.
#
# GQUICHE points at an unmodified checkout of https://github.com/google/quiche.
# QUICHE is C++ and builds with Bazel (bazelisk reads .bazelversion), so
# harness/gquiche is a small Bazel workspace that links gquiche_shim.cc and all
# of QUICHE into out/libgquiche_shim.so, exporting only the gq_* calls of
# harness/gquiche/gquiche_shim.h.  QUICHE's own sources carry libFuzzer's
# coverage instrumentation; its dependencies (BoringSSL, Abseil, protobuf) do
# not.  libngtcp2 is still linked: the driver builds the peer's packets and
# parses headers with it.
set -eu
cd "$(dirname "$0")"
NGTCP2=$(cd "${NGTCP2:-../ngtcp2}" && pwd)
GQUICHE=$(cd "${GQUICHE:-../google-quiche}" && pwd)
BAZEL=${BAZEL:-$(command -v bazelisk || command -v bazel || echo "$HOME/.local/bin/bazelisk")}
mkdir -p out/obj
( cd harness/gquiche &&
  CC=clang CXX=clang++ "$BAZEL" build -c opt --copt=-g1 \
    --override_module=quiche="$GQUICHE" \
    --per_file_copt='quiche/quic/.*\.cc,gquiche_shim\.cc@-fsanitize=fuzzer-no-link' \
    //:libgquiche_shim.so > ../../out/gquiche_shim_build.log 2>&1 ) ||
  { tail -40 out/gquiche_shim_build.log; exit 1; }
cp -f harness/gquiche/bazel-bin/libgquiche_shim.so out/libgquiche_shim.so
chmod u+w out/libgquiche_shim.so
lake build QuicModel
LEAN_PREFIX=$(lean --print-prefix)
objs=""
for c in $(find .lake/build/ir/QuicModel .lake/build/ir/QuicModel.c -name '*.c'); do
  o=out/obj/$(echo "$c" | tr '/' '_').o
  if [ ! -f "$o" ] || [ "$c" -nt "$o" ]; then
    clang -c -O1 -g -fsanitize=fuzzer-no-link -I"$LEAN_PREFIX/include" "$c" -o "$o"
  fi
  objs="$objs $o"
done
clang -g -O1 -fsanitize=address,fuzzer -DDRIVER_GQUICHE \
  -DHAVE_CONFIG_H -Ibuild-c -I"$NGTCP2/lib" -I"$NGTCP2/lib/includes" -Ibuild-c/lib/includes \
  -Iharness -I"$LEAN_PREFIX/include" -Wno-unused-function \
  harness/endpoint_diff.c $objs build-c/lib/libngtcp2.a \
  -Lout -lgquiche_shim -Wl,-rpath,"$(pwd)/out" \
  -L"$LEAN_PREFIX/lib/lean" -lleanshared -Wl,-rpath,"$LEAN_PREFIX/lib/lean" \
  -lpthread -ldl -lm -lstdc++ \
  -o out/gquiche_diff
