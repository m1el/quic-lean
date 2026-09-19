#!/bin/sh
# Builds harness/api_misuse.c twice: against build-c/ (asserts live, as ngtcp2
# ships) into out/api_misuse_assert, and against build-c-ndebug/ (-DNDEBUG,
# see build_ngtcp2.sh) into out/api_misuse_ndebug.  The Lean objects are the
# ones build_harness.sh compiles into out/obj/.
set -eu
cd "$(dirname "$0")"
NGTCP2=$(cd "${NGTCP2:-../ngtcp2}" && pwd)
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
build() { # <build dir> <output> <extra cflags>
  clang -g -O1 -fsanitize=address,fuzzer-no-link $3 \
    -DHAVE_CONFIG_H -I"$1" -I"$NGTCP2/lib" -I"$NGTCP2/lib/includes" -I"$1/lib/includes" \
    -I"$LEAN_PREFIX/include" -Wno-unused-function \
    harness/api_misuse.c $objs "$1/lib/libngtcp2.a" \
    -L"$LEAN_PREFIX/lib/lean" -lleanshared -Wl,-rpath,"$LEAN_PREFIX/lib/lean" \
    -o "$2"
}
build build-c out/api_misuse_assert ""
build build-c-ndebug out/api_misuse_ndebug "-DNDEBUG"
