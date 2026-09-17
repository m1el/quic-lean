#!/bin/sh
# Builds libngtcp2 (static, Debug so asserts stay on) with ASan and libFuzzer
# coverage into build-c/.  NGTCP2 points at an ngtcp2 checkout.
set -eu
cd "$(dirname "$0")"
NGTCP2=$(cd "${NGTCP2:-../ngtcp2}" && pwd)
mkdir -p build-c && cd build-c
CC=clang CFLAGS="-g -O1 -fsanitize=address,fuzzer-no-link" cmake "$NGTCP2" \
  -DENABLE_LIB_ONLY=ON -DENABLE_SHARED_LIB=OFF -DENABLE_OPENSSL=OFF \
  -DBUILD_TESTING=OFF -DCMAKE_BUILD_TYPE=Debug > cmake.log 2>&1
make -j8 ngtcp2_static > make.log 2>&1
