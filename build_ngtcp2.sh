#!/bin/sh
# Builds libngtcp2 (static, Debug so asserts stay on) with ASan and libFuzzer
# coverage into build-c/.  NGTCP2 points at an ngtcp2 checkout.
# BUILD_DIR=build-c-ndebug EXTRA_CFLAGS=-DNDEBUG compiles the asserts out, ASan
# still on (harness/api_misuse.c).  The build type alone does not: ngtcp2's
# CMakeLists.txt strips -DNDEBUG from Release flags on purpose, so a standard
# build ships with its asserts live.
set -eu
cd "$(dirname "$0")"
NGTCP2=$(cd "${NGTCP2:-../ngtcp2}" && pwd)
BUILD_DIR=${BUILD_DIR:-build-c}
BUILD_TYPE=${BUILD_TYPE:-Debug}
mkdir -p "$BUILD_DIR" && cd "$BUILD_DIR"
CC=clang CFLAGS="-g -O1 -fsanitize=address,fuzzer-no-link ${EXTRA_CFLAGS:-}" cmake "$NGTCP2" \
  -DENABLE_LIB_ONLY=ON -DENABLE_SHARED_LIB=OFF -DENABLE_OPENSSL=OFF \
  -DBUILD_TESTING=OFF -DCMAKE_BUILD_TYPE="$BUILD_TYPE" > cmake.log 2>&1
make -j8 ngtcp2_static > make.log 2>&1
