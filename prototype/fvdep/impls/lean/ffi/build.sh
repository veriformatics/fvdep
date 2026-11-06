#!/bin/sh
# Builds .lake/build/ffi/libfvdep_base64.so from the Lean-generated C of Base64Ffi + every module it
# imports outside Lean's own runtime, plus the C shim. Needs `lake build` first (writes the C).
set -e
cd "$(dirname "$(readlink -f "$0")")/.."
LIB=$(cd ../../library && pwd)
LEAN=$(lean --print-prefix)
OUT=.lake/build/ffi
mkdir -p "$OUT"
cc -DLEAN_EXPORTING -I"$LEAN/include" -shared -fPIC -O2 -o "$OUT/libfvdep_base64.so" \
  .lake/build/ir/Base64Ffi.c .lake/build/ir/Base64Acc.c \
  "$LIB/.lake/build/ir/Fvdep/Abi.c" \
  "$LIB/.lake/build/ir/Fvdep/Base64/Encode/V1_0_0.c" "$LIB/.lake/build/ir/Fvdep/Base64/Decode/V1_0_0.c" \
  ffi/fvdep_base64.c \
  -L"$LEAN/lib/lean" -lleanshared -Wl,-rpath,"$LEAN/lib/lean"
echo "$OUT/libfvdep_base64.so"
