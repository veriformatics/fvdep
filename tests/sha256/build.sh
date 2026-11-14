#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p tests/sha256/.build
out="$PWD/tests/sha256/.build"
key=$({ gcc -dumpfullversion; gcc -dumpmachine; sha256sum tests/sha256/build.sh tests/sha256/core_driver.c c/fvdep_sha256_core.c c/fvdep_sha256_core.h; /usr/bin/find vendor/hacl-star -type f -print0 | sort -z | xargs -0 sha256sum; } | sha256sum | cut -d' ' -f1)
if [[ -f "$out/key" && "$(<"$out/key")" == "$key" && -f "$out/outputs.sha256" ]] && sha256sum -c "$out/outputs.sha256" >/dev/null 2>&1; then
  printf 'CONTROL C-build cached byte-identical closure PASS\n'
  exit 0
fi
v="$PWD/vendor/hacl-star/dist"
inc=(-I "$PWD/c" -I "$v/gcc-compatible" -I "$v/karamel/include" -I "$v/karamel/krmllib/dist/minimal")
sources=(tests/sha256/core_driver.c c/fvdep_sha256_core.c)
sanitize=(-std=gnu11 -O1 -g -fno-omit-frame-pointer "-fsanitize=address,undefined" -fno-pie -no-pie)
small=(-DFVDEP_SHA256_ONESHOT_MAX=127 -DFVDEP_SHA256_CHUNK=64 -DFVDEP_SHA256_TOTAL_MAX=513)
gcc "${sanitize[@]}" "${inc[@]}" -c "$v/gcc-compatible/Hacl_Hash_SHA2.c" -o "$out/hacl-sanitized.o"
gcc "${sanitize[@]}" "${inc[@]}" "${sources[@]}" "$out/hacl-sanitized.o" -o "$out/core-normal"
gcc "${sanitize[@]}" "${small[@]}" "${inc[@]}" "${sources[@]}" "$out/hacl-sanitized.o" -o "$out/core-small"
rename=()
for fn in init absorb squeeze; do
  rename+=("-Dfvdep_sha256_${fn}_raw=__wrap_fvdep_sha256_${fn}_raw")
done
rename+=(-Dfvdep_sha256_raw=__wrap_fvdep_sha256_raw)
gcc -std=gnu11 -O2 -fPIC "${small[@]}" "${rename[@]}" "${inc[@]}" -c c/fvdep_sha256_core.c -o "$out/wrapped-core.o"
gcc -std=gnu11 -O2 -fPIC "${inc[@]}" -c "$v/gcc-compatible/Hacl_Hash_SHA2.c" -o "$out/hacl.o"
ar rcs "$out/libsha-small.a" "$out/wrapped-core.o" "$out/hacl.o"
sha256sum "$out/core-normal" "$out/core-small" "$out/libsha-small.a" >"$out/outputs.sha256"
printf '%s\n' "$key" >"$out/key"
printf 'CONTROL C-build ASan+UBSan normal+small; ceilings=127/64/513 PASS\n'
