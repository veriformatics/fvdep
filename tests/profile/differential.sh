#!/usr/bin/env bash
# U6 P3 + P4 (Q1): the parse's fidelity evidence — `fvdep-dev profile differential` over the witness
# corpus + the boundary fixtures (tests/profile/differential/): the child's trees + grammar order vs
# the frontend's; the library hop's module (`Fvdep.Trial`, importing `Std.Data.HashSet`) compiled
# into a temporary search path first. Exit 0 = every module `same`.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "$root"
dev=$root/tool/.lake/build/bin/fvdep-dev
lib=$(mktemp -d)
trap 'rm -rf "$lib"' EXIT
mkdir -p "$lib/Fvdep"
printf 'import Std.Data.HashSet\n\ndef Fvdep.Trial.sample : Nat := 1\n' >"$lib/Fvdep/Trial.lean"
# From the repository root: elan picks the toolchain by `lean-toolchain` (a CI runner has no default).
lean -R "$lib" -o "$lib/Fvdep/Trial.olean" "$lib/Fvdep/Trial.lean"
"$dev" profile differential --lib=Fvdep.Trial=Std.Data.HashSet "--path=$lib" \
    tests/profile/witness/*.lean tests/profile/differential/*.lean
