#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "$root"
bash tools/pidns-check.sh || exit 2
mkdir -p tests/profile/.runs
build_log=$root/tests/profile/.runs/build.log
if ! (
    cd tool
    targets=('«fvdep-dev»' '«fvdep-step»' '«fvdep-cli»')
    if grep -Eq '^lean_exe[[:space:]]+(«fvdep-parse»|fvdep-parse)([[:space:]]|$)' lakefile.lean; then
        targets+=('«fvdep-parse»')
    fi
    lake build "${targets[@]}"
) >"$build_log" 2>&1; then
    tail -n 60 "$build_log" >&2
    exit 2
fi
export FVDEP_BIN=${FVDEP_BIN:-$root/tool/.lake/build/bin/fvdep}
export FVDEP_DEV_BIN=${FVDEP_DEV_BIN:-$root/tool/.lake/build/bin/fvdep-dev}
exec python3 -I tests/profile/run.py "$@"
