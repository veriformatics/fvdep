#!/usr/bin/env bash
# U6 Q: the witness corpus (tests/profile/witness.py) + P3/P4's differential (differential.sh).
# Builds the binaries the phase check runs.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "$root"
bash tools/pidns-check.sh || exit 2
mkdir -p tests/profile/.runs
build_log=$root/tests/profile/.runs/witness-build.log
if ! (cd tool && lake build '«fvdep-dev»' '«fvdep-step»' '«fvdep-cli»' '«fvdep-parse»') >"$build_log" 2>&1; then
    tail -n 60 "$build_log" >&2
    exit 2
fi
export FVDEP_BIN=${FVDEP_BIN:-$root/tool/.lake/build/bin/fvdep}
export FVDEP_DEV_BIN=${FVDEP_DEV_BIN:-$root/tool/.lake/build/bin/fvdep-dev}
rc=0
python3 -I tests/profile/witness.py "$@" || rc=$?
# P3 + P4's differential (Q1): the child's trees + grammar order = the frontend's.
bash tests/profile/differential.sh || rc=$((rc > 1 ? rc : 1))
exit "$rc"
