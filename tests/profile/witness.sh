#!/usr/bin/env bash
# U6 Q: the witness corpus (tests/profile/witness.py) + P3/P4's differential (differential.sh) +
# P4's pinned scoped namespaces (`fvdep-dev profile scoped --check`). Builds the binaries the phase
# check runs. FVDEP_WITNESS_PART = corpus | differential | scoped runs that part alone (a probe's
# narrowing: a narrowed run never vouches for the stage).
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "$root"
part=${FVDEP_WITNESS_PART:-}
case "$part" in
'' | corpus | differential | scoped) ;;
*)
    echo "witness.sh: FVDEP_WITNESS_PART must be corpus, differential or scoped" >&2
    exit 2
    ;;
esac
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
if [[ -z "$part" || "$part" == corpus ]]; then
    python3 -I tests/profile/witness.py "$@" || rc=$?
fi
# P3 + P4's differential (Q1): the child's trees + grammar order = the frontend's.
if [[ -z "$part" || "$part" == differential ]]; then
    bash tests/profile/differential.sh || rc=$((rc > 1 ? rc : 1))
fi
# P4: the live scoped namespaces over [Init, Std] = the pinned `scopedNamespaces`.
if [[ -z "$part" || "$part" == scoped ]]; then
    "$FVDEP_DEV_BIN" profile scoped --check || rc=$((rc > 1 ? rc : 1))
fi
exit "$rc"
