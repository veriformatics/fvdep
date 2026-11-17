#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "$root"
# The steps run fvdep-step: on vflab (shared) only inside a PID namespace of this job's own.
bash tools/pidns-check.sh || exit 2
mkdir -p tests/sandbox/.runs
build_log=$root/tests/sandbox/.runs/build.log
if ! (cd tool && lake build fvdep-dev «fvdep-step» «fvdep-cli») >"$build_log" 2>&1; then
  tail -n 60 "$build_log" >&2
  exit 2
fi
export FVDEP_DEV_BIN=${FVDEP_DEV_BIN:-$root/tool/.lake/build/bin/fvdep-dev}
export FVDEP_BIN=${FVDEP_BIN:-$root/tool/.lake/build/bin/fvdep}
exec python3 -I tests/sandbox/run.py "$@"
