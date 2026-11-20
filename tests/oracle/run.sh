#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "$root"
# Only run steps under the job's own PID namespace on a shared host.
bash tools/pidns-check.sh || exit 2
mkdir -p tests/oracle/.runs
build_log=$root/tests/oracle/.runs/build.log
if ! (cd tool && lake build fvdep-dev «fvdep-step» «fvdep-cli») >"$build_log" 2>&1; then
  tail -n 60 "$build_log" >&2
  exit 2
fi
export FVDEP_BIN=${FVDEP_BIN:-$root/tool/.lake/build/bin/fvdep}
export FVDEP_DEV_BIN=${FVDEP_DEV_BIN:-$root/tool/.lake/build/bin/fvdep-dev}
exec python3 -I tests/oracle/run.py "$@"
