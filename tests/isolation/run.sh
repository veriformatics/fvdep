#!/usr/bin/env bash
# U5 isolation tests (contract docs/contracts/U5-sandbox.md G1, G3, G4 through D2): builds the dev
# driver + its step helper (built by name: a stale helper ran unguarded once), then every case
# (`--case <substring>` narrows).
set -euo pipefail
cd "$(dirname "$0")/../.."
# The steps run fvdep-step: on vflab (shared) only inside a PID namespace of this job's own.
bash tools/pidns-check.sh || exit 2
(cd tool && lake build -q «fvdep-dev» «fvdep-step»)
exec python3 -I tests/isolation/run.py "$@"
