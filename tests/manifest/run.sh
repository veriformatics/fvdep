#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname -- "$0")/../.."
python3 -I tests/manifest/suite.py --oracle-only
(cd tests/manifest && lake build manifest-driver)
python3 -I tests/manifest/suite.py \
    --driver tests/manifest/.lake/build/bin/manifest-driver \
    --report "${FVDEP_MANIFEST_REPORT:-tests/manifest/.results/latest.tsv}" \
    --label "${FVDEP_MANIFEST_LABEL:-current}" "$@"
