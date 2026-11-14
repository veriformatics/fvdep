#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
(cd tool && lake build fvdep-dev)
(cd tests/library && lake build library-driver)
python3 -I tests/library/suite.py \
  --driver tests/library/.lake/build/bin/library-driver \
  --oracle tool/.lake/build/bin/fvdep-dev
