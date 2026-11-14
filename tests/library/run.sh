#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
(cd tool && lake build fvdep-dev)
(cd tests/library && lake build library-driver)
# Contract U4 A8: the conformance trial (its build fails unless both statements rest on std axioms).
(cd tests/library/conformance && lake build)
python3 -I tests/library/suite.py \
  --driver tests/library/.lake/build/bin/library-driver \
  --oracle tool/.lake/build/bin/fvdep-dev
