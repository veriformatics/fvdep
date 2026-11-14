#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d "$PWD/tests/codec/.run.XXXXXX")
trap 'rm -rf -- "$work"' EXIT
python3 -I tests/codec/freeze_jh.py
python3 -I tests/codec/freeze_jhd.py
(cd tests/sha256/nist && sha256sum -c SHA256SUMS)
bash tests/sha256/build.sh
(cd tests/codec && lake build codec-driver codec-driver-small)
base=0
python3 -I tests/codec/suite.py \
  --driver tests/codec/.lake/build/bin/codec-driver \
  --work "$work" \
  --report "${FVDEP_CODEC_REPORT:-tests/codec/.results/latest.tsv}" || base=$?
sha=0
python3 -I tests/sha256/suite.py || sha=$?
((base == 0 && sha == 0))
