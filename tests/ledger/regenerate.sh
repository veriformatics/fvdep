#!/usr/bin/env bash
# Idempotent fixture repair: contract-only templates → pinned Lean layout. Run through vflab-run.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
python3 -I tests/ledger/generate.py
(cd tools/lean-fmt && lake build «lean-fmt»)
formatter="$root/tools/lean-fmt/.lake/packages/lean-fmt/.lake/build/bin/lean-fmt"
cd tool
shopt -s globstar nullglob
files=(FvdepLedgerFixtures/**/*.lean)
modules=()
for file in "${files[@]}"; do
    name="${file%.lean}"
    modules+=("${name//\//.}")
done
# Build each module explicitly: the optional fixture library root imports none of these cases.
lake build "${modules[@]}"
"$formatter" format "${files[@]}"
