#!/usr/bin/env bash
# Regenerates index.json (contract U4 C1: `fvdep index` at the repo root) on vflab + writes its bytes
# into this worktree: a file made in the vflab workspace alone dies at the next tools/vflab-run sync.
# Gate stage `index` checks the result. Run from the desktop: bash tools/update-index.sh
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp)"
trap 'rm -f -- "$tmp"' EXIT
"$root/tools/vflab-run" bash -c '(cd tool && lake build «fvdep-cli» >&2) &&
    tool/.lake/build/bin/fvdep index >&2 && cat index.json' >"$tmp"
cat -- "$tmp" >"$root/index.json"
