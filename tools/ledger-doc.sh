#!/usr/bin/env bash
# Regenerate docs/verification.md (contract U2 L7) from the ledger rows: the checker runs on vflab
# (no fvdep build on the desktop), its document comes back on stdout into a temp file, then lands
# in the tree. Findings → stderr (`ledger: <component>: <code>: <detail>`), the doc untouched, rc 1.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
out="$(mktemp)"
err="$(mktemp)"
trap 'rm -f "$out" "$err"' EXIT
# shellcheck disable=SC2016 # expanded on vflab
if ! "$root/tools/vflab-run" bash -c 'cd tool && lake build -q FvdepLedger «fvdep-ledger» >&2 || exit 1
    t="$(mktemp)"; trap "rm -f $t" EXIT
    lake exe fvdep-ledger --write "$t" >&2 && cat "$t"' >"$out" 2>"$err"; then
    cat "$err" >&2
    exit 1
fi
cp "$out" "$root/docs/verification.md"
printf 'ledger-doc: docs/verification.md (%s lines)\n' "$(wc -l <"$out")"
