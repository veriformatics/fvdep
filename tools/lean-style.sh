#!/usr/bin/env bash
# Lean layout (gate stage `lean-style`): tracked Lean sources outside prototype/ keep no tab, no
# trailing whitespace, lines ≤ 100 characters + a final newline; then the pinned lean-fmt
# (tools/lean-fmt: a Lake package pinned by commit) reports no format drift (`format --check`) +
# no lint finding (`check`) in both packages. lean-fmt elaborates each file, so the packages must
# be built first (stage `lean-build`); a file that does not compile is red. Prints `file:line: rule`
# per layout finding.
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root" || exit 1

mapfile -t files < <(git ls-files -co --exclude-standard -- '*.lean' ':!prototype/')
if [[ ${#files[@]} -eq 0 ]]; then
    printf 'lean-style: no Lean source found\n' >&2
    exit 1
fi
rc=0
for f in "${files[@]}"; do
    # Generated ledger fixtures (tests/ledger/generate.py + regenerate.sh): their layout = the
    # generator's + lean-fmt's (a 160-deep statement stairs past 100 columns); lean-fmt still checks.
    [[ "$f" == tool/FvdepLedgerFixtures/* ]] && continue
    LC_ALL=C.UTF-8 awk -v f="$f" '
        /\t/ { printf "%s:%d: tab\n", f, FNR; bad = 1 }
        /[ \t]$/ { printf "%s:%d: trailing whitespace\n", f, FNR; bad = 1 }
        length($0) > 100 { printf "%s:%d: line longer than 100 characters\n", f, FNR; bad = 1 }
        END { exit bad }
    ' "$f" || rc=1
    if [[ -s "$f" && "$(tail -c 1 "$f" | od -An -c | tr -d ' ')" != '\n' ]]; then
        printf '%s: no final newline\n' "$f"
        rc=1
    fi
done

# FVDEP_LEAN_FMT = an already built lean-fmt (tools/gate-probe.sh: its scratch copies share the
# gate tree's build instead of copying a 339 MB package cache per probe).
fmt="${FVDEP_LEAN_FMT:-}"
if [[ -z "$fmt" ]]; then
    if ! out="$(cd tools/lean-fmt && lake build «lean-fmt» 2>&1)"; then
        printf '%s\nlean-style: lean-fmt does not build (tools/lean-fmt)\n' "$out" >&2
        exit 1
    fi
    fmt="$root/tools/lean-fmt/.lake/packages/lean-fmt/.lake/build/bin/lean-fmt"
fi
for pkg in . tool; do
    (cd "$pkg" && "$fmt" format --check && "$fmt" check) || rc=1
done
exit $rc
