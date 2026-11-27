#!/usr/bin/env bash
# U7 C1 (contract docs/contracts/U7-judge.md C1, stage `verification-canaries`): each raw control
# (MANIFEST.tsv: path, SHA-256, the expected vector pinned before measuring) through the three pinned
# kernels alone (K1 + K2 + K4: `fvdep-dev judge kernels`) — PASS = its bytes = the pin + exactly one
# line per kernel in K1's order (lean, con-leche, nanoda), each with its expected status class (a
# crash, timeout or decline never stands in for a reject) + the seam's exit status (0 all accept, 1
# a completed vector with a non-acceptance; infrastructure is never a measured vector). `--case
# <path>` runs one. Its steps run fvdep-step ⇒ a PID namespace of the job's own.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2
bash tools/pidns-check.sh || exit 2
dev=tool/.lake/build/bin/fvdep-dev
only=""
[ "${1:-}" = "--case" ] && only="${2:-}"
cache=$(mktemp -d); trap 'rm -rf "$cache"' EXIT
pass=0; fail=0
while IFS=$'\t' read -r path sum want; do
    [[ -z "$path" || "$path" == \#* ]] && continue
    [ -z "$only" ] || [ "$only" = "$path" ] || continue
    f=tests/canaries/$path
    got_sum=$(sha256sum "$f" | cut -c1-64)
    if [ "$got_sum" != "$sum" ]; then
        echo "FAIL $path: SHA-256 $got_sum, pinned $sum"; fail=$((fail + 1)); continue
    fi
    out=$(FVDEP_CACHE=$cache "$dev" judge kernels "$f" 2>&1)
    rc=$?
    got=$(printf '%s\n' "$out" | sed -n 's/^kernel \([a-z-]*\) \([a-z]*\).*/\1 \2/p' | paste -sd';' -)
    read -r a b c <<<"$want"
    exp="lean $a;con-leche $b;nanoda $c"
    code=1; [ "$want" = "accept accept accept" ] && code=0
    if [ "$got" = "$exp" ] && [ "$rc" = "$code" ]; then
        echo "PASS $path ($got)"; pass=$((pass + 1))
    else
        echo "FAIL $path: kernels ($got) exit $rc, expected ($exp) exit $code"
        printf '%s\n' "$out" | tail -5 | sed 's/^/    /'
        fail=$((fail + 1))
    fi
done <tests/canaries/MANIFEST.tsv
echo "verification-canaries: $pass passed, $fail failed"
[ "$fail" = 0 ] && [ "$pass" -gt 0 ]
