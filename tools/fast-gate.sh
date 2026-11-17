#!/usr/bin/env bash
# Iteration gate: FAST_STAGES from tools/gate.sh — the independent checks in parallel, then the
# incremental Lean build + the stages that consume it. Never the claim: the stages it skips (the
# registry minus FAST_STAGES) run in tools/gate.sh alone and are printed. Each stage's row lands in
# the step ledger (kind `fast`). rc 0 iff every selected stage returned 0 + the ledger took every
# row. Run on vflab: tools/vflab-run bash tools/fast-gate.sh
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root" || exit 1
# shellcheck source=tools/gate.sh
source tools/gate.sh
registry_ok || exit 2
start="$(stamp)"
ledger_begin fast

# Checks that build + run no fvdep code run in parallel; every other selected stage runs after
# them, one at a time in FAST_STAGES order, `lean-build` first: a stage running its own
# `lake build` beside `lean-build` races its relink (its driver then finds no binary) ⇒ a stage
# runs in parallel only when listed here.
independent=" imports preview spec shell python fanout vendor deps renovate meta "
# A suite's green verdict stands while its inputs are unchanged (gate.sh `suite`).
export FVDEP_REUSE=1
parallel=()
sequential=()
for name in $FAST_STAGES; do
    if [[ "$independent" == *" $name "* ]]; then parallel+=("$name"); else sequential+=("$name"); fi
done
[[ "${sequential[0]:-}" == lean-build ]] || {
    printf 'fast-gate: lean-build must lead the sequential stages (FAST_STAGES order)\n' >&2
    exit 2
}

log="$(mktemp -d)"
trap 'rm -rf "$log"' EXIT
pids=()
for name in "${parallel[@]}"; do
    (
        t0="$(stamp)"
        ("${name//-/_}") >"$log/$name" 2>&1
        rc=$?
        elapsed "$t0" >"$log/$name.time"
        exit $rc
    ) &
    pids+=($!)
done

for name in "${sequential[@]}"; do
    stage "$name" "${name//-/_}"
done

for i in "${!parallel[@]}"; do
    wait "${pids[$i]}"
    rc=$?
    secs="$(cat "$log/${parallel[$i]}.time")"
    printf '\n=== %s ===\n' "${parallel[$i]}"
    cat "$log/${parallel[$i]}"
    printf '%s rc=%d %ss\n' "${parallel[$i]}" "$rc" "$secs"
    ledger_row "${parallel[$i]}" "$rc" "$secs"
    [[ $rc -eq 0 ]] || failed+=("${parallel[$i]}")
done
[[ $ledger_ok -eq 1 ]] || failed+=(ledger)

skipped="$(awk -v fast=" $FAST_STAGES " 'NF && index(fast, " " $1 " ") == 0 { s = s (s == "" ? "" : " ") $1 } END { printf "%s", s }' <<<"$STAGES")"
printf '\n=== fast gate ===\nselected: %s\nskipped (tools/gate.sh alone): %s\n' "$FAST_STAGES" "$skipped"
if [[ ${#failed[@]} -ne 0 ]]; then
    printf 'FAILED: %s\nfast-gate rc=1 %ss\n' "${failed[*]}" "$(elapsed "$start")"
    exit 1
fi
printf 'fast-gate rc=0 %ss\n' "$(elapsed "$start")"
