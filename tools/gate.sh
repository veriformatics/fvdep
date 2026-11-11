#!/usr/bin/env bash
# Gate = the one full check chain (.claude/rules/gate.md). Each step runs to completion in a
# subshell (one run reports every red), prints `<step> rc=N <s>s` + appends a ledger row; the run
# closes on `gate rc=N <s>s`. Any nonzero step rc = red: a missing tool or unreadable input never
# reads green.
# Ledger = .gate/ledger.tsv (gitignored), one row per step per run: date (run start, UTC), tree
# (graded file set = tracked + untracked-unignored, so uncommitted edits count), step, seconds,
# verdict (green | red), class (`-` | red: `unclassified` until set to product|gate|flake|planted).
# An unwritable ledger fails the run as step `ledger`.
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root" || exit 1

ledger="$root/.gate/ledger.tsv"
run_date="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
failed=()

stamp() { printf '%s' "${EPOCHREALTIME//[!0-9]/}"; }
elapsed() {
    local us=$(($(stamp) - $1))
    printf '%d.%d' $((us / 1000000)) $((us / 100000 % 10))
}

gated_tree() {
    local tmp tree
    tmp="$(mktemp -d)" || { printf unknown; return 0; }
    cp -- "$(git rev-parse --git-path index 2>/dev/null)" "$tmp/index" 2>/dev/null
    tree="$(GIT_INDEX_FILE="$tmp/index" git add -A 2>/dev/null &&
        GIT_INDEX_FILE="$tmp/index" git write-tree 2>/dev/null)"
    rm -rf -- "$tmp"
    printf '%s' "${tree:-unknown}"
}
tree="$(gated_tree)"

ledger_row() { # STEP RC SECONDS
    local verdict=green class=- header=""
    if [[ $2 -ne 0 ]]; then
        verdict=red
        class=unclassified
    fi
    [[ -s "$ledger" ]] || header=$'date\ttree\tstep\tseconds\tverdict\tclass\n'
    mkdir -p -- "${ledger%/*}" 2>/dev/null &&
        printf '%s%s\t%s\t%s\t%s\t%s\t%s\n' "$header" "$run_date" "$tree" "$1" "$3" "$verdict" \
            "$class" 2>/dev/null >>"$ledger" && return 0
    printf 'ledger: cannot append to %s\n' "$ledger" >&2
    [[ " ${failed[*]} " == *" ledger "* ]] || failed+=(ledger)
}

step() { # NAME CMD...
    local name="$1" start rc secs
    shift
    start="$(stamp)"
    printf '=== %s ===\n' "$name"
    ("$@")
    rc=$?
    secs="$(elapsed "$start")"
    printf '%s rc=%d %ss\n' "$name" "$rc" "$secs"
    [[ $rc -eq 0 ]] || failed+=("$name")
    ledger_row "$name" "$rc" "$secs"
}

run_start="$(stamp)"
step spec-lint .agent/spec-lint .agent/spec.md

rc=0
if [[ ${#failed[@]} -gt 0 ]]; then
    rc=1
    printf 'red: %s\n' "${failed[*]}"
fi
printf 'gate rc=%d %ss\n' "$rc" "$(elapsed "$run_start")"
exit "$rc"
