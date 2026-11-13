#!/usr/bin/env bash
# Contract U2 L1–L9. Each invocation loads one independent fixture, never the checker source.
# Run at the repo root on vflab: tools/vflab-run bash tests/ledger/run.sh
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
seed="${FVDEP_TEST_SEED:-24681357}"
printf 'SEED %s\n' "$seed"

(cd "$root/tool" && lake build FvdepLedgerFixtures «fvdep-ledger») >"$tmp/build.out" 2>"$tmp/build.err"
rc=$?
if [[ $rc -ne 0 ]]; then
    printf 'FAIL BUILD fixture/checker build (rc %s)\n' "$rc"
    cat "$tmp/build.out" "$tmp/build.err"
    exit 1
fi
printf 'PASS BUILD fixture/checker build\n'
# Cases run in parallel (each its own temp dir); the checker binary runs with Lake's LEAN_PATH, captured
# once (`lake exe` per call = Lake startup + its build lock on every call).
jobs="${FVDEP_LEDGER_JOBS:-$(nproc)}"
lean_path="$(cd "$root/tool" && lake env printenv LEAN_PATH)"
bin="$root/tool/.lake/build/bin/fvdep-ledger"


# call PHASE ARGS…; rc captured immediately, streams retained until the next call.
call() {
    local phase="$1"
    shift
    printf 'CMD %s/%s (cd tool && fvdep-ledger' "$id" "$phase"
    printf ' %q' "$@"
    printf ')\n'
    (cd "$root/tool" && LEAN_PATH="$lean_path" "$bin" "$@") >"$ct/out" 2>"$ct/err"
    actual=$?
    printf 'OBS %s/%s rc=%s\n' "$id" "$phase" "$actual"
    if [[ -f "$doc" ]]; then
        printf 'DOC %s/%s bytes=%s\n' "$id" "$phase" "$(wc -c <"$doc")"
    else
        printf 'DOC %s/%s absent\n' "$id" "$phase"
    fi
    if [[ -s "$ct/out" ]]; then sed 's/^/stdout: /' "$ct/out"; fi
    if [[ -s "$ct/err" ]]; then sed 's/^/stderr: /' "$ct/err"; fi
}

# Finding = expected status + named L8 code; refusal preserves the exact input bytes.
judge() {
    [[ $actual -eq $want ]] || return 1
    if [[ "$code" != - ]]; then
        grep -Eq -- "^ledger: [^:]+: $code: .+" "$ct/err" || return 1
        # Every finding stays on one line and uses an L8 code (kernel errors are quoted details).
        awk '!/^ledger: [^:]+: (uncovered|module|subject|theorem|statement|axiom|about|waiver|residue|ruling|root|path|edge|nocaller|compiled|replay|doc): .+$/ {bad=1} END {exit bad}' \
            "$ct/err" || return 1
    fi
    if [[ $want -ne 0 ]]; then
        cmp -s "$doc" "$ct/before" || return 1
    fi
}

# Rendering + creation have separate controls. Seeded bytes keep drift checks independent of
# whether --write is implemented; a conforming writer replaces them with its canonical document.
write_clean() {
    call write --write "$doc" "${options[@]}"
    [[ $actual -eq 0 && -s "$doc" ]] || return 1
}

mutate() {
    python3 -I "$root/tests/ledger/mutate.py" "$doc" "$seed" "$1"
}

n=0
while IFS=$'\t' read -r id label fixture want code spec action; do
    [[ -n "$id" && "$id" != \#* ]] || continue
    # FVDEP_LEDGER_ONLY=<id> runs one case (the gate probe's planted case).
    [[ -z "${FVDEP_LEDGER_ONLY:-}" || "$id" == "$FVDEP_LEDGER_ONLY" ]] || continue
    n=$((n + 1))
    if ((n > jobs)); then wait -n; fi
    (
    ct="$tmp/case.$id"
    mkdir -p "$ct"
    doc="$ct/$id.md"
    printf 'sentinel for %s\n' "$id" >"$doc"
    cp "$doc" "$ct/before"
    module="FvdepLedgerFixtures.$fixture"
    options=(--module "$module" --ledger "$module.ledger" --spec "$root/tests/ledger/fixtures/$spec.spec")
    ok=0
    actual=-1
    case "$action" in
    negative)
        call write --write "$doc" "${options[@]}"
        judge && ok=1
        ;;
    writecheck)
        if write_clean; then
            cp "$doc" "$ct/canonical"
            call check --check "$doc" "${options[@]}"
            [[ $actual -eq 0 ]] && cmp -s "$doc" "$ct/canonical" && ok=1
        fi
        ;;
    drift)
        if write_clean && mutate 0; then
            cp "$doc" "$ct/before"
            call check --check "$doc" "${options[@]}"
            judge && ok=1
        fi
        ;;
    property-drift)
        if write_clean; then
            cp "$doc" "$ct/canonical"
            ok=1
            # L7: every unequal byte sequence must fail --check without repairing the document.
            # Deterministic generated offsets + replacements, with committed seed printed above.
            for sample in 0 1 2 3 4 5 6 7; do
                cp "$ct/canonical" "$doc"
                if ! mutate "$sample"; then ok=0; break; fi
                cp "$doc" "$ct/before"
                call "check-$sample" --check "$doc" "${options[@]}"
                judge || ok=0
            done
        fi
        ;;
    first-line)
        if write_clean; then
            { printf '!'; cat "$doc"; printf '\nsecond drift\n'; } >"$ct/changed"
            mv "$ct/changed" "$doc"
            cp "$doc" "$ct/before"
            call check --check "$doc" "${options[@]}"
            if judge && sed -n 's/^ledger: [^:]*: doc: //p' "$ct/err" |
                grep -Eq '(^|[^[:digit:]])1([^[:digit:]]|$)'; then
                ok=1
            fi
        fi
        ;;
    idempotent)
        if write_clean; then
            cp "$doc" "$ct/canonical"
            call rewrite --write "$doc" "${options[@]}"
            [[ $actual -eq 0 ]] && cmp -s "$doc" "$ct/canonical" && ok=1
        fi
        ;;
    create)
        rm "$doc"
        call write --write "$doc" "${options[@]}"
        [[ $actual -eq 0 && -s "$doc" ]] && grep -Fq -- "$module.main" "$doc" && ok=1
        ;;
    no-create)
        rm "$doc"
        call write --write "$doc" "${options[@]}"
        [[ $actual -eq $want && ! -e "$doc" ]] &&
            grep -Eq -- "^ledger: [^:]+: $code: .+" "$ct/err" && ok=1
        ;;
    hash)
        if write_clean; then
            (cd "$root/tool" && lake env lean FvdepLedgerFixtures/DocHashOracle.lean) \
                >"$ct/oracle" 2>"$ct/oracle.err"
            oracle_rc=$?
            printf 'ORACLE %s rc=%s\n' "$id" "$oracle_rc"
            cat "$ct/oracle" "$ct/oracle.err"
            if [[ $oracle_rc -eq 0 ]] &&
                python3 -I "$root/tests/ledger/hash.py" "$ct/oracle" "$doc"; then
                ok=1
            fi
        fi
        ;;
    deep)
        if write_clean && grep -Fq 'deepTail' "$doc" &&
            [[ $(grep -o 'True' "$doc" | wc -l) -ge 160 ]]; then
            ok=1
        fi
        ;;
    render)
        if write_clean; then
            ok=1
            # L7 fixes contents, not Markdown syntax. These fields must survive any layout.
            for text in "$module.main" "$module.interpret" "$module.plan" 'List String' \
                "$module.proof" 'docs/contracts/U2-core.md L1–L9' \
                'The named statement holds for the executed subject.' \
                'Fixture interpreter and optional primitive boundary.' \
                'The effect-to-primitive mapping is tested residue.'; do
                grep -Fq -- "$text" "$doc" || ok=0
            done
        fi
        ;;
    usage-unknown)
        call usage --write "$doc" "${options[@]}" --unknown-ledger-option
        judge && ok=1
        ;;
    usage-module)
        call usage --write "$doc" --module FvdepLedgerFixtures.NoSuchModule \
            --ledger "$module.ledger" --spec "$root/tests/ledger/fixtures/$spec.spec"
        judge && ok=1
        ;;
    usage-nonliteral)
        call usage --write "$doc" --module "$module" --ledger "$module.hiddenLedger" \
            --spec "$root/tests/ledger/fixtures/$spec.spec"
        judge && ok=1
        ;;
    usage-ledger)
        call usage --write "$doc" --module "$module" --ledger "$module.noSuchLedger" \
            --spec "$root/tests/ledger/fixtures/$spec.spec"
        judge && ok=1
        ;;
    usage-argument)
        call usage --write
        judge && ok=1
        ;;
    usage-mode)
        call usage "$doc" "${options[@]}"
        judge && ok=1
        ;;
    *) printf 'Unsupported fixture action: %s\n' "$action" >&2 ;;
    esac
    if [[ $ok -eq 1 ]]; then
        printf 'PASS %s %s\n' "$id" "$label"
    else
        printf 'FAIL %s %s (last rc %s; want %s, code %s)\n' \
            "$id" "$label" "${actual:-not-run}" "$want" "$code"
    fi
    ) </dev/null >"$tmp/log.$(printf '%03d' "$n")" 2>&1 &
done <"$root/tests/ledger/cases.tsv"
wait
cat "$tmp"/log.*
passes="$(cat "$tmp"/log.* | grep -c '^PASS ')"
fails="$(cat "$tmp"/log.* | grep -c '^FAIL ')"
printf 'TOTAL %s PASS %s FAIL %s\n' "$((passes + fails))" "$passes" "$fails"
[[ $((passes + fails)) -eq $n ]] || { printf 'FAIL driver: %s cases ran, %s judged\n' "$n" "$((passes + fails))"; exit 1; }
exit "$fails"
