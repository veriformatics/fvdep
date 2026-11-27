#!/usr/bin/env bash
# U7 E (contract docs/contracts/U7-judge.md E1, D1): the launch examples PROVEN end to end — U6's
# profile, U5's phases + J (S, G, A, the three kernels) on each of the 10 cases (6 fn, 4 abi), no
# override. Each case = `fvdep-dev phase check … --profile --judge`; PASS = exit 0 + its PROVEN line.
# FVDEP_JUDGE_JOBS cases at once (default 3), one shared FVDEP_CACHE (the library fills once, K3).
# `--case <name>` runs one. Its steps run fvdep-step ⇒ a PID namespace of the job's own (pidns-check).
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2
bash tools/pidns-check.sh || exit 2
dev=tool/.lake/build/bin/fvdep-dev
only=""
[ "${1:-}" = "--case" ] && only="${2:-}"
cache=$(mktemp -d); logs=$(mktemp -d)
# FVDEP_JUDGE_KEEP=<dir>: each case's D1/D2 output kept there (Q1's measurements read them).
trap '[ -n "${FVDEP_JUDGE_KEEP:-}" ] && mkdir -p "$FVDEP_JUDGE_KEEP" && cp "$logs"/[ER]* "$FVDEP_JUDGE_KEEP"/ 2>/dev/null; rm -rf "$cache" "$logs"' EXIT
# name|id|manifest|spec module|spec constant|abi module|abi constant|impl
CASES='fn.encode|base64.encode|fvdep.toml|Fvdep.Base64.Encode.V1_0_0|Fvdep.Base64.Encode.V1_0_0.encode|||Launch.Base64.encode
fn.decode|base64.decode|fvdep.toml|Fvdep.Base64.Decode.V1_0_0|Fvdep.Base64.Decode.V1_0_0.decode|||Launch.Base64.decode
fn.encode_url|base64.encode_url|fvdep.toml|Fvdep.Base64.EncodeUrl.V1_0_0|Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl|||Launch.Base64.encodeUrl
fn.decode_url|base64.decode_url|fvdep.toml|Fvdep.Base64.DecodeUrl.V1_0_0|Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl|||Launch.Base64.decodeUrl
fn.parse|semver.parse|fvdep.toml|Fvdep.Semver.Parse.V1_0_0|Fvdep.Semver.Parse.V1_0_0.parse|||Launch.Semver.parse
fn.compare|semver.compare|fvdep.toml|Fvdep.Semver.Compare.V1_0_0|Fvdep.Semver.Compare.V1_0_0.compare|||Launch.Semver.compare
abi.encode|base64.encode|fvdep-abi.toml|Fvdep.Base64.Encode.V1_0_0|Fvdep.Base64.Encode.V1_0_0.encode|Fvdep.Abi.V1_0_0|Fvdep.Abi.V1_0_0.encoder|Launch.Base64Abi.encode
abi.decode|base64.decode|fvdep-abi.toml|Fvdep.Base64.Decode.V1_0_0|Fvdep.Base64.Decode.V1_0_0.decode|Fvdep.Abi.V1_0_0|Fvdep.Abi.V1_0_0.decoder|Launch.Base64Abi.decode
abi.encode_url|base64.encode_url|fvdep-abi.toml|Fvdep.Base64.EncodeUrl.V1_0_0|Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl|Fvdep.Abi.V1_0_0|Fvdep.Abi.V1_0_0.encoder|Launch.Base64Abi.encodeUrl
abi.decode_url|base64.decode_url|fvdep-abi.toml|Fvdep.Base64.DecodeUrl.V1_0_0|Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl|Fvdep.Abi.V1_0_0|Fvdep.Abi.V1_0_0.decoder|Launch.Base64Abi.decodeUrl'
# R (contract U7 R): source-level regressions through D1 (a fresh project each: the launch base64
# implementation + one proof module from tests/judge/r) — name|proof module|launch proofs too|the
# verdict line's start|the kernels' lines (`none` = K never ran).
RCASES='R.forged|R.Forged|no|NOT PROVEN base64.encode@1.0.0: kernel lean rejected the proof|kernel lean reject;kernel con-leche reject;kernel nanoda crash;^  detail: Lean default kernel rejects the solution: ;^  detail: con-leche: invalid:;^  detail: thread 
R.sorry|R.Sorry|no|NOT PROVEN base64.encode@1.0.0: the proof depends on axiom «sorryAx»|none;  detail: «sorryAx»
R.native|R.Native|yes|NOT PROVEN base64.encode@1.0.0: the proof depends on axiom «|none
R.extra|R.Extra|no|NOT PROVEN base64.encode@1.0.0: the proof depends on axiom «R.Extra.cheat»|none
R.pointwise|R.Pointwise|yes|NOT PROVEN base64.encode@1.0.0: the proof does not prove the required statement|none
R.self|R.Self|no|NOT PROVEN base64.encode@1.0.0: the proof does not prove the required statement|none'
# R through D2 (`fvdep-dev judge run`, always SIMULATION): byte edits of E.fn.encode's honest exports
# (tests/judge/edit.py) — name|edit|extra options|the verdict line|a detail line (or `-`).
SIM="(overrides: given e1 + e2"
DCASES="R.d2.honest|none||SIMULATION PROVEN judge Launch.Base64.encode $SIM)|-
R.d2.header|header||SIMULATION NOT PROVEN judge: the proof does not prove the required statement $SIM)|  detail: the solution lacks Launch.Proof.Base64.encode_eq
R.d2.spec|swap-value Fvdep.Base64.Encode.V1_0_0.encode Launch.Base64.encode||SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution redefines Fvdep.Base64.Encode.V1_0_0.encode
R.d2.propext|drop propext||SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution lacks propext
R.d2.collision|collide Launch.Proof.Base64.encode_eq Fvdep.Base64.Encode.V1_0_0.encode|--proof-as Fvdep.Base64.Encode.V1_0_0.encode|SIMULATION NOT PROVEN judge: the proof does not prove the required statement $SIM)|  detail: the proof's name Fvdep.Base64.Encode.V1_0_0.encode is a trusted constant
R.d2.propext-type|refield propext type||SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution redefines propext
R.d2.prelude|refield Nat.add value||SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution redefines Nat.add
R.d2.budget-s|none|--limit judge.work=5|SIMULATION NOT PROVEN judge: the proof does not prove the required statement $SIM, --limit judge.work)|  detail: the comparison passes its work budget
R.d2.budget-g|none|--limit judge.work=1000|SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM, --limit judge.work)|  detail: the comparison passes its work budget"
one() {
    local name=$1 id=$2 mf=$3 sm=$4 sc=$5 am=$6 ac=$7 impl=$8 abi=() s rc
    [ -n "$am" ] && abi=(--abi-module "$am" --abi "$ac")
    s=$(date +%s)
    local keep=()
    [ "$name" = fn.encode ] && keep=(--artifacts "$logs/art")
    FVDEP_CACHE=$cache "$dev" phase check examples/launch "$id" --library . --spec-module "$sm" \
        --spec "$sc" "${abi[@]}" --manifest "examples/launch/$mf" --profile --judge "${keep[@]}" \
        >"$logs/E.$name" 2>&1
    rc=$?
    if [ "$rc" = 0 ] && command grep -qxF "PROVEN $id@1.0.0 $impl" "$logs/E.$name"; then
        echo "PASS E.$name $(( $(date +%s) - s ))s"
    else
        echo "FAIL E.$name rc=$rc"
        command grep -vE '^(artifact|module|import|grammar) ' "$logs/E.$name" | tail -12 >"$logs/why.$name"
    fi
}
export -f one; export dev cache logs
selected=$(printf '%s\n' "$CASES" | while IFS='|' read -r name rest; do
    # a D2 case edits E.fn.encode's exports: it runs that case too
    [ -z "$only" ] || [ "$only" = "E.$name" ] || { [[ "$only" == R.d2.* ]] && [ "$name" = fn.encode ]; } ||
        continue
    printf '%s|%s\n' "$name" "$rest"
done)
rnames=" $(printf '%s\n' "$RCASES" "$DCASES" | cut -d'|' -f1 | tr '\n' ' ')"
[ -n "$selected" ] || [[ "$rnames" == *" $only "* ]] || { echo "judge-suite: no case ${only:-}"; exit 2; }
touch "$logs/out"
if [ -n "$selected" ]; then
    # shellcheck disable=SC2016 # the fields expand in the child bash that xargs starts
    printf '%s\n' "$selected" | xargs -P "${FVDEP_JUDGE_JOBS:-3}" -I{} bash -c \
        'IFS="|" read -r a b c d e f g h <<<"{}"; one "$a" "$b" "$c" "$d" "$e" "$f" "$g" "$h"' \
        >"$logs/out"
fi

# The log's lines: line 1 of the verdict block starts with $want; each of $kern's lines present (or
# no `kernel ` line at all for `none`).
verdict_ok() {
    local log=$1 want=$2 kern=$3 line found=0 k
    while IFS= read -r line; do [[ "$line" == "$want"* ]] && found=1; done <"$log"
    [ "$found" = 1 ] || return 1
    if [ "${kern%%;*}" = none ]; then
        command grep -q '^kernel ' "$log" && return 1
        [ "$kern" = none ] || command grep -qxF "${kern#none;}" "$log"
    else
        IFS=';' read -ra ks <<<"$kern"
        for k in "${ks[@]}"; do
            if [[ "$k" == ^* ]]; then  # `^<text>` = some line starting with <text> (J4's own lines)
                found=0
                while IFS= read -r line; do [[ "$line" == "${k#^}"* ]] && found=1; done <"$log"
                [ "$found" = 1 ] || return 1
            else
                command grep -qxF "$k" "$log" || return 1
            fi
        done
    fi
}
rsrc() {
    local name=$1 mod=$2 launch=$3 want=$4 kern=$5 tmp s rc proofs
    tmp=$(mktemp -d); s=$(date +%s)
    mkdir -p "$tmp/Launch/Proof" "$tmp/R"
    cp examples/launch/Launch/Base64.lean "$tmp/Launch/"
    cp "tests/judge/r/${mod#R.}.lean" "$tmp/R/"
    proofs="\"$mod\""
    if [ "$launch" = yes ]; then
        cp examples/launch/Launch/Proof/Base64.lean "$tmp/Launch/Proof/"
        proofs="\"$mod\", \"Launch.Proof.Base64\""
    fi
    printf 'schema = 1\n\n[library]\ncommit = "%s"\n\n[modules."base64.encode"]\nversion = "1.0.0"\nshape = "fn"\nimpl_modules = ["Launch.Base64"]\nproof_modules = [%s]\nimpl = "Launch.Base64.encode"\nproof = "%s.encode_eq"\n' \
        0000000000000000000000000000000000000000 "$proofs" "$mod" >"$tmp/fvdep.toml"
    FVDEP_CACHE=$cache "$dev" phase check "$tmp" base64.encode --library . \
        --spec-module Fvdep.Base64.Encode.V1_0_0 --spec Fvdep.Base64.Encode.V1_0_0.encode \
        --profile --judge >"$logs/$name" 2>&1
    rc=$?
    rm -rf "$tmp"
    if [ "$rc" = 1 ] && verdict_ok "$logs/$name" "$want" "$kern"; then
        echo "PASS $name $(( $(date +%s) - s ))s"
    else
        echo "FAIL $name rc=$rc"
        command grep -vE '^(artifact|module|import|grammar) ' "$logs/$name" | tail -12 >"$logs/why.$name"
    fi
}
export -f rsrc verdict_ok
rsel=$(printf '%s\n' "$RCASES" | while IFS='|' read -r name rest; do
    [ -z "$only" ] || [ "$only" = "$name" ] || continue
    printf '%s|%s\n' "$name" "$rest"
done)
if [ -n "$rsel" ]; then
    # shellcheck disable=SC2016 # the fields expand in the child bash that xargs starts
    printf '%s\n' "$rsel" | xargs -P "${FVDEP_JUDGE_JOBS:-3}" -I{} bash -c \
        'IFS="|" read -r a b c d e <<<"{}"; rsrc "$a" "$b" "$c" "$d" "$e"' >>"$logs/out"
fi

# R through D2: the DCASES table (top).
e1="$logs/art/exports/e1.ndjson"; e2="$logs/art/exports/e2.ndjson"
while IFS='|' read -r name edit extra want detail; do
    [ -z "$only" ] || [ "$only" = "$name" ] || continue
    if [ ! -f "$e1" ] || [ ! -f "$e2" ]; then echo "FAIL $name rc=- (no honest exports: E.fn.encode)" >>"$logs/out"; continue; fi
    s=$(date +%s); f="$e2"; proof=Launch.Proof.Base64.encode_eq; opts=()
    if [ "$edit" != none ]; then
        f="$logs/e2.$name"
        read -ra ed <<<"$edit"
        if ! python3 -I tests/judge/edit.py "${ed[0]}" "$e2" "$f" "${ed[@]:1}" 2>"$logs/why.$name"; then
            echo "FAIL $name (edit)" >>"$logs/out"
            continue
        fi
    fi
    case "$extra" in
        --proof-as\ *) proof=${extra#--proof-as }; opts=() ;;
        "") opts=() ;;
        *) read -ra opts <<<"$extra" ;;
    esac
    FVDEP_CACHE=$cache "$dev" judge run "$e1" "$f" --spec Fvdep.Base64.Encode.V1_0_0.encode \
        --impl Launch.Base64.encode --proof "$proof" "${opts[@]}" >"$logs/$name" 2>&1
    rc=$?
    ok=1
    command grep -qxF "$want" "$logs/$name" || ok=0
    [ "$detail" = - ] || command grep -qxF "$detail" "$logs/$name" || ok=0
    # a stage that stopped ran no kernel (the honest pair alone reaches K)
    [ "$name" = R.d2.honest ] || ! command grep -q '^kernel ' "$logs/$name" || ok=0
    if [ "$ok" = 1 ]; then echo "PASS $name $(( $(date +%s) - s ))s" >>"$logs/out"
    else echo "FAIL $name rc=$rc" >>"$logs/out"; tail -12 "$logs/$name" >"$logs/why.$name"; fi
done <<<"$DCASES"
sort "$logs/out"
for f in "$logs"/why.*; do
    [ -e "$f" ] || continue
    echo "--- ${f##*/why.}"; sed 's/^/    /' "$f"
done
pass=$(command grep -c '^PASS ' "$logs/out"); fail=$(command grep -c '^FAIL ' "$logs/out")
echo "judge-suite: $pass passed, $fail failed"
[ "$fail" = 0 ] && [ "$pass" -gt 0 ]
