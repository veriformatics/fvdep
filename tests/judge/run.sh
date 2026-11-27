#!/usr/bin/env bash
# U7 E (contract docs/contracts/U7-judge.md E1, D1): the launch examples PROVEN end to end — U6's
# profile, U5's phases + J (S, G, A, the three kernels) on each of the 10 cases (6 fn, 4 abi), no
# override. Each case = `fvdep-dev phase check … --profile --judge`; PASS = exit 0 + its PROVEN line.
# + R's regressions (D1 source-level, D1's own refusals + stops, D2 byte edits: tables below).
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
R.native|R.Native|yes|NOT PROVEN base64.encode@1.0.0: the proof depends on axiom «R.Native.encode_eq._native.native_decide.ax_1_1»|none;  detail: «R.Native.encode_eq._native.native_decide.ax_1_1»
R.extra|R.Extra|no|NOT PROVEN base64.encode@1.0.0: the proof depends on axiom «R.Extra.cheat»|none
R.pointwise|R.Pointwise|yes|NOT PROVEN base64.encode@1.0.0: the proof does not prove the required statement|none;  detail: the proof'\''s type is not an equation
R.self|R.Self|no|NOT PROVEN base64.encode@1.0.0: the proof does not prove the required statement|none;  detail: the proof does not prove the required statement'
# R through D2 (`fvdep-dev judge run`, always SIMULATION): byte edits of E.fn.encode's honest exports
# (tests/judge/edit.py), a missing or oversized e2 (`missing`, `sparse <bytes>`) — name|edit|extra
# options|exit|the verdict line (`~<ERE>` = a line matching it)|a detail line (or `-`).
SIM="(overrides: given e1 + e2"
long=$(head -c 1100 /dev/zero | tr '\0' L); lcause="the solution lacks $long"
DCASES="R.d2.honest|none||0|SIMULATION PROVEN judge Launch.Base64.encode $SIM)|-
R.d2.header|header||1|SIMULATION NOT PROVEN judge: the proof does not prove the required statement $SIM)|  detail: the solution lacks Launch.Proof.Base64.encode_eq
R.d2.spec|swap-value Fvdep.Base64.Encode.V1_0_0.encode Launch.Base64.encode||1|SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution redefines Fvdep.Base64.Encode.V1_0_0.encode
R.d2.propext|drop propext||1|SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution lacks propext
R.d2.collision|collide Launch.Proof.Base64.encode_eq Fvdep.Base64.Encode.V1_0_0.encode|--proof-as Fvdep.Base64.Encode.V1_0_0.encode|1|SIMULATION NOT PROVEN judge: the proof does not prove the required statement $SIM)|  detail: the proof's name Fvdep.Base64.Encode.V1_0_0.encode is a trusted constant
R.d2.propext-type|refield propext type||1|SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution redefines propext
R.d2.prelude|refield Nat.add value||1|SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM)|  detail: the solution redefines Nat.add
R.d2.budget-s|none|--limit judge.work=5|1|SIMULATION NOT PROVEN judge: the proof does not prove the required statement $SIM, --limit judge.work)|  detail: the comparison passes its work budget
R.d2.budget-g|none|--limit judge.work=1000|1|SIMULATION NOT PROVEN judge: the implementation changed between phases $SIM, --limit judge.work)|  detail: the comparison passes its work budget
R.d2.long-cause|none|--proof-as $long|1|SIMULATION NOT PROVEN judge: the proof does not prove the required statement $SIM)|  detail: ${lcause:0:1021}...
R.d2.missing|missing||2|~^SIMULATION infra io: the export .*/e2\.R\.d2\.missing could not be read: .* \(overrides: given e1 \+ e2\)\$|-
R.d2.over-cap|sparse 134217729||2|~^SIMULATION infra io: the export .*/e2\.R\.d2\.over-cap passes the export cap of 134217728 bytes \(overrides: given e1 \+ e2\)\$|-"
# D1's own refusals, early stops + overrides (contract U7 D1, J3): name|project (`launch` =
# examples/launch's base64.encode, `launch-parse` = its semver.parse; else a fresh base64.encode
# project: `impl-spec` names the spec as the implementation, `theorem` + `ill-typed` append a
# refused / an ill-typed declaration to the implementation)|extra options|exit|lines present
# (`;`-separated EREs)|a line start absent (`-` = none).
XCASES="X.dup-explicit|launch|--roots1 Eq Eq|2|^fvdep-dev: phase 1's export roots name Eq twice\$|phase1 
X.dup-default|impl-spec||2|^fvdep-dev: phase 1's export roots name Fvdep\.Base64\.Encode\.V1_0_0\.encode twice\$|phase1 
X.refused|theorem||1|^NOT PROVEN base64\.encode@1\.0\.0: Launch\.Base64 [0-9]+:0 kind Lean\.Parser\.Command\.theorem\$|phase1 
X.ill-typed|ill-typed||1|^phase1 failed: ;^NOT PROVEN base64\.encode@1\.0\.0: .|statement 
X.override|launch-parse|--limit depth=4096 --deadline 600|0|^SIMULATION PROVEN semver\.parse@1\.0\.0 Launch\.Semver\.parse \(overrides: --limit depth, --deadline\)\$|-"
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
rnames=" $(printf '%s\n' "$RCASES" "$DCASES" "$XCASES" | cut -d'|' -f1 | tr '\n' ' ')"
[ -n "$selected" ] || [[ "$rnames" == *" $only "* ]] || { echo "judge-suite: no case ${only:-}"; exit 2; }
touch "$logs/out"
if [ -n "$selected" ]; then
    # shellcheck disable=SC2016 # the fields expand in the child bash that xargs starts
    printf '%s\n' "$selected" | xargs -d '\n' -P "${FVDEP_JUDGE_JOBS:-3}" -I{} bash -c \
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
    printf '%s\n' "$rsel" | xargs -d '\n' -P "${FVDEP_JUDGE_JOBS:-3}" -I{} bash -c \
        'IFS="|" read -r a b c d e <<<"{}"; rsrc "$a" "$b" "$c" "$d" "$e"' >>"$logs/out"
fi

# D1's own refusals + overrides: the XCASES table (top).
xcase() {
    local name=$1 proj=$2 extra=$3 code=$4 present=$5 absent=$6 tmp="" s rc ok=1 id=base64.encode
    local sm=Fvdep.Base64.Encode.V1_0_0 sc=Fvdep.Base64.Encode.V1_0_0.encode dir mf=() opts=() p
    s=$(date +%s)
    case "$proj" in
        launch) dir=examples/launch; mf=(--manifest examples/launch/fvdep.toml) ;;
        launch-parse)
            dir=examples/launch; mf=(--manifest examples/launch/fvdep.toml); id=semver.parse
            sm=Fvdep.Semver.Parse.V1_0_0; sc=Fvdep.Semver.Parse.V1_0_0.parse ;;
        *)
            tmp=$(mktemp -d); dir=$tmp
            mkdir -p "$tmp/Launch/Proof"
            cp examples/launch/Launch/Base64.lean "$tmp/Launch/"
            cp examples/launch/Launch/Proof/Base64.lean "$tmp/Launch/Proof/"
            local impl=Launch.Base64.encode
            case "$proj" in
                impl-spec) impl=$sc ;;
                theorem) printf '\ntheorem t : True := True.intro\n' >>"$tmp/Launch/Base64.lean" ;;
                ill-typed) printf '\ndef broken : Nat := "x"\n' >>"$tmp/Launch/Base64.lean" ;;
            esac
            printf 'schema = 1\n\n[library]\ncommit = "%s"\n\n[modules."base64.encode"]\nversion = "1.0.0"\nshape = "fn"\nimpl_modules = ["Launch.Base64"]\nproof_modules = ["Launch.Proof.Base64"]\nimpl = "%s"\nproof = "Launch.Proof.Base64.encode_eq"\n' \
                0000000000000000000000000000000000000000 "$impl" >"$tmp/fvdep.toml" ;;
    esac
    [ -n "$extra" ] && read -ra opts <<<"$extra"
    FVDEP_CACHE=$cache "$dev" phase check "$dir" "$id" --library . --spec-module "$sm" --spec "$sc" \
        "${mf[@]}" --profile --judge "${opts[@]}" >"$logs/$name" 2>&1
    rc=$?
    [ -n "$tmp" ] && rm -rf "$tmp"
    [ "$rc" = "$code" ] || ok=0
    IFS=';' read -ra ps <<<"$present"
    for p in "${ps[@]}"; do command grep -qE "$p" "$logs/$name" || ok=0; done
    if [ "$absent" != - ]; then
        while IFS= read -r line; do [[ "$line" == "$absent"* ]] && ok=0; done <"$logs/$name"
    fi
    if [ "$ok" = 1 ]; then echo "PASS $name $(( $(date +%s) - s ))s"
    else
        echo "FAIL $name rc=$rc"
        command grep -vE '^(artifact|module|import|grammar) ' "$logs/$name" | tail -12 >"$logs/why.$name"
    fi
}
xsel=$(printf '%s\n' "$XCASES" | while IFS='|' read -r name rest; do
    [ -z "$only" ] || [ "$only" = "$name" ] || continue
    printf '%s|%s\n' "$name" "$rest"
done)
if [ -n "$xsel" ]; then
    while IFS='|' read -r a b c d e f; do xcase "$a" "$b" "$c" "$d" "$e" "$f"; done <<<"$xsel" \
        >>"$logs/out"
fi

# R through D2: the DCASES table (top).
e1="$logs/art/exports/e1.ndjson"; e2="$logs/art/exports/e2.ndjson"
while IFS='|' read -r name edit extra code want detail; do
    [ -z "$only" ] || [ "$only" = "$name" ] || continue
    if [ ! -f "$e1" ] || [ ! -f "$e2" ]; then echo "FAIL $name rc=- (no honest exports: E.fn.encode)" >>"$logs/out"; continue; fi
    s=$(date +%s); f="$e2"; proof=Launch.Proof.Base64.encode_eq; opts=()
    case "$edit" in
        none) ;;
        missing) f="$logs/e2.$name" ;;
        sparse\ *) f="$logs/e2.$name"; truncate -s "${edit#sparse }" "$f" ;;
        *)
            f="$logs/e2.$name"
            read -ra ed <<<"$edit"
            if ! python3 -I tests/judge/edit.py "${ed[0]}" "$e2" "$f" "${ed[@]:1}" 2>"$logs/why.$name"; then
                echo "FAIL $name (edit)" >>"$logs/out"
                continue
            fi ;;
    esac
    case "$extra" in
        --proof-as\ *) proof=${extra#--proof-as }; opts=() ;;
        "") opts=() ;;
        *) read -ra opts <<<"$extra" ;;
    esac
    FVDEP_CACHE=$cache "$dev" judge run "$e1" "$f" --spec Fvdep.Base64.Encode.V1_0_0.encode \
        --impl Launch.Base64.encode --proof "$proof" "${opts[@]}" >"$logs/$name" 2>&1
    rc=$?
    ok=1
    [ "$rc" = "$code" ] || ok=0
    if [[ "$want" == "~"* ]]; then command grep -qE "${want#\~}" "$logs/$name" || ok=0
    else command grep -qxF "$want" "$logs/$name" || ok=0; fi
    [ "$detail" = - ] || command grep -qxF "$detail" "$logs/$name" || ok=0
    # a stage that stopped ran no kernel (the honest pair alone reaches K)
    [ "$name" = R.d2.honest ] || ! command grep -q '^kernel ' "$logs/$name" || ok=0
    if [ "$ok" = 1 ]; then echo "PASS $name $(( $(date +%s) - s ))s" >>"$logs/out"
    else echo "FAIL $name rc=$rc" >>"$logs/out"; tail -12 "$logs/$name" | cut -c1-300 >"$logs/why.$name"; fi
done <<<"$DCASES"
sort "$logs/out"
for f in "$logs"/why.*; do
    [ -e "$f" ] || continue
    echo "--- ${f##*/why.}"; sed 's/^/    /' "$f"
done
pass=$(command grep -c '^PASS ' "$logs/out"); fail=$(command grep -c '^FAIL ' "$logs/out")
# Each selected case reported exactly once (a lost or doubled case never passes the tally).
ids=$({ printf '%s\n' "$CASES" | cut -d'|' -f1 | sed 's/^/E./'
    printf '%s\n' "$RCASES" "$XCASES" "$DCASES" | cut -d'|' -f1; } | while read -r id; do
    [ -z "$only" ] || [ "$only" = "$id" ] || { [[ "$only" == R.d2.* ]] && [ "$id" = E.fn.encode ]; } ||
        continue
    printf '%s\n' "$id"
done)
tally=0
while read -r id; do
    n=$(command grep -cE "^(PASS|FAIL) ${id//./\\.}( |\$)" "$logs/out")
    [ "$n" = 1 ] || { echo "judge-suite: case $id reported $n times"; tally=1; }
done <<<"$ids"
[ "$(printf '%s\n' "$ids" | wc -l)" = "$((pass + fail))" ] || tally=1
# K5's default target vs the launch closures' fills (contract U7 Q1, U5 Q): one data point a run.
echo "judge-suite: the shared cache holds $(du -sb "$cache" | cut -f1) bytes"
echo "judge-suite: $pass passed, $fail failed"
[ "$fail" = 0 ] && [ "$pass" -gt 0 ] && [ "$tally" = 0 ]
