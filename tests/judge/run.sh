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
cache=$(mktemp -d); logs=$(mktemp -d); trap 'rm -rf "$cache" "$logs"' EXIT
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
one() {
    local name=$1 id=$2 mf=$3 sm=$4 sc=$5 am=$6 ac=$7 impl=$8 abi=() s rc
    [ -n "$am" ] && abi=(--abi-module "$am" --abi "$ac")
    s=$(date +%s)
    FVDEP_CACHE=$cache "$dev" phase check examples/launch "$id" --library . --spec-module "$sm" \
        --spec "$sc" "${abi[@]}" --manifest "examples/launch/$mf" --profile --judge >"$logs/$name" 2>&1
    rc=$?
    if [ "$rc" = 0 ] && command grep -qxF "PROVEN $id@1.0.0 $impl" "$logs/$name"; then
        echo "PASS E.$name $(( $(date +%s) - s ))s"
    else
        echo "FAIL E.$name rc=$rc"
        command grep -vE '^(artifact|module|import|grammar) ' "$logs/$name" | tail -12 >"$logs/why.$name"
    fi
}
export -f one; export dev cache logs
selected=$(printf '%s\n' "$CASES" | while IFS='|' read -r name rest; do
    [ -z "$only" ] || [ "$only" = "E.$name" ] || continue
    printf '%s|%s\n' "$name" "$rest"
done)
[ -n "$selected" ] || { echo "judge-suite: no case ${only:-}"; exit 2; }
# shellcheck disable=SC2016 # the fields expand in the child bash that xargs starts
printf '%s\n' "$selected" | xargs -P "${FVDEP_JUDGE_JOBS:-3}" -I{} bash -c \
    'IFS="|" read -r a b c d e f g h <<<"{}"; one "$a" "$b" "$c" "$d" "$e" "$f" "$g" "$h"' >"$logs/out"
sort "$logs/out"
for f in "$logs"/why.*; do
    [ -e "$f" ] || continue
    echo "--- ${f##*/why.}"; sed 's/^/    /' "$f"
done
pass=$(command grep -c '^PASS ' "$logs/out"); fail=$(command grep -c '^FAIL ' "$logs/out")
echo "judge-suite: $pass passed, $fail failed"
[ "$fail" = 0 ] && [ "$pass" -gt 0 ]
