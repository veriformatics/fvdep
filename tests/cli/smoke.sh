#!/usr/bin/env bash
# The built binary end to end: output streams + exit codes (docs/interface.md §1; contract U1 K2).
# Usage: tests/cli/smoke.sh <fvdep binary>. Prints PASS|FAIL per case; rc = failures.
set -uo pipefail

bin="${1:?usage: tests/cli/smoke.sh <fvdep binary>}"
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
version="$(sed -n 's/^def version : String := "\(.*\)"$/\1/p' "$root/Fvdep/Version.lean")"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
fails=0
usage_line='Usage: fvdep <command> [<arguments>]'

# case NAME WANT_RC WANT_STREAM(stdout|stderr) WANT_FIRST_LINE ARGS…
case_() {
    local name="$1" want_rc="$2" stream="$3" first="$4" rc out err
    shift 4
    "$bin" "$@" >"$tmp/out" 2>"$tmp/err"
    rc=$?
    out="$tmp/out" err="$tmp/err"
    [[ "$stream" == stderr ]] && { out="$tmp/err" err="$tmp/out"; }
    if [[ $rc -eq $want_rc && "$(head -n 1 "$out")" == "$first" && ! -s "$err" ]]; then
        printf 'PASS %s\n' "$name"
    else
        printf 'FAIL %s (rc %d, want %d; %s first line "%s", want "%s"; other stream %s bytes)\n' \
            "$name" "$rc" "$want_rc" "$stream" "$(head -n 1 "$out")" "$first" "$(wc -c <"$err")"
        fails=$((fails + 1))
    fi
}

if [[ -z "$version" ]]; then
    printf 'FAIL no version in Fvdep/Version.lean\n'
    exit 1
fi
case_ "--version" 0 stdout "fvdep $version" --version
# Whole-output check: --version prints exactly one line.
"$bin" --version >"$tmp/out" 2>/dev/null
if cmp -s "$tmp/out" <(printf 'fvdep %s\n' "$version"); then
    printf 'PASS --version output is exactly "fvdep %s" + LF\n' "$version"
else
    printf 'FAIL --version output is not exactly "fvdep %s" + LF\n' "$version"
    fails=$((fails + 1))
fi
case_ "help" 0 stdout "$usage_line" help
case_ "--help" 0 stdout "$usage_line" --help
case_ "help help" 0 stdout "$usage_line" help help
case_ "help --help" 0 stdout "$usage_line" help --help
"$bin" help >"$tmp/out" 2>/dev/null
if grep -q -- '--version' "$tmp/out" && grep -q -- '  help ' "$tmp/out"; then
    printf 'PASS help names --version + help\n'
else
    printf 'FAIL help does not name --version + help\n'
    fails=$((fails + 1))
fi
case_ "no argument" 2 stderr "$usage_line"
case_ "unknown command" 2 stderr "$usage_line" frobnicate
case_ "unknown option" 2 stderr "$usage_line" --frobnicate
case_ "extra argument" 2 stderr "$usage_line" --version extra

# A failed write of the command's own output = I/O failure (docs/interface.md §2): exit 2, the
# reason on stderr while stderr accepts it, nothing written to stdout by the handler. /dev/full
# fails every write; `>&-` closes the stream. Each case truncates out + err first.
# msg_ok: stderr = exactly one line `Could not write the output: <reason>.` + LF.
msg_ok() {
    [[ $(wc -l <"$tmp/err") -eq 1 && "$(tail -c 1 "$tmp/err" | od -An -tx1 | tr -d ' ')" == 0a ]] &&
        grep -qx 'Could not write the output: .*[^ .]\.' "$tmp/err"
}
io_check() { # NAME RC STDERR(message: msg_ok | empty | any: stderr itself unwritable)
    local ok=0
    if [[ $2 -eq 2 && ! -s "$tmp/out" ]]; then
        case "$3" in
        message) msg_ok && ok=1 ;;
        empty) [[ -s "$tmp/err" ]] || ok=1 ;;
        *) ok=1 ;;
        esac
    fi
    if [[ $ok -eq 1 ]]; then
        printf 'PASS %s\n' "$1"
    else
        printf 'FAIL %s (rc %d, want 2; stderr "%s"; stdout %s bytes)\n' "$1" "$2" \
            "$(head -n 1 "$tmp/err")" "$(wc -c <"$tmp/out")"
        fails=$((fails + 1))
    fi
}
: >"$tmp/out" && : >"$tmp/err"
"$bin" --version >/dev/full 2>"$tmp/err"
io_check "stdout write fails (--version >/dev/full)" $? message
: >"$tmp/out" && : >"$tmp/err"
"$bin" frobnicate >"$tmp/out" 2>/dev/full
io_check "stderr write fails (usage error 2>/dev/full)" $? any
: >"$tmp/out" && : >"$tmp/err"
"$bin" --version >/dev/full 2>/dev/full
io_check "both streams fail" $? any
# A reader that stopped reading (`fvdep help | head -0`) = broken pipe: exit 2, quiet, as standard
# tools. A FIFO whose last reader closed fails the write every time (a real `| head` races it).
# `>&-` cannot stand in for a closed stream: the runtime reuses fd 1 (observed EINVAL, not EBADF).
mkfifo "$tmp/pipe"
# shellcheck disable=SC2094 # one FIFO opened read-write + write-only on purpose (no reader left)
exec 3<>"$tmp/pipe" 4>"$tmp/pipe"
exec 3<&-
: >"$tmp/out" && : >"$tmp/err"
"$bin" help >&4 2>"$tmp/err"
io_check "reader closed the pipe (help into a FIFO without reader)" $? empty
exec 4>&-
exit "$fails"
