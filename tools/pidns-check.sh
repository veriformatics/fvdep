#!/usr/bin/env bash
# Fails closed (exit 1, naming why) unless this job runs in a PID namespace of its own: the sandbox
# suites run `fvdep-step`, whose `kill(-1)` a regression could carry out of its step, and vflab is
# shared with fvapi (`.claude/rules/sandbox.md`). The host's initial PID namespace is the one that
# shows kernel threads (kthreadd); a `tools/vflab-run` unit never does (PrivatePIDs). A GitHub
# Actions runner (a VM of its own) passes. Usage: tools/pidns-check.sh [proc root, default /proc]
set -uo pipefail
proc="${1:-/proc}"
[[ "${GITHUB_ACTIONS:-}" == true ]] && exit 0
if [[ ! -e "$proc/1" ]]; then
    printf "pidns-check: %s lists no PID 1, so this job's PID namespace is unknown\n" "$proc" >&2
    exit 1
fi
if grep -qsx kthreadd "$proc"/[0-9]*/comm; then
    printf "pidns-check: this job shares the host's PID namespace (%s shows kthreadd): %s\n" \
        "$proc" "run it through tools/vflab-run" >&2
    exit 1
fi
