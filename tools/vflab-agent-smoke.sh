#!/usr/bin/env bash
# Drafting-agent preflight on vflab (Decisions `Growth`; Tasks `Growth preflight`), after
# tools/vflab-provision.sh. Each check runs as fvdep-agent in fvapi_gate.slice:
#   isolation — an eturkes process cannot read the agent unit's credential or its environment
#     (a canary credential; positive control: root reads both);
#   binary — the pinned claude starts under bwrap (`--version` names the pinned version);
#   login — with /etc/fvdep/claude-oauth-token present, `claude -p` under bwrap answers a fixed
#     prompt (the subscription login works unattended).
# bwrap: every namespace unshared but the network (the API), writes confined to a tmpfs, the
# binary + system files read-only. The token goes LoadCredential → environment, never argv:
# /proc/<pid>/cmdline is world-readable.
# Usage: tools/vflab-agent-smoke.sh   FVDEP_VFLAB = ssh target (default vflab).
# rc 0 = every check held; 1 = a check failed; 3 = token absent, the rest held; 2 = usage.
set -uo pipefail

host="${FVDEP_VFLAB:-vflab}"
[[ -n "$host" && "$host" != -* ]] || {
    printf 'vflab-agent-smoke: FVDEP_VFLAB=%q: want an ssh host\n' "$host" >&2
    exit 2
}
claude_version="$(sed -n 's/^claude_version=\([0-9.]*\)$/\1/p' \
    "$(dirname -- "${BASH_SOURCE[0]}")/vflab-provision.sh")"
[[ -n "$claude_version" ]] || {
    printf 'vflab-agent-smoke: no claude_version in tools/vflab-provision.sh\n' >&2
    exit 2
}

# Runs as eturkes on vflab; $1 = claude version.
remote="$(
    cat <<'REMOTE'
set -uo pipefail
version=$1
fails=0
check() { # NAME DETAIL HELD(0|1)
    if [ "$3" -eq 1 ]; then
        printf 'SMOKE %s: held (%s)\n' "$1" "$2"
    else
        printf 'SMOKE %s: FAILED (%s)\n' "$1" "$2"
        fails=$((fails + 1))
    fi
}
hex() { od -An -N"$1" -tx1 /dev/urandom | tr -d ' \n'; }
unit_opts=(--uid=fvdep-agent --gid=fvdep-agent --slice=fvapi_gate.slice --collect
    --expand-environment=no --property=MemoryMax=4G --property=MemorySwapMax=0)

unit=fvdep-agent-probe-$(hex 4)
canary=canary-$(hex 8)
sudo systemd-run -q --unit="$unit" "${unit_opts[@]}" --property=RuntimeMaxSec=60 \
    --property=SetCredential="probe:$canary" \
    -- /bin/sh -c 'CANARY=$(cat "$CREDENTIALS_DIRECTORY/probe"); export CANARY; exec sleep 30' \
    </dev/null
root_env=0 pid=0
for _ in $(seq 20); do
    pid=$(systemctl show -P MainPID "$unit.service")
    if [ "$pid" != 0 ] && sudo cat "/proc/$pid/environ" 2>/dev/null | tr '\0' '\n' |
        grep -qx "CANARY=$canary"; then
        root_env=1
        break
    fi
    sleep 0.5
done
root_cred=0
[ "$(sudo cat "/run/credentials/$unit.service/probe" 2>/dev/null)" = "$canary" ] && root_cred=1
cat "/proc/$pid/environ" >/dev/null 2>&1
user_env=$?
cat "/run/credentials/$unit.service/probe" >/dev/null 2>&1
user_cred=$?
sudo systemctl stop "$unit.service" 2>/dev/null
held=0
[ "$root_env$root_cred" = 11 ] && [ "$user_env" -ne 0 ] && [ "$user_cred" -ne 0 ] && held=1
check isolation "root reads environment $root_env, credential $root_cred; eturkes read rc environment $user_env, credential $user_cred" "$held"

# The sandbox: $1 = claude version, the rest = claude's arguments.
# shellcheck disable=SC2016 # expands inside the unit
sandbox='set -eu
version=$1
shift
if [ -r "${CREDENTIALS_DIRECTORY:-/nonexistent}/claude-token" ]; then
    CLAUDE_CODE_OAUTH_TOKEN=$(cat "$CREDENTIALS_DIRECTORY/claude-token")
    export CLAUDE_CODE_OAUTH_TOKEN
fi
exec bwrap --unshare-all --share-net --die-with-parent --new-session \
    --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/sbin /sbin --symlink usr/lib /lib \
    --symlink usr/lib64 /lib64 --ro-bind /etc/ssl /etc/ssl \
    --ro-bind /etc/ca-certificates /etc/ca-certificates \
    --ro-bind "$(readlink -f /etc/resolv.conf)" /etc/resolv.conf --ro-bind /etc/hosts /etc/hosts \
    --ro-bind /etc/nsswitch.conf /etc/nsswitch.conf --ro-bind /etc/passwd /etc/passwd \
    --ro-bind /etc/group /etc/group --ro-bind "/opt/fvdep/claude/$version" /opt/claude \
    --proc /proc --dev /dev --tmpfs /tmp --dir /tmp/home --chdir /tmp \
    --setenv HOME /tmp/home --setenv SHELL /bin/bash --setenv DISABLE_AUTOUPDATER 1 \
    /opt/claude/claude "$@"'
agent() { # extra systemd-run options… -- claude arguments…
    local opts=()
    while [ "$1" != -- ]; do
        opts+=("$1")
        shift
    done
    shift
    sudo systemd-run -q "${unit_opts[@]}" --wait --pipe --property=Type=oneshot \
        --property=TimeoutStartSec=300 "${opts[@]}" \
        -- /bin/sh -c "$sandbox" sandbox "$version" "$@" </dev/null
}

out=$(agent -- --version 2>&1)
rc=$?
held=0
[ "$rc" -eq 0 ] && [ "$(printf '%s\n' "$out" | head -n 1)" = "$version (Claude Code)" ] && held=1
check binary "rc $rc, output \"$(printf '%s' "$out" | head -n 1)\"" "$held"

token=/etc/fvdep/claude-oauth-token
if ! sudo test -s "$token"; then
    printf 'SMOKE login: absent (%s missing; the user stores it, README)\n' "$token"
    [ "$fails" -eq 0 ] && exit 3
    exit 1
fi
out=$(agent --property=LoadCredential="claude-token:$token" -- \
    -p 'Reply with the single word fvdep-agent-ok and nothing else.' 2>&1)
rc=$?
held=0
[ "$rc" -eq 0 ] && printf '%s\n' "$out" | grep -q 'fvdep-agent-ok' && held=1
check login "rc $rc, output \"$(printf '%s' "$out" | head -c 200)\"" "$held"
[ "$fails" -eq 0 ]
REMOTE
)"
ssh -o BatchMode=yes "$host" "bash -c $(printf '%q' "$remote") vflab-agent-smoke $claude_version" </dev/null
