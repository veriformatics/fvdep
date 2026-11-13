#!/usr/bin/env bash
# Provisions vflab for fvdep growth (Decisions `Growth`; Tasks `Growth preflight`) from the desktop.
# Idempotent: each piece missing or off its stated state is set + printed; the rest stays as is.
# Host maintenance ⇒ announce it to the fvapi session first (CLAUDE.local.md).
# - ZFS dataset data/fvdep at /srv/data/fvdep (child of the encrypted pool `data`, under its key),
#   quota 64G = fvdep's bound on the pool it shares with fvapi; growth/ = eturkes 0750.
# - System user fvdep-agent (no home, nologin) = the drafting agent's UID: same-UID processes can
#   read a unit's credentials + /proc/<pid>/environ ⇒ the subscription token never reaches an
#   eturkes process.
# - /etc/fvdep = root 0700, the token drop: /etc/fvdep/claude-oauth-token (root 0600), read only by
#   systemd LoadCredential into the agent's unit.
# - Claude Code native binary /opt/fvdep/claude/<version>/claude (root 0755), pinned by version +
#   the linux-x64 SHA-256 of the release manifest, whose detached PGP signature verified against the
#   release key 31DDDE24DDFAB679F42D7BD2BAA929FF1A7ECACE when pinned.
# Usage: tools/vflab-provision.sh   FVDEP_VFLAB = ssh target (default vflab). rc 0 = provisioned.
set -euo pipefail

host="${FVDEP_VFLAB:-vflab}"
[[ -n "$host" && "$host" != -* ]] || {
    printf 'vflab-provision: FVDEP_VFLAB=%q: want an ssh host\n' "$host" >&2
    exit 2
}
claude_version=2.1.311
claude_sha256=86dc1fcc69498159eaf15f446613e847010f9036bfbbdffd4c49350be8489ada

# Runs as root on vflab; $1 = claude version, $2 = its SHA-256.
remote="$(
    cat <<'REMOTE'
set -euo pipefail
version=$1 sha=$2
say() { printf 'vflab-provision: %s\n' "$*"; }
if ! zfs list -H -o name data/fvdep >/dev/null 2>&1; then
    zfs create -o quota=64G data/fvdep
    say 'created dataset data/fvdep (quota 64G)'
fi
if [ "$(zfs get -H -o value quota data/fvdep)" != 64G ]; then
    zfs set quota=64G data/fvdep
    say 'set the quota of data/fvdep to 64G'
fi
[ "$(zfs get -H -o value mountpoint data/fvdep)" = /srv/data/fvdep ] &&
    [ "$(zfs get -H -o value mounted data/fvdep)" = yes ] ||
    { say 'data/fvdep is not mounted at /srv/data/fvdep'; exit 1; }
install -d -o eturkes -g eturkes -m 0750 /srv/data/fvdep/growth
if ! id -u fvdep-agent >/dev/null 2>&1; then
    useradd --system --user-group --no-create-home --home-dir /nonexistent \
        --shell /usr/sbin/nologin fvdep-agent
    say 'created system user fvdep-agent'
fi
install -d -o root -g root -m 0700 /etc/fvdep
token=/etc/fvdep/claude-oauth-token
if [ -e "$token" ]; then
    chown root:root "$token"
    chmod 0600 "$token"
fi
dir=/opt/fvdep/claude/$version
bin=$dir/claude
if [ ! -f "$bin" ] || [ "$(sha256sum <"$bin" | cut -d ' ' -f 1)" != "$sha" ]; then
    install -d -m 0755 /opt/fvdep /opt/fvdep/claude
    tmp=$(mktemp -d /opt/fvdep/claude/.download.XXXXXX)
    trap 'rm -rf "$tmp"' EXIT
    curl -fsSL --proto =https --retry 3 -o "$tmp/claude" \
        "https://downloads.claude.ai/claude-code-releases/$version/linux-x64/claude"
    got=$(sha256sum <"$tmp/claude" | cut -d ' ' -f 1)
    [ "$got" = "$sha" ] || { say "claude $version: SHA-256 $got, want $sha"; exit 1; }
    chmod 0755 "$tmp/claude"
    install -d -m 0755 "$dir"
    mv -f "$tmp/claude" "$bin"
    say "installed claude $version at $bin"
fi
say "data/fvdep quota $(zfs get -H -o value quota data/fvdep), used $(zfs get -H -o value used data/fvdep);" \
    "fvdep-agent uid $(id -u fvdep-agent); claude $version SHA-256 verified;" \
    "token $([ -s "$token" ] && echo present || echo absent) at $token"
REMOTE
)"
ssh -o BatchMode=yes "$host" "sudo bash -c $(printf '%q' "$remote") vflab-provision $claude_version $claude_sha256" </dev/null
