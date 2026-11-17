#!/usr/bin/env bash
# CI setup for U5's sandbox (contract U5 G, CI): bubblewrap ≥ 0.8.0 on the runner (Ubuntu 26.04's
# `apparmor` package ships its `bwrap-userns-restrict` profile), then one step whose flags =
# `FvdepCore.Sandbox.ops` for {ro: (src, /fvdep/src), env: PATH=/usr/bin, 1 MiB per tmpfs}; its
# command = `/bin/sh` in place of the step helper (U5-B's). A runner that cannot sandbox fails here.
set -euo pipefail
if ! command -v bwrap >/dev/null; then
    sudo apt-get update -q
    sudo apt-get install -y -q bubblewrap
fi
bwrap --version
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir "$work/src"
# The step's script expands `$(pwd)` inside the sandbox.
# shellcheck disable=SC2016
bwrap --unshare-all --unshare-user --disable-userns --die-with-parent --new-session --cap-drop ALL \
    --clearenv --setenv PATH /usr/bin --ro-bind /usr /usr --symlink usr/lib /lib \
    --symlink usr/lib64 /lib64 --symlink usr/bin /bin --ro-bind "$work/src" /fvdep/src \
    --size 1048576 --tmpfs /fvdep/work --size 1048576 --tmpfs /tmp --proc /proc --dev /dev \
    --remount-ro / --remount-ro /dev --chdir /fvdep/src --json-status-fd 3 -- /bin/sh -c '
        [ "$(pwd)" = /fvdep/src ] || exit 7
        if touch /x 2>/dev/null || touch /fvdep/src/x 2>/dev/null; then exit 8; fi
        touch /fvdep/work/x /tmp/x || exit 9' 3>"$work/status.json"
grep -q '"exit-code": 0' "$work/status.json"
echo "install-bwrap: a sandbox step with R1's flags ran (status: exit-code 0)"
