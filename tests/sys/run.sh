#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname -- "$0")/../.."
bash tests/sys/build.sh
work=$(mktemp -d "$PWD/tests/sys/.run.XXXXXX")
zfs=""
cleanup() {
    rm -rf -- "$work"
    if [[ -n "$zfs" ]]; then rm -rf -- "$zfs"; fi
}
trap cleanup EXIT
# F.filesystem.zfs needs fvdep's ZFS dataset (vflab; its sys-test/ root = tools/vflab-provision.sh):
# on that host the root must exist, elsewhere (CI runners) the case reports SKIP by name.
zfs_args=()
if [[ -d /srv/data/fvdep ]]; then
    root=/srv/data/fvdep/sys-test
    if [[ ! -d "$root" || ! -w "$root" ]]; then
        printf 'tests/sys: %s missing or not writable: run tools/vflab-provision.sh\n' "$root" >&2
        exit 2
    fi
    zfs=$(mktemp -d -p "$root" f6.XXXXXXXX)
    zfs_args=(--zfs "$zfs")
fi
python3 -I tests/sys/suite.py --work "$work" "${zfs_args[@]}" \
    --report "${FVDEP_SYS_REPORT:-tests/sys/.results/latest.tsv}" \
    --label "${FVDEP_SYS_LABEL:-current}" "$@"
