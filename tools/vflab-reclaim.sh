#!/usr/bin/env bash
# Removes abandoned fvdep workspaces on vflab (contract U1 R6), from the desktop that owns their
# worktrees: each ~/gate/ws/fvdep-* whose recorded origin is no git worktree on this machine, or
# that holds no origin record, goes (+ its .origin, .lock + stray run bundles), unless a run holds
# its lock. Entries without the `fvdep-` prefix (fvapi's) are never read or touched.
# Usage: tools/vflab-reclaim.sh [--dry-run]   FVDEP_VFLAB = ssh target (default vflab)
set -uo pipefail

host="${FVDEP_VFLAB:-vflab}"
dry=0
case "${1:-}" in
    "") ;;
    --dry-run) dry=1 ;;
    *)
        printf 'usage: tools/vflab-reclaim.sh [--dry-run]\n' >&2
        exit 2
        ;;
esac
ssh_opts=(-o BatchMode=yes)

# name<TAB>origin (`-` = none: tab runs collapse under IFS)<TAB>bytes<TAB>locked per workspace.
# shellcheck disable=SC2016
listing="$(ssh "${ssh_opts[@]}" "$host" 'cd ~/gate/ws 2>/dev/null || exit 0
    for d in fvdep-*; do
        [ -d "$d" ] || continue
        o="$(cat "$d.origin" 2>/dev/null || true)"
        s="$(du -sb "$d" | cut -f1)"
        l=0
        if [ -e "$d.lock" ] && ! flock -n "$d.lock" true; then l=1; fi
        printf "%s\t%s\t%s\t%s\n" "$d" "${o:--}" "$s" "$l"
    done')" || {
    printf 'vflab-reclaim: cannot list workspaces on %s\n' "$host" >&2
    exit 2
}

freed=0
while IFS=$'\t' read -r name origin bytes locked; do
    [[ -n "$name" ]] || continue
    [[ "$origin" == - ]] && origin=""
    if [[ ! "$name" =~ ^fvdep-[A-Za-z0-9._-]+$ ]]; then
        printf 'vflab-reclaim: skip unexpected name %q\n' "$name" >&2
        continue
    fi
    if [[ -n "$origin" && "$(git -C "$origin" rev-parse --show-toplevel 2>/dev/null)" == "$origin" ]]; then
        printf 'keep    %s (%s)\n' "$name" "$origin"
        continue
    fi
    if [[ "$locked" == 1 ]]; then
        printf 'busy    %s (a run holds its lock)\n' "$name"
        continue
    fi
    printf 'remove  %s (%s, %s bytes)\n' "$name" "${origin:-no origin record}" "$bytes"
    freed=$((freed + bytes))
    [[ $dry -eq 1 ]] && continue
    # shellcheck disable=SC2029  # the validated name expands here on purpose
    # </dev/null: ssh would otherwise drain the rest of the listing from this loop's stdin.
    ssh "${ssh_opts[@]}" "$host" "cd ~/gate/ws && rm -rf -- '$name' '$name.origin' '$name.lock' '$name'.bundle.*" </dev/null || {
        printf 'vflab-reclaim: removing %s failed\n' "$name" >&2
        exit 1
    }
done <<<"$listing"
printf 'vflab-reclaim: %s %d bytes\n' "$([[ $dry -eq 1 ]] && echo 'would free' || echo freed)" "$freed"
