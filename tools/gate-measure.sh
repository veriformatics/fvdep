#!/usr/bin/env bash
# The run phase's inputs (tools/gate.sh GATE_FIRST + GATE_WEIGHTS): each named stage (default: every
# stage but tree-clean, the build phase first) alone, in registry order; per stage its wall-clock,
# CPU seconds (user + sys of its processes) + the run cgroup's peaks sampled every 0.2 s (GiB:
# memory.current; memory.stat anon, shmem = tmpfs files, file = page cache incl. shmem). A stage's
# weight = its anon + shmem peak rounded up (page cache is reclaimed under the cap; anon + tmpfs are
# not: no swap). Run on vflab with no other fvdep job there:
# tools/vflab-run bash tools/gate-measure.sh [STAGE…]
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root" || exit 1
# shellcheck source=tools/gate.sh
source tools/gate.sh
registry_ok || exit 2
cg="/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)"
[[ -r "$cg/memory.stat" ]] || {
    printf 'gate-measure: no cgroup v2 memory accounting at %s\n' "$cg" >&2
    exit 2
}
names=("$@")
[[ $# -gt 0 ]] || mapfile -t names < <(awk 'NF && $1 != "tree-clean" { print $1 }' <<<"$STAGES")
for name in "${names[@]}"; do
    [[ "$(type -t "${name//-/_}")" == function ]] || {
        printf 'gate-measure: no stage %s\n' "$name" >&2
        exit 2
    }
done
printf 'gate-measure: %s CPUs, cap %s\n' "$(nproc)" "$(cat "$cg/memory.max")"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT

# Peaks (bytes) until TERM, then written to FILE: current anon shmem file anon+shmem.
sample() { # FILE
    local cur anon shmem file p=(0 0 0 0 0) i v
    trap 'printf "%s\n" "${p[*]}" >"$1"; exit 0' TERM
    while :; do
        cur="$(<"$cg/memory.current")"
        read -r anon shmem file < <(awk '$1 == "anon" { a = $2 } $1 == "shmem" { s = $2 }
            $1 == "file" { f = $2 } END { print a, s, f }' "$cg/memory.stat")
        i=0
        for v in "$cur" "$anon" "$shmem" "$file" $((anon + shmem)); do
            ((v > p[i])) && p[i]=$v
            i=$((i + 1))
        done
        sleep 0.2
    done
}

gib() { awk -v b="$1" 'BEGIN { printf "%.1f", b / 2^30 }'; }
# GATE_WEIGHTS's value: whole GiB, rounded up, at least 1 (an unlisted stage weighs 1).
weight() { awk -v b="$1" 'BEGIN { w = int(b / 2^30); if (w * 2^30 < b) w++; print (w > 1 ? w : 1) }'; }
TIMEFORMAT='%R %U %S'
for name in "${names[@]}"; do
    sample "$out/$name.mem" &
    sampler=$!
    { time { ("${name//-/_}") >"$out/$name.log" 2>&1; echo $? >"$out/$name.rc"; }; } 2>"$out/$name.time"
    kill -TERM "$sampler"
    wait "$sampler"
    read -r real user sys <"$out/$name.time"
    read -r cur anon shmem file both <"$out/$name.mem"
    printf 'MEASURE %s rc=%s wall=%ss cpu=%ss current=%sG anon=%sG shmem=%sG file=%sG weight=%s\n' \
        "$name" "$(<"$out/$name.rc")" "$real" "$(awk -v u="$user" -v s="$sys" 'BEGIN { print u + s }')" \
        "$(gib "$cur")" "$(gib "$anon")" "$(gib "$shmem")" "$(gib "$file")" "$(weight "$both")"
done
