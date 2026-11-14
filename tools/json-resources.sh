#!/usr/bin/env bash
# J5 resources (contract docs/contracts/U3-codecs.md "Resources (J5)"): every family × size, RUNS
# times, each in a fresh `fvdep-dev json measure` process (VmHWM = that run's peak): one TSV row
# per run + the host's 1-minute load before it. Recorded, not promised ⇒ run on a quiet host (no
# gate on vflab): tools/vflab-run bash tools/json-resources.sh [RUNS]
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
runs="${1:-3}"
(cd tool && lake build fvdep-dev >&2)
dev=tool/.lake/build/bin/fvdep-dev
printf '# CLK_TCK %s; nproc %s; runs %s\n' "$(getconf CLK_TCK)" "$(nproc)" "$runs"
printf 'family\tn\ttasks\tbytes\toutcome\tdecode_ms\tnormalize_ms\tprint_ms\tout_bytes\t'
printf 'release_ms\tcpu_ticks\trss_kB\thwm_kB\treleased_kB\tload1\n'
cell() {
    local i load out
    for ((i = 0; i < runs; i++)); do
        load="$(cut -d' ' -f1 /proc/loadavg)"
        out="$("$dev" json measure "$@")"
        printf '%s\n' "$out" | sed "s/\$/\t$load/"
    done
}
for f in deep digits string string-mb string-esc array; do
    for n in 100000 1000000 10000000; do cell "$f" "$n" 1; done
done
for f in ints keys-sorted keys-reverse keys-prefix object; do
    for n in 10000 100000 1000000; do cell "$f" "$n" 1; done
done
for n in 1000 10000 100000; do cell lock "$n" 1; done
for k in 1 2 4 8; do cell array 1000000 "$k"; done
# TASKS 0 = the calling thread (the CLI's path) vs one dedicated Task.
for f in array keys-prefix; do cell "$f" 100000 0; cell "$f" 1000000 0; done
# One process, 5 cycles each (a Task, the calling thread, an object family, a refused input):
# memory the allocator keeps plateaus, a leak grows per cycle.
cell array 1000000 1 5
cell array 1000000 0 5
cell keys-prefix 100000 0 5
cell string-esc 1000000 0 5
