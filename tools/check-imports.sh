#!/usr/bin/env bash
# Import policy (gate stages `imports`, `preview`). Prints `file:line: import X` per violation.
#   imports: library modules (Fvdep, FvdepPreview, FvdepProofs trees) import Init, Std + library
#            modules alone, so a consumer's build of a pinned snapshot stays toolchain-only; tool
#            shipped modules (tool/Main.lean, tool/FvdepCore + tool/FvdepIO trees) add Lean, Lake +
#            the tool's own libraries. Test modules are free.
#   preview: no module under Fvdep imports the preview or proof trees (previews + phase-2 proofs
#            never enter the published library).
# Usage: tools/check-imports.sh imports|preview
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root" || exit 1

# check PATTERN FILES… — every import of FILES matches PATTERN (an awk ERE over the module name;
# `[.]`, never `\.`: awk -v turns `\.` into `.`, which would admit `FvdepX` for `Fvdep`).
check() {
    local allowed="$1"
    shift
    if [[ $# -eq 0 ]]; then
        printf 'imports: no module found\n' >&2
        return 1
    fi
    awk -v ok="$allowed" '
        match($0, /^[ \t]*((public|private|meta)[ \t]+)*import[ \t]+/) {
            n = split(substr($0, RSTART + RLENGTH), mods, /[ \t]+/)
            for (i = 1; i <= n; i++) {
                if (mods[i] == "" || mods[i] ~ /^--/) break
                if (mods[i] !~ ok) {
                    printf "%s:%d: import %s\n", FILENAME, FNR, mods[i]
                    bad = 1
                }
            }
        }
        END { exit bad }' "$@" >&2
}

files() { git ls-files -co --exclude-standard -- "$@"; }

case "${1:-}" in
imports)
    rc=0
    mapfile -t lib < <(files Fvdep.lean 'Fvdep/*.lean' FvdepPreview.lean 'FvdepPreview/*.lean' \
        FvdepProofs.lean 'FvdepProofs/*.lean')
    check '^(Init|Std|Fvdep|FvdepPreview|FvdepProofs)([.]|$)' "${lib[@]}" || rc=1
    mapfile -t tool < <(files tool/Main.lean tool/FvdepCore.lean 'tool/FvdepCore/*.lean' \
        tool/FvdepIO.lean 'tool/FvdepIO/*.lean')
    check '^(Init|Std|Lean|Lake|Fvdep|FvdepCore|FvdepIO)([.]|$)' "${tool[@]}" || rc=1
    exit $rc
    ;;
preview)
    mapfile -t lib < <(files Fvdep.lean 'Fvdep/*.lean')
    check '^(Init|Std|Fvdep)([.]|$)' "${lib[@]}"
    ;;
*)
    printf 'usage: tools/check-imports.sh imports|preview\n' >&2
    exit 2
    ;;
esac
