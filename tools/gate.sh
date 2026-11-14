#!/usr/bin/env bash
# The one gate command: a human, an agent and CI run exactly this, so one result is one claim.
# On vflab (`.claude/rules/gate.md`): tools/vflab-run bash tools/gate.sh. Stages run to completion
# after a failure, each in a subshell (a stage that exits cannot end the run), so one run reports
# every problem; each prints `<stage> rc=N <s>s` + appends it to the step ledger, the run closes on
# `gate rc=N <s>s`. A missing tool or one whose pinned identity fails fails its stage: an
# unavailable tool = gate incomplete, never green. Contract: docs/contracts/U1-foundation.md.
# Usage: tools/gate.sh [--shard NAME] — no argument = every stage; a shard = its stages alone
# (CI runs one job per shard, see STAGES).
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root" || exit 1

failed=()

stamp() { printf '%s' "${EPOCHREALTIME//[!0-9]/}"; }
elapsed() {
    local us=$(($(stamp) - $1))
    printf '%d.%d' $((us / 1000000)) $((us / 100000 % 10))
}

# Step ledger = the record of which stages buy signal (CLAUDE.md `Execution`): one TSV row per
# stage per run, appended to the gitignored .gate/ledger.tsv of the run's root as the stage ends
# (tools/vflab-run keeps it across runs). Columns: date (run start, UTC), tree (the graded file
# set: tracked + untracked-unignored, so HEAD alone would miss uncommitted edits), kind (gate |
# shard:NAME | fast), step, seconds, verdict (green | red), class (`-` | a red's `unclassified`
# until tools/gate-ledger.sh classifies it). An unwritable ledger fails the run, named `ledger`.
ledger="$root/.gate/ledger.tsv"
ledger_kind=""
ledger_tree=unknown
ledger_ok=1

# Tree object of the graded file set (content + mode), through a scratch index: the real index
# and the worktree stay untouched.
gated_tree() {
    local tmp tree
    tmp="$(mktemp -d)" || return 1
    cp -- "$(git rev-parse --git-path index 2>/dev/null)" "$tmp/index" 2>/dev/null
    tree="$(GIT_INDEX_FILE="$tmp/index" git add -A 2>/dev/null &&
        GIT_INDEX_FILE="$tmp/index" git write-tree 2>/dev/null)"
    rm -rf -- "$tmp"
    printf '%s' "${tree:-unknown}"
}

ledger_begin() { # KIND
    ledger_kind="$1"
    ledger_date="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    ledger_tree="$(gated_tree)"
}

ledger_row() { # STEP RC SECONDS
    local verdict=green class=- header=""
    [[ -n "$ledger_kind" ]] || return 0
    if [[ $2 -ne 0 ]]; then
        verdict=red
        class=unclassified
    fi
    [[ -s "$ledger" ]] || header=$'date\ttree\tkind\tstep\tseconds\tverdict\tclass\n'
    if mkdir -p -- "${ledger%/*}" 2>/dev/null &&
        printf '%s%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$header" "$ledger_date" "$ledger_tree" \
            "$ledger_kind" "$1" "$3" "$verdict" "$class" 2>/dev/null >>"$ledger"; then
        return 0
    fi
    printf 'ledger: cannot append to %s\n' "$ledger" >&2
    ledger_ok=0
}

stage() {
    local name="$1" start rc secs
    shift
    start="$(stamp)"
    printf '\n=== %s ===\n' "$name"
    ("$@")
    rc=$?
    secs="$(elapsed "$start")"
    printf '%s rc=%d %ss\n' "$name" "$rc" "$secs"
    ledger_row "$name" "$rc" "$secs"
    [[ $rc -eq 0 ]] || failed+=("$name")
    return 0
}

# Stage · CI shards. A full run takes every stage in this order, each running the function of its
# name (`-` → `_`). CI runs one job per shard (gate.yml matrix), each on a fresh checkout, so a
# shard whose stages read the build lists lean-build too; `fanout` holds the matrix = these shards.
STAGES='
tools       lean checks
lean-build  lean
lean-style  lean
lean-test   lean
cli         lean
coverage    lean
ledger-suite lean
codec-suite lean
manifest-suite lean
fuzz-replay lean
imports     checks
preview     checks
spec        checks
shell       checks
python      checks
secrets     checks
vulns       checks
workflows   checks
fanout      checks
vendor      checks
vendor-upstream checks
deps        checks
renovate    checks
meta        checks
probes      lean
tree-clean  lean checks
'

# The iteration subset tools/fast-gate.sh runs (build-consuming stages after lean-build).
# shellcheck disable=SC2034
FAST_STAGES='imports preview spec shell python fanout vendor deps renovate meta lean-build lean-style lean-test cli coverage ledger-suite codec-suite manifest-suite fuzz-replay'

# Every Lake target of both packages (stage `meta` holds this list = the lakefiles' declarations).
ROOT_TARGETS=(Fvdep FvdepPreview)
TOOL_TARGETS=(FvdepCore FvdepIO «fvdep-cli» «fvdep-tests» FvdepDev «fvdep-dev» FvdepFuzz FvdepAudit FvdepLedger
    «fvdep-ledger» FvdepLedgerFixtures)

# Every shard STAGES names, once each, in first-use order.
shard_names() { awk 'NF { for (i = 2; i <= NF; i++) if (!seen[$i]++) print $i }' <<<"$STAGES"; }

# STAGES is nonempty; each row = a unique stage whose function exists + ≥ 1 shard.
registry_ok() {
    local rc=0 rows row name shards
    mapfile -t rows < <(awk 'NF' <<<"$STAGES")
    if [[ ${#rows[@]} -eq 0 ]]; then
        printf 'gate: STAGES is empty\n' >&2
        return 1
    fi
    for row in "${rows[@]}"; do
        read -r name shards <<<"$row"
        if [[ -z "$shards" ]]; then
            printf 'gate: stage %s has no shard\n' "$name" >&2
            rc=1
        fi
        if [[ "$(type -t "${name//-/_}")" != function ]]; then
            printf 'gate: stage %s has no function %s\n' "$name" "${name//-/_}" >&2
            rc=1
        fi
    done
    if [[ -n "$(awk 'NF { print $1 }' <<<"$STAGES" | sort | uniq -d)" ]]; then
        printf 'gate: duplicate stage names\n' >&2
        rc=1
    fi
    return $rc
}

# A pinned tool's installed path after tools/fetch-tools.sh verified it (prints nothing + fails
# otherwise); stages call this path, never a PATH lookup.
pinned() { bash tools/fetch-tools.sh "$1" >&2 && printf '%s' "$root/.tools/bin/$1"; }

tools() { bash tools/fetch-tools.sh; }

# Type-check + lint in one build: leanOptions carry autoImplicit off, warningAsError + the extra
# core linters (probes plant one violation per option).
lean_build() {
    local rc=0
    lake build "${ROOT_TARGETS[@]}" || rc=1
    (cd tool && lake build "${TOOL_TARGETS[@]}") || rc=1
    return $rc
}

# Layout rules + the pinned lean-fmt (format drift + lint findings) over both packages.
lean_style() { bash tools/lean-style.sh; }

lean_test() { (cd tool && lake test); }

# The shipped binary end to end: output streams + exit codes (docs/interface.md §1).
cli() { bash tests/cli/smoke.sh "$root/tool/.lake/build/bin/fvdep"; }

# Coverage ledger (docs/contracts/U2-core.md L1–L8): every claim's theorem type = its statement,
# axioms ⊆ std, root shape + call paths, compiled = checked, kernel replay (leanchecker), and
# docs/verification.md = the rendering.
coverage() { (cd tool && lake exe fvdep-ledger --check ../docs/verification.md); }

# SHA-256 over the tracked + untracked-unignored files under PATH…, both Lake configs + toolchain
# pins: a suite's input closure (over-inclusive: a missed input would reuse a stale green).
closure_key() {
    git ls-files -co --exclude-standard -z -- "$@" tool/lakefile.lean tool/lake-manifest.json \
        tool/lean-toolchain lakefile.lean lake-manifest.json lean-toolchain |
        sort -z | xargs -0 sha256sum | sha256sum | cut -c1-64
}

# A blind suite with its input closure KEY: with FVDEP_REUSE=1 (the fast gate) a green verdict
# stands while that closure stays byte-identical; the full gate always runs it. A run narrowed to
# one case (FVDEP_LEDGER_ONLY, FVDEP_CODEC_CASE, FVDEP_MANIFEST_CASE, FVDEP_FUZZ_TARGET) never vouches
# for the whole.
suite() { # NAME KEY CMD…
    local name="$1" key="$2" mark=".gate/$1.green"
    shift 2
    if [[ "${FVDEP_REUSE:-0}" == 1 && -n "$key" && -f "$mark" && "$(cat "$mark")" == "$key" ]]; then
        printf '%s: input closure %s = the last green run: verdict reused\n' "$name" "${key:0:12}"
        return 0
    fi
    "$@" || return 1
    [[ -z "${FVDEP_LEDGER_ONLY:-}${FVDEP_CODEC_CASE:-}${FVDEP_MANIFEST_CASE:-}${FVDEP_FUZZ_TARGET:-}" &&
        -n "$key" ]] || return 0
    mkdir -p .gate && printf '%s\n' "$key" >"$mark"
}

ledger_suite_key() {
    closure_key tool/FvdepLedger tool/FvdepLedger.lean tool/LedgerMain.lean \
        tool/FvdepLedgerFixtures tool/FvdepLedgerFixtures.lean tests/ledger
}

# The blind fixture suite (L9): the checker's planted breaches + clean controls; it grades the
# checker alone.
ledger_suite() { suite ledger-suite "$(ledger_suite_key)" bash tests/ledger/run.sh; }

# Shipped code the codec + manifest drivers build (the tool requires the root library by path).
shipped_closure() {
    closure_key "$@" tool/FvdepCore tool/FvdepCore.lean tool/FvdepIO tool/FvdepIO.lean c \
        vendor/hacl-star 'Fvdep*'
}

# The blind codec suite (tester-3; U3 J, H, D + S5): tests/codec/run.sh = the J/H/D cases through
# the codec driver + the S cases through the sanitized SHA-256 core; jq = the pinned one (its output
# bytes are the printer cases' second oracle).
codec_suite() {
    local jq
    jq="$(pinned jq)" || return 1
    suite codec-suite "$({ shipped_closure tests/codec tests/sha256; awk '$1 == "jq"' tools/tools.lock; } |
        sha256sum | cut -c1-64)" env PATH="${jq%/*}:$PATH" bash tests/codec/run.sh
}

# The blind manifest suite (tester-4; U3 T6): the reader, validator + printer through its driver.
manifest_suite() {
    suite manifest-suite "$(shipped_closure tests/manifest)" bash tests/manifest/run.sh \
        ${FVDEP_MANIFEST_CASE:+--case "$FVDEP_MANIFEST_CASE"}
}

# Fuzz corpora (contract U3 "Fuzz"; tools/fuzz.sh): every seed + pinned crash input through each
# target's engine-free replay build (a Lean target's panic aborts; C targets under gcc ASan + UBSan).
fuzz_replay() {
    suite fuzz-replay "$(shipped_closure tests/fuzz tool/FvdepFuzz tool/FvdepFuzz.lean tools/fuzz.sh)" \
        bash tools/fuzz.sh replay ${FVDEP_FUZZ_TARGET:+"$FVDEP_FUZZ_TARGET"}
}

# Each purpose-built check passes on a clean copy, fails on its planted input, passes restored.
probes() { bash tools/gate-probe.sh; }

# Library modules import Init, Std + the library; tool modules add Lean, Lake + the tool's libs.
imports() { bash tools/check-imports.sh imports; }

# No module under Fvdep imports the preview or proof trees.
preview() { bash tools/check-imports.sh preview; }

spec() { sh .agent/spec-lint .agent/spec.md; }

# Every shell script outside prototype/ (disposable, outside the gate until retired): `*.sh` +
# each other file whose shebang names sh or bash.
shell() {
    local files=() shellcheck
    shellcheck="$(pinned shellcheck)" || return 1
    mapfile -t files < <(
        git ls-files -co --exclude-standard -- '*.sh' ':!prototype/'
        git ls-files -co --exclude-standard -z -- ':!*.sh' ':!prototype/' | xargs -0 -r awk 'FNR == 1 {
            if (/^#!(\/usr)?\/bin\/(env +)?(ba)?sh([ \t]|$)/) print FILENAME
            nextfile }'
    )
    if [[ ${#files[@]} -eq 0 ]]; then
        printf 'shell: no shell script found\n' >&2
        return 1
    fi
    "$shellcheck" -- "${files[@]}"
}

# Stdlib-only gate helpers + test drivers; explicit configs prevent Pyrefly's silent basic fallback.
python() {
    local rc=0 ruff pyrefly
    ruff="$(pinned ruff)" || return 1
    pyrefly="$(pinned pyrefly)" || return 1
    "$ruff" check --config ruff.toml --output-format concise . || rc=1
    "$pyrefly" check --config pyrefly.toml --output-format=min-text --min-severity=warn \
        --threads 1 --skip-interpreter-query || rc=1
    return $rc
}

# History + every tracked or untracked-unignored file; live validation stays off (no network).
secrets() {
    local rc=0 leaks
    leaks="$(pinned betterleaks)" || return 1
    "$leaks" git --no-banner --no-color --redact --verbose . || rc=1
    git ls-files -co --exclude-standard -z |
        xargs -0 -r "$leaks" dir --no-banner --no-color --redact --verbose || rc=1
    return $rc
}

# Known vulnerabilities in the declared lockfile set (tools/lockfiles.txt).
vulns() {
    local scanner
    scanner="$(pinned osv-scanner)" || return 1
    python3 -I tools/check-vulns.py "$scanner"
}

workflows() {
    local rc=0 zizmor actionlint
    zizmor="$(pinned zizmor)" || return 1
    actionlint="$(pinned actionlint)" || return 1
    "$zizmor" --offline --no-progress .github/ || rc=1
    "$actionlint" || rc=1
    return $rc
}

# CI runs the gate as one job per gate.yml matrix shard: the matrix = the gate's shards, every
# stage has a shard, and job `gate` runs exactly one unconditional, unmasked
# `bash tools/gate.sh --shard "$SHARD"` step with SHARD bound to the matrix value and fail-fast
# off. Matched by YAML position (job keys at 2 spaces, job properties at 4, steps at 6, step keys
# at 8): the same text in a comment or a block scalar runs no gate and does not count.
fanout() {
    local rc=0 wf=.github/workflows/gate.yml matrix shards facts
    awk 'NF == 1 { print "fanout: stage " $1 " has no CI shard"; bad = 1 } END { exit bad }' \
        <<<"$STAGES" >&2 || rc=1
    matrix="$(sed -n 's/^ *shard: \[\(.*\)\]$/\1/p' "$wf" | tr -d ' ' | tr ',' '\n' | sort)"
    shards="$(shard_names | sort)"
    if [[ -z "$matrix" || "$matrix" != "$shards" ]]; then
        printf 'fanout: %s matrix shards [%s] != tools/gate.sh shards [%s]\n' "$wf" \
            "$(paste -sd, - <<<"$matrix")" "$(paste -sd, - <<<"$shards")" >&2
        rc=1
    fi
    # shellcheck disable=SC2016
    facts="$(awk '
        function flush() { if (run) { runs++; if (cond) masked++ } run = 0; cond = 0 }
        /^[^ #]/ { flush(); top = $0 }
        top == "jobs:" && /^  [^ #]/ { flush(); job = $1 }
        job == "gate:" {
            if ($0 ~ /^    (if|continue-on-error):/) jobmask = 1
            if ($0 ~ /^      fail-fast: false$/) failfast = 1
            if ($0 ~ /^      SHARD: \$\{\{ matrix\.shard \}\}$/) bound = 1
            if ($0 ~ /^      - /) flush()
            if ($0 ~ /^        run: bash tools\/gate\.sh --shard "\$SHARD"$/) run = 1
            if ($0 ~ /^(      - |        )(if|continue-on-error):/) cond = 1
        }
        END { flush(); print runs + 0, masked + 0, jobmask + 0, failfast + 0, bound + 0 }' "$wf")"
    if [[ "$facts" != "1 0 0 1 1" ]]; then
        printf 'fanout: %s job gate needs one unconditional, unmasked gate step, SHARD bound to the matrix + fail-fast false (runs masked job-mask fail-fast bound = %s)\n' \
            "$wf" "$facts" >&2
        rc=1
    fi
    return $rc
}

# Vendored upstream trees (vendor/*/lock.json) hold exactly their locked bytes; relock with
# tools/vendor-hacl.sh.
vendor() { bash tools/check-vendor.sh; }

# The locked upstream commit's allowlisted blobs = the lock + the tree (network: a fresh fetch by
# commit id; a Renovate bump of `commit` alone stays red here until relocked).
vendor_upstream() { bash tools/vendor-hacl.sh --check; }

# Every pin (lean-toolchain, tools/tools.lock, workflow actions, Lake packages, vendored
# upstreams) has a row in docs/dependencies.md naming its update path + scanner.
deps() { python3 -I tools/check-deps.py; }

# Renovate's custom managers extract every pin they own (lean-toolchain, tools/tools.lock, every
# Lake manifest, every vendor lock), and the lock file keeps one coherent version per tool.
renovate() { python3 -I tools/check-renovate.py; }

# One version in Fvdep/Version.lean + both lakefiles; the target lists above = every lean_lib +
# lean_exe the lakefiles declare; every rule file's frontmatter keeps the quoted `paths:` list.
meta() {
    local rc=0 lean root_v tool_v f declared listed
    lean="$(sed -n 's/^def version : String := "\(.*\)"$/\1/p' Fvdep/Version.lean)"
    root_v="$(sed -n 's/^  version := v!"\(.*\)"$/\1/p' lakefile.lean)"
    tool_v="$(sed -n 's/^  version := v!"\(.*\)"$/\1/p' tool/lakefile.lean)"
    if [[ -z "$lean" || "$lean" == *$'\n'* || "$lean" != "$root_v" || "$lean" != "$tool_v" ]]; then
        printf 'meta: Fvdep/Version.lean version "%s" != lakefile.lean "%s" / tool/lakefile.lean "%s"\n' \
            "$lean" "$root_v" "$tool_v" >&2
        rc=1
    fi
    declared="$(sed -n 's/^\(@\[default_target\] \)\{0,1\}lean_\(lib\|exe\) \([^ ]*\).*/\3/p' \
        lakefile.lean tool/lakefile.lean | sort)"
    listed="$(printf '%s\n' "${ROOT_TARGETS[@]}" "${TOOL_TARGETS[@]}" | sort)"
    if [[ "$declared" != "$listed" ]]; then
        printf 'meta: lakefile targets [%s] != tools/gate.sh target lists [%s]\n' \
            "$(paste -sd' ' - <<<"$declared")" "$(paste -sd' ' - <<<"$listed")" >&2
        rc=1
    fi
    for f in .claude/rules/*.md; do
        [[ -e "$f" ]] || continue
        awk -v f="$f" '
            NR == 1 { if ($0 != "---") exit 0; fm = 1; next }
            fm && $0 == "---" { closed = 1; exit }
            fm && /^paths:/ { paths = 1; next }
            fm && /^[^ ]/ { paths = 0 }
            fm && paths && !/^  - "[^"]+"$/ { printf "meta: %s:%d: paths entry is not a quoted glob\n", f, NR; bad = 1 }
            END { if (fm && !closed) { printf "meta: %s: frontmatter not closed\n", f; bad = 1 } exit bad }
        ' "$f" >&2 || rc=1
    done
    return $rc
}

# The run leaves the graded file set as it found it (a stage writing outside ignored paths fails).
tree_clean() {
    local now
    if [[ "$ledger_tree" == unknown ]]; then
        printf 'tree-clean: no graded tree (outside git)\n' >&2
        return 1
    fi
    now="$(gated_tree)"
    if [[ "$now" != "$ledger_tree" ]]; then
        printf 'tree-clean: the run changed the graded file set:\n' >&2
        git diff-tree -r --name-status "$ledger_tree" "$now" >&2
        return 1
    fi
}

main() {
    local start shard="" rows row name shards
    registry_ok || exit 2
    if [[ $# -gt 0 ]]; then
        if [[ $# -ne 2 || "$1" != --shard ]] || ! shard_names | grep -x -F -- "$2" >/dev/null; then
            printf 'usage: tools/gate.sh [--shard %s]\n' "$(shard_names | paste -sd'|' -)" >&2
            exit 2
        fi
        shard="$2"
    fi
    start="$(stamp)"
    if [[ -n "$shard" ]]; then ledger_begin "shard:$shard"; else ledger_begin gate; fi
    # An array, not a `while read` loop: stages keep the caller's stdin.
    mapfile -t rows <<<"$STAGES"
    for row in "${rows[@]}"; do
        read -r name shards <<<"$row"
        if [[ -n "$name" && ( -z "$shard" || " $shards " == *" $shard "* ) ]]; then
            stage "$name" "${name//-/_}"
        fi
    done
    printf '\n=== gate%s ===\n' "${shard:+ (shard $shard)}"
    [[ $ledger_ok -eq 1 ]] || failed+=(ledger)
    if [[ ${#failed[@]} -ne 0 ]]; then
        printf 'FAILED: %s\n' "${failed[*]}"
        printf 'gate rc=1 %ss\n' "$(elapsed "$start")"
        exit 1
    fi
    printf 'gate rc=0 %ss\n' "$(elapsed "$start")"
}

# Sourcing exposes the stage functions without running the gate (tools/fast-gate.sh, probes).
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
