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

# A finished stage: its rc line, its ledger row, its name among the failures.
report() { # NAME RC SECONDS
    printf '%s rc=%d %ss\n' "$1" "$2" "$3"
    ledger_row "$1" "$2" "$3"
    [[ $2 -eq 0 ]] || failed+=("$1")
    return 0
}

stage() {
    local name="$1" start rc
    shift
    start="$(stamp)"
    printf '\n=== %s ===\n' "$name"
    ("$@")
    rc=$?
    report "$name" "$rc" "$(elapsed "$start")"
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
library-suite lean
index-suite lean
fuzz-replay lean
sys-suite   lean
sandbox-suite lean
isolation   lean
acceptance  lean
index       lean
index-history lean
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

# Run phase (`run_stages`): the stages over 90 s alone start first (longest first), then the rest in
# registry order; a stage's weight = its peak memory alone (GiB, anon + tmpfs, rounded up; unlisted
# = 1). Both from `tools/vflab-run bash tools/gate-measure.sh [STAGE…]` (vflab, no other fvdep job).
GATE_FIRST='index-suite sandbox-suite acceptance sys-suite coverage'
GATE_WEIGHTS='index-suite=9 acceptance=10 coverage=5 lean-style=4 index=4 ledger-suite=3 sys-suite=3'

# The iteration subset tools/fast-gate.sh runs (build-consuming stages after lean-build).
# shellcheck disable=SC2034
FAST_STAGES='imports preview spec shell python fanout vendor deps renovate meta lean-build lean-style lean-test cli coverage ledger-suite codec-suite manifest-suite library-suite index-suite fuzz-replay sys-suite sandbox-suite isolation acceptance index index-history'

# Every Lake target of both packages (stage `meta` holds this list = the lakefiles' declarations).
ROOT_TARGETS=(Fvdep FvdepPreview FvdepProofs)
TOOL_TARGETS=(FvdepCore FvdepIO «fvdep-cli» «fvdep-step» «fvdep-tests» FvdepDev «fvdep-dev» FvdepFuzz FvdepAudit
    FvdepLedger «fvdep-ledger» FvdepLedgerFixtures)

# Every shard STAGES names, once each, in first-use order.
shard_names() { awk 'NF { for (i = 2; i <= NF; i++) if (!seen[$i]++) print $i }' <<<"$STAGES"; }

# STAGES is nonempty; each row = a unique stage whose function exists + ≥ 1 shard; GATE_FIRST +
# GATE_WEIGHTS name its stages, each weight whole GiB ≥ 1 (a stale name would weigh 1 unseen).
registry_ok() {
    local rc=0 rows row name shards names w
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
    names=" $(awk 'NF { printf "%s ", $1 }' <<<"$STAGES")"
    for w in $GATE_FIRST; do
        if [[ "$names" != *" $w "* ]]; then
            printf 'gate: GATE_FIRST names no stage %s\n' "$w" >&2
            rc=1
        fi
    done
    for w in $GATE_WEIGHTS; do
        if [[ "$names" != *" ${w%%=*} "* || ! "${w#*=}" =~ ^[1-9][0-9]*$ ]]; then
            printf 'gate: GATE_WEIGHTS entry %s is not <stage>=<GiB>\n' "$w" >&2
            rc=1
        fi
    done
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

# Layout rules + the pinned lean-fmt (format drift + lint findings) over both packages; verdict
# reused like a suite's in the fast gate (input closure = every Lean source, the formatter's
# configs + pin, the script).
lean_style() {
    suite lean-style \
        "$(closure_key '*.lean' .lean-fmt.toml tool/.lean-fmt.toml tools/lean-style.sh tools/lean-fmt)" "" \
        bash tools/lean-style.sh
}

lean_test() { (cd tool && lake test); }

# The shipped binary end to end: output streams + exit codes (docs/interface.md §1).
cli() { bash tests/cli/smoke.sh "$root/tool/.lake/build/bin/fvdep"; }

# Coverage ledger (docs/contracts/U2-core.md L1–L8): every claim's theorem type = its statement,
# axioms ⊆ std, root shape + call paths, compiled = checked, kernel replay (leanchecker), and
# docs/verification.md = the rendering. Verdict reused like a suite's in the fast gate (input
# closure = the tool package, the library, the doc + `.agent/spec.md`: `noCaller` names its rows).
# The checker loads `FvdepLedger.Rows` at run time (`lake exe` builds its own imports alone) ⇒ the
# rows' build first: a row edit or plant is checked as written, never a stale `.olean`.
coverage() {
    suite coverage "$(shipped_closure tool docs/verification.md .agent/spec.md)" "" \
        bash -c 'cd tool && lake build -q FvdepLedger && lake exe fvdep-ledger --check ../docs/verification.md'
}

# SHA-256 over the tracked + untracked-unignored files under PATH…, both Lake configs + toolchain
# pins: a suite's input closure (over-inclusive: a missed input would reuse a stale green).
closure_key() {
    git ls-files -co --exclude-standard -z -- "$@" tool/lakefile.lean tool/lake-manifest.json \
        tool/lean-toolchain lakefile.lean lake-manifest.json lean-toolchain |
        sort -z | xargs -0 sha256sum | sha256sum | cut -c1-64
}

# A blind suite with its input closure KEY: with FVDEP_REUSE=1 (the fast gate) a green verdict
# stands while that closure stays byte-identical; the full gate always runs it. NARROW = the
# caller's own narrowing value (one case or target): a narrowed run never vouches for the whole.
suite() { # NAME KEY NARROW CMD…
    local name="$1" key="$2" narrow="$3" mark=".gate/$1.green"
    shift 3
    if [[ "${FVDEP_REUSE:-0}" == 1 && -n "$key" && -f "$mark" && "$(cat "$mark")" == "$key" ]]; then
        printf '%s: input closure %s = the last green run: verdict reused\n' "$name" "${key:0:12}"
        return 0
    fi
    "$@" || return 1
    [[ -z "$narrow" && -n "$key" ]] || return 0
    mkdir -p .gate && printf '%s\n' "$key" >"$mark"
}

ledger_suite_key() {
    closure_key tool/FvdepLedger tool/FvdepLedger.lean tool/LedgerMain.lean \
        tool/FvdepLedgerFixtures tool/FvdepLedgerFixtures.lean tests/ledger
}

# The blind fixture suite (L9): the checker's planted breaches + clean controls; it grades the
# checker alone.
ledger_suite() {
    suite ledger-suite "$(ledger_suite_key)" "${FVDEP_LEDGER_ONLY:-}" bash tests/ledger/run.sh
}

# Shipped code the codec + manifest drivers build (the tool requires the root library by path).
shipped_closure() {
    closure_key "$@" tool/FvdepCore tool/FvdepCore.lean tool/FvdepIO tool/FvdepIO.lean c \
        vendor/hacl-star 'Fvdep*'
}

# The blind codec suite (tester-3; U3 J, H, D + S5): tests/codec/run.sh = the J/H/D cases through
# the codec driver + the S cases through the sanitized SHA-256 core; jq = the pinned one (its output
# bytes are the printer cases' second oracle).
codec_suite() {
    local jq key
    jq="$(pinned jq)" || return 1
    key="$({ shipped_closure tests/codec tests/sha256; awk '$1 == "jq"' tools/tools.lock; } |
        sha256sum | cut -c1-64)"
    suite codec-suite "$key" "${FVDEP_CODEC_CASE:-}" env PATH="${jq%/*}:$PATH" bash tests/codec/run.sh
}

# The blind manifest suite (tester-4; U3 T6): the reader, validator + printer through its driver.
manifest_suite() {
    suite manifest-suite "$(shipped_closure tests/manifest)" "${FVDEP_MANIFEST_CASE:-}" \
        bash tests/manifest/run.sh ${FVDEP_MANIFEST_CASE:+--case "$FVDEP_MANIFEST_CASE"}
}

# The blind library suite (tester-5; U4 A + B): the launch specs + the protocol codec through its
# Lean driver, `fvdep-dev oracle` through its CLI.
library_suite() {
    local key
    key="$(shipped_closure tests/library tool/FvdepDev tool/FvdepDev.lean tool/DevMain.lean)"
    suite library-suite "$key" "${FVDEP_LIBRARY_CASE:-}" bash tests/library/run.sh
}

# The blind index suite (tester-5 batch 2; U4 C): `fvdep index [--check]` through the built binary
# (fixture libraries, each built fresh; an LD_PRELOAD fault library) + `fvdep-dev index` (decode,
# history).
index_suite() {
    local key
    key="$(shipped_closure tests/index tool/FvdepDev tool/FvdepDev.lean tool/DevMain.lean tool/Main.lean)"
    suite index-suite "$key" "${FVDEP_INDEX_CASE:-}" bash tests/index/run.sh
}

# Fuzz corpora (contract U3 "Fuzz"; tools/fuzz.sh): every seed + pinned crash input through each
# target's engine-free replay build (a Lean target's panic aborts; C targets under gcc ASan + UBSan).
fuzz_replay() {
    suite fuzz-replay "$(shipped_closure tests/fuzz tool/FvdepFuzz tool/FvdepFuzz.lean tools/fuzz.sh)" \
        "${FVDEP_FUZZ_TARGET:-}" bash tools/fuzz.sh replay ${FVDEP_FUZZ_TARGET:+"$FVDEP_FUZZ_TARGET"}
}

# The blind persistence suite (tester-4; U3 F6): the shim + writer guard through the dev driver,
# an LD_PRELOAD fault library + sanitizer harnesses (tests/sys/build.sh); its ZFS case needs
# fvdep's dataset (a host without it reports that case SKIP: .claude/rules/checks.md).
sys_suite() {
    local key
    key="$(shipped_closure tests/sys tool/FvdepDev tool/FvdepDev.lean tool/DevMain.lean)"
    suite sys-suite "$key" "${FVDEP_SYS_CASE:-}" bash tests/sys/run.sh \
        ${FVDEP_SYS_CASE:+--case "$FVDEP_SYS_CASE"}
}

# Shipped code a sandbox suite's driver builds: the dev driver, the step helper, the runner + shim.
sandbox_closure() {
    shipped_closure "$@" tools/pidns-check.sh tool/FvdepDev tool/FvdepDev.lean tool/DevMain.lean \
        tool/StepMain.lean
}

# The blind sandbox suite's D2 + D3 cases (tester-6; U5 R + D2: `fvdep-dev sandbox run`, one step
# each: outcomes, pumps, frames, preflight; K + D3: `fvdep-dev cache`, fills, pins, eviction); its D1
# + D4 cases merge with U5-D. Its steps run fvdep-step ⇒ tests/sandbox/run.sh refuses outside a PID
# namespace of the job's own.
sandbox_suite() {
    local cases=(--case R. --case K. --case P. --case S. --case B.)
    [[ -z "${FVDEP_SANDBOX_CASE:-}" ]] || cases=(--case "$FVDEP_SANDBOX_CASE")
    suite sandbox-suite "$(sandbox_closure tests/sandbox)" "${FVDEP_SANDBOX_CASE:-}" \
        bash tests/sandbox/run.sh "${cases[@]}"
}

# The isolation cases (MAIN's; U5 G1, G3, G4 + R8's descriptor 4: D2 steps + the helper alone in a
# fresh bwrap namespace), each killed by a mutant of tests/isolation/mutants.py. Its steps run
# fvdep-step ⇒ tests/isolation/run.sh refuses outside a PID namespace of the job's own.
isolation() {
    suite isolation "$(sandbox_closure tests/isolation)" "${FVDEP_ISOLATION_CASE:-}" \
        bash tests/isolation/run.sh ${FVDEP_ISOLATION_CASE:+--case "$FVDEP_ISOLATION_CASE"}
}

# The blind acceptance suite (tester-1; Intent + Decisions + interface): the cases merged into the
# gate (MANIFEST status `merged`) through the built `fvdep`; the rest wait for their units.
acceptance() {
    suite acceptance "$(shipped_closure tests/acceptance tool/Main.lean)" \
        "${FVDEP_ACCEPTANCE_CASE:-}" env FVDEP_BIN="$root/tool/.lake/build/bin/fvdep" \
        python3 -I tests/acceptance/run.py --merged ${FVDEP_ACCEPTANCE_CASE:+-k "$FVDEP_ACCEPTANCE_CASE"}
}

# C7: the committed index.json = the bytes `fvdep index` makes of the library sources (a fresh
# snapshot build, its observations + the kernel replay; `--check` never writes); verdict reused like
# the suites'. Drift after a library change → regenerate: bash tools/update-index.sh (desktop).
index_key() { shipped_closure index.json tool/Main.lean; }
index() {
    suite index "$(index_key)" "" "$root/tool/.lake/build/bin/fvdep" index --check
}

# C7 + C9 `history`: the working tree's index.json against HEAD's + each of HEAD's parents' committed
# ones (no index.json in any of them ⇒ nothing to check); shallow → exit 2.
index_history() { "$root/tool/.lake/build/bin/fvdep-dev" index history "$root"; }

# Each purpose-built check passes on a clean copy, fails on its planted input, passes restored.
probes() { bash tools/gate-probe.sh && python3 tools/test-vflab-identity.py; }

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

# History + every tracked or untracked-unignored file; live validation stays off (no network). The
# files = one directory scan of a staged copy: betterleaks pays ≈ 20 ms per path argument (2,168
# paths: 47.7 s; the copy: 255 ms, the same 6,955,185 bytes).
secrets() {
    local rc=0 leaks files
    leaks="$(pinned betterleaks)" || return 1
    "$leaks" git --no-banner --no-color --redact --verbose . || rc=1
    files="$(mktemp -d)" || return 1
    { git ls-files -co --exclude-standard -z | tar --null -T - -cf - | tar -C "$files" -xf -; } &&
        (cd -- "$files" && "$leaks" dir --no-banner --no-color --redact --verbose .) || rc=1
    rm -rf -- "$files"
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

# Concurrent stages: FVDEP_GATE_JOBS, else the CPU count.
gate_jobs() { printf '%s' "${FVDEP_GATE_JOBS:-$(nproc)}"; }

# Memory budget (GiB) of concurrent stages: FVDEP_GATE_MEMORY, else 4/5 of the run's cap (its
# cgroup's memory.max, else MemTotal: vflab's unit cap 24G → 19, a 16 GB CI runner → 12).
gate_budget() {
    local cap max
    if [[ -n "${FVDEP_GATE_MEMORY:-}" ]]; then
        printf '%s' "$FVDEP_GATE_MEMORY"
        return
    fi
    cap="$(awk '$1 == "MemTotal:" { print $2 * 1024 }' /proc/meminfo)"
    max="$(cat "/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup 2>/dev/null)/memory.max" 2>/dev/null)"
    [[ "$max" =~ ^[0-9]+$ && $max -lt $cap ]] && cap=$max
    cap=$((cap * 4 / 5 / 1024 ** 3))
    printf '%d' $((cap > 0 ? cap : 1))
}

# Both run-phase knobs = positive integers (G1: else rc 2 before any stage; `pool` does arithmetic
# on them).
knobs_ok() {
    [[ "$(gate_jobs)" =~ ^[1-9][0-9]*$ && "$(gate_budget)" =~ ^[1-9][0-9]*$ ]] && return 0
    printf 'gate: FVDEP_GATE_JOBS + FVDEP_GATE_MEMORY (GiB) must be positive integers\n' >&2
    return 1
}

# STAGE… at once (G1; bash ≥ 5.1: `wait -n -p`): at most `gate_jobs` running, their weights
# (GATE_WEIGHTS) summed within `gate_budget` (a stage over it starts alone), started GATE_FIRST
# first, then in the given order, each started as soon as it fits; each stage's block, rc line +
# ledger row print in the given order once it + every earlier one has ended.
pool() {
    local names=("$@") todo=() next=() name w p rc used=0 shown=0 jobs budget out
    local -A weight=() pid=() began=() result=()
    jobs="$(gate_jobs)"
    budget="$(gate_budget)"
    for w in $GATE_WEIGHTS; do weight[${w%=*}]="${w#*=}"; done
    for name in $GATE_FIRST; do [[ " $* " == *" $name "* ]] && todo+=("$name"); done
    for name in "$@"; do [[ " $GATE_FIRST " == *" $name "* ]] || todo+=("$name"); done
    out="$(mktemp -d)" || return 1
    while [[ ${#todo[@]} -gt 0 || ${#pid[@]} -gt 0 ]]; do
        next=()
        for name in "${todo[@]}"; do
            w="${weight[$name]:-1}"
            if [[ ${#pid[@]} -eq 0 ]] || ((${#pid[@]} < jobs && used + w <= budget)); then
                began[$name]="$(stamp)"
                "${name//-/_}" >"$out/$name" 2>&1 &
                pid[$!]="$name"
                used=$((used + w))
            else
                next+=("$name")
            fi
        done
        todo=("${next[@]}")
        wait -n -p p
        rc=$?
        name="${pid[$p]}"
        unset "pid[$p]"
        used=$((used - ${weight[$name]:-1}))
        result[$name]="$rc $(elapsed "${began[$name]}")"
        while [[ $shown -lt ${#names[@]} && -n "${result[${names[shown]}]:-}" ]]; do
            name="${names[shown]}"
            printf '\n=== %s ===\n' "$name"
            cat -- "$out/$name"
            # shellcheck disable=SC2086  # "RC SECONDS" splits into report's two arguments
            report "$name" ${result[$name]}
            shown=$((shown + 1))
        done
    done
    rm -rf -- "$out"
}

# The selected stages in their phases (G1): the build phase (`tools`, `lean-build`) in order; then
# the rest at once (`pool`) — after a red build phase one at a time (a stage's own build of a
# shared package would race another's writes); `probes` after them (its copies reuse their fresh
# green marks), `tree-clean` last.
run_stages() {
    local name build=() rest=() last=()
    for name in "$@"; do
        case "$name" in
        tools | lean-build) build+=("$name") ;;
        probes | tree-clean) last+=("$name") ;;
        *) rest+=("$name") ;;
        esac
    done
    for name in "${build[@]}"; do stage "$name" "${name//-/_}"; done
    if [[ " ${failed[*]} " != *" tools "* && " ${failed[*]} " != *" lean-build "* ]]; then
        pool "${rest[@]}"
    else
        for name in "${rest[@]}"; do stage "$name" "${name//-/_}"; done
    fi
    for name in "${last[@]}"; do stage "$name" "${name//-/_}"; done
}

main() {
    local start shard="" rows row name shards selected=()
    registry_ok || exit 2
    if [[ $# -gt 0 ]]; then
        if [[ $# -ne 2 || "$1" != --shard ]] || ! shard_names | grep -x -F -- "$2" >/dev/null; then
            printf 'usage: tools/gate.sh [--shard %s]\n' "$(shard_names | paste -sd'|' -)" >&2
            exit 2
        fi
        shard="$2"
    fi
    knobs_ok || exit 2
    start="$(stamp)"
    if [[ -n "$shard" ]]; then ledger_begin "shard:$shard"; else ledger_begin gate; fi
    mapfile -t rows <<<"$STAGES"
    for row in "${rows[@]}"; do
        read -r name shards <<<"$row"
        if [[ -n "$name" && ( -z "$shard" || " $shards " == *" $shard "* ) ]]; then
            selected+=("$name")
        fi
    done
    run_stages "${selected[@]}"
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
