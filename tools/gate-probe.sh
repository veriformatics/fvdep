#!/usr/bin/env bash
# Probes every purpose-built check of the gate (gate stage `probes`; contract U1 P1): in a scratch
# copy of the worktree the check passes (control), fails once its bad input is planted — for the
# named cause, matched in its output — and passes again once the copy is restored byte for byte.
# A check that cannot fail and a clean tree print the same green. Run on vflab:
# tools/vflab-run bash tools/gate-probe.sh (tools/vflab-run's own behaviour is qualified from the
# desktop: tools/vflab-run-probe.sh). Prints one PROBE line each; exit status = probes that failed.
# Check + plant functions run indirectly, through probe().
# shellcheck disable=SC2329
set -uo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root" || exit 1

# A keyed stage (gate.sh `suite`) in a copy reuses the tree's green verdict for an identical input
# closure: control + restored = the tree's closure, so the planted run alone executes; a plant
# outside the stage's key would reuse a green there too, which fails the probe.
export FVDEP_REUSE=1

# lean-style probes share the gate tree's lean-fmt build (tools/lean-style.sh FVDEP_LEAN_FMT).
(cd tools/lean-fmt && lake build «lean-fmt» >/dev/null 2>&1) || {
    printf 'gate-probe: lean-fmt does not build\n' >&2
    exit 1
}
export FVDEP_LEAN_FMT="$root/tools/lean-fmt/.lake/packages/lean-fmt/.lake/build/bin/lean-fmt"

# Scratch copies live beside the tree (ignored .gate/), on its filesystem: the tool downloads are
# hardlinked into them, which fails across filesystems.
scratch="$(mktemp -d -p "$root/.gate" probe.XXXXXX 2>/dev/null || { mkdir -p "$root/.gate" && mktemp -d -p "$root/.gate" probe.XXXXXX; })"
export TMPDIR="$scratch"

# The tree's ignored directories a copy takes (no probe writes the tree's: each restore takes them
# afresh from there): pinned tools (binaries copied: probes corrupt them; downloads hardlinked: only
# ever replaced whole) so tool stages run offline; unless the probe runs no Lean (with_build=0: 750
# MB less per copy, measured), the Lake build caches so Lean plants rebuild incrementally — minus
# each `.lake/config` (Lake's elaborated lakefile: it bakes `__dir__`, so a copy would link the
# tree's files), which Lake re-elaborates in the copy; a suite probe (with_suites=1) also the test
# packages' builds, so its planted + restored runs rebuild incrementally.
taken() {
    local d
    for d in .tools/bin .tools/cache; do [[ -d "$root/$d" ]] && printf '%s\n' "$d"; done
    [[ "${with_build:-1}" == 1 ]] || return 0
    for d in .lake tool/.lake; do [[ -d "$root/$d" ]] && printf '%s\n' "$d"; done
    [[ "${with_suites:-0}" == 1 ]] || return 0
    for d in tests/codec/.lake tests/manifest/.lake tests/library/.lake tests/library/conformance/.lake \
        tests/sha256/.build tests/sys/.lake tests/sys/.build; do
        [[ -d "$root/$d" ]] && printf '%s\n' "$d"
    done
    return 0
}

# DIR's `taken` directories made the tree's, each `.lake/config` dropped: copied when absent (`cp`
# outpaces rsync on a first copy), else synced (a restore rewrites what the run changed alone).
take() { # DIR
    local d
    while read -r d; do
        if [[ ! -d "$1/$d" ]]; then
            mkdir -p "$(dirname -- "$1/$d")"
            if [[ "$d" == .tools/cache ]]; then cp -al "$root/$d" "$1/$d"; else cp -a "$root/$d" "$1/$d"; fi
            [[ "$d" != *.lake ]] || rm -rf "$1/$d/config"
        elif [[ "$d" == .tools/cache ]]; then
            rsync -a --delete --link-dest="$root/$d" "$root/$d/" "$1/$d/"
        elif [[ "$d" == *.lake ]]; then
            rsync -a --delete --exclude=/config --delete-excluded "$root/$d/" "$1/$d/"
        else
            rsync -a --delete "$root/$d/" "$1/$d/"
        fi
    done < <(taken)
}

# A git-tracked scratch copy of the worktree (the checks read `git ls-files`: `add -f` keeps the
# tracked files an ignore pattern matches, e.g. fixtures under a `.lake/`, so every closure key in a
# copy = the tree's) + its `taken` directories + the keyed stages' green marks (FVDEP_REUSE above).
copy() {
    local dir
    dir="$(mktemp -d)"
    git ls-files -co --exclude-standard -z | tar --null -T - -cf - | tar -C "$dir" -xf -
    git -C "$dir" init -q && git -C "$dir" add -A -f &&
        git -C "$dir" -c user.name=probe -c user.email=probe@invalid commit -q -m probe
    take "$dir"
    if compgen -G "$root/.gate/*.green" >/dev/null; then
        mkdir -p "$dir/.gate" && cp "$root"/.gate/*.green "$dir/.gate/"
    fi
    printf '%s' "$dir"
}

# probe NAME PLANT EXPECT CHECK… — CHECK passes on a fresh copy, fails after PLANT with EXPECT in
# its output, passes again after the copy is restored byte for byte (its own files + git from a
# pristine copy, its `taken` directories from the tree). `probe` queues; `launch` (after the last
# declaration) runs the queue in the background, at most $jobs at a time (each owns its copy),
# `first` before the rest: the stage lasts at least its longest probe, so a long one started late
# sets the tail (the index probes spread out: they share one lock). Results print in declaration
# order once all finish.
jobs=4
results="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
n=0
# Every line of an expectation names the planted run's cause (a combined plant: one line per check).
names_all() {
    local e
    while IFS= read -r e; do
        grep -q -F -- "$e" "$2" || return 1
    done <<<"$1"
}
run_probe() {
    local name="$1" plant="$2" expect="${3//$'\n'/ + }" lines="$3" dir pristine control planted
    local restored t took skip
    shift 3
    # Wall-clock per phase (whole seconds; this background subshell's own SECONDS).
    SECONDS=0
    t=()
    dir="$(copy)"
    pristine="$(mktemp -d)"
    mapfile -t skip < <(taken | sed 's|^|--exclude=/|')
    rsync -a "${skip[@]}" "$dir/" "$pristine/"
    t+=("$SECONDS")
    (cd -- "$dir" && "$@") >"$pristine.control" 2>&1
    control=$?
    t+=("$SECONDS")
    (cd -- "$dir" && "$plant") >/dev/null 2>&1
    (cd -- "$dir" && "$@") >"$pristine.planted" 2>&1
    planted=$?
    t+=("$SECONDS")
    # --ignore-times: rsync's quick check (size + mtime) keeps a planted file of the pristine size
    # written in the same second (a planted branch ref: the restored HEAD then named a deleted
    # commit), so every file is rewritten.
    rsync -a --delete --ignore-times "${skip[@]}" "$pristine/" "$dir/"
    take "$dir"
    (cd -- "$dir" && "$@") >"$pristine.restored" 2>&1
    restored=$?
    took="${SECONDS}s (copy ${t[0]}, control $((t[1] - t[0])), planted $((t[2] - t[1])), restored $((SECONDS - t[2])))"
    if [[ $control -eq 0 && $planted -ne 0 && $restored -eq 0 ]] &&
        names_all "$lines" "$pristine.planted"; then
        printf 'PROBE %s: fired (control 0, planted %d naming "%s", restored 0) %s\n' \
            "$name" "$planted" "$expect" "$took"
    else
        printf 'PROBE %s: FAILED (control %d, planted %d, restored %d; want 0, ≠0 naming "%s", 0) %s\n' \
            "$name" "$control" "$planted" "$restored" "$expect" "$took"
        sed 's/^/    control: /' "$pristine.control" | tail -n 10
        sed 's/^/    planted: /' "$pristine.planted" | tail -n 20
        sed 's/^/    restored: /' "$pristine.restored" | tail -n 10
        # a suite's failing cases sit far above its stage's tail: name them (a flake stays traceable)
        for run in control restored; do
            command grep -E '^FAIL ' "$pristine.$run" | head -n 8 | sed "s/^/    $run FAIL: /"
        done
    fi
    rm -rf -- "$dir" "$pristine" "$pristine".{control,planted,restored}
}
queued=()
suites_of=()
builds_of=()
probe() {
    # FVDEP_PROBE = a name prefix: a narrowed run queues the matching probes alone (iteration; the
    # gate's `probes` stage leaves it unset + runs every probe).
    [[ -z "${FVDEP_PROBE:-}" || "$1" == "$FVDEP_PROBE"* ]] || return 0
    n=$((n + 1))
    printf -v 'queued[n]' '%q ' "$@"
    suites_of[n]="${with_suites:-0}"
    builds_of[n]="${with_build:-1}"
}
# The coverage probes (≈ 5 GiB each: the checker loads the whole environment) alternate with
# lighter ones: four at once peak at the run's 24 GiB cap.
first=(coverage vendor-upstream coverage-extra-reach index-replay coverage-extra-root lean-fmt
    coverage-step lean-style coverage-step-binding sys-suite index-registry fast-gate cli
    index-drift manifest-suite codec-suite library-conformance)
launch() {
    local i name order=() seen=" "
    for name in "${first[@]}"; do
        for i in "${!queued[@]}"; do
            [[ "${queued[i]%% *}" == "$name" ]] && order+=("$i") && seen+="$i "
        done
    done
    for i in "${!queued[@]}"; do
        [[ "$seen" == *" $i "* ]] || order+=("$i")
    done
    for i in "${order[@]}"; do
        while [[ "$(jobs -rp | wc -l)" -ge $jobs ]]; do wait -n; done
        with_suites="${suites_of[i]}" with_build="${builds_of[i]}" eval "run_probe ${queued[i]}" \
            >"$results/$(printf '%03d' "$i")" 2>&1 &
    done
}

plant_marker() { touch .planted; }

# A gate main() over planted stages; `.planted` switches each scenario's bad case on.
run_main() { # STAGES-text FUNCTIONS-text ARGS…
    local stages="$1" fns="$2"
    shift 2
    bash -c 'source tools/gate.sh
STAGES="$1"
GATE_FIRST="" GATE_WEIGHTS=""
eval "$2"
shift 2
main "$@"' _ "$stages" "$fns" "$@" 2>&1
}

# G1: a failing stage among passing ones → every stage runs, rc 1, the failure named.
aggregate() {
    local out rc
    out="$(run_main $'\nok-stage probe\nmid-stage probe\nlate-stage probe\n' \
        'ok_stage() { return 0; }; mid_stage() { [[ ! -e .planted ]] || return 3; }; late_stage() { return 0; }' \
        --shard probe)"
    rc=$?
    printf '%s\n' "$out"
    [[ $rc -eq 0 ]] && return 0
    [[ $rc -eq 1 && "$out" == *"mid-stage rc=3"* && "$out" == *"late-stage rc=0"* &&
        "$out" == *"FAILED: mid-stage"* && "$out" == *"gate rc=1"* ]] && return 1
    return 0
}
with_build=0 probe gate-aggregate plant_marker "FAILED: mid-stage" aggregate

# G1: a stage that exits its process cannot end the run; several failures are all named.
exits() {
    local out rc
    out="$(run_main $'\nfirst probe\nleaver probe\nsecond probe\nlast probe\n' \
        'first() { [[ ! -e .planted ]] || return 4; }; leaver() { [[ ! -e .planted ]] || exit 9; }; second() { return 0; }; last() { [[ ! -e .planted ]] || return 5; }' \
        --shard probe)"
    rc=$?
    printf '%s\n' "$out"
    [[ $rc -eq 0 ]] && return 0
    [[ $rc -eq 1 && "$out" == *"leaver rc=9"* && "$out" == *"second rc=0"* &&
        "$out" == *"FAILED: first leaver last"* ]] && return 1
    return 0
}
with_build=0 probe gate-stage-exit plant_marker "FAILED: first leaver last" exits

# G1/G2: an invalid registry (undefined function, duplicate, shardless) fails before any stage
# runs, rc 2.
registry() {
    local out rc stages=$'\nok-stage probe\n'
    if [[ -e .planted ]]; then
        stages=$'\nok-stage probe\nghost-stage probe\nok-stage probe\nlonely\n'
    fi
    out="$(run_main "$stages" 'ok_stage() { return 0; }; lonely() { return 0; }')"
    rc=$?
    printf '%s\n' "$out"
    [[ $rc -eq 0 ]] && return 0
    [[ $rc -eq 2 && "$out" != *"=== "* ]] && return 2
    return 0
}
with_build=0 probe gate-registry plant_marker "has no function ghost_stage" registry

# G1: a run-phase knob naming no stage or a weight that is no whole GiB fails before any stage
# runs, rc 2.
weights() {
    local out rc knobs='GATE_FIRST=ok-stage GATE_WEIGHTS=ok-stage=2'
    [[ -e .planted ]] && knobs='GATE_FIRST=ghost-stage GATE_WEIGHTS="ghost-stage=2 ok-stage=0"'
    out="$(run_main $'\nok-stage probe\n' "ok_stage() { return 0; }; $knobs" --shard probe)"
    rc=$?
    printf '%s\n' "$out"
    [[ $rc -eq 0 ]] && return 0
    [[ $rc -eq 2 && "$out" != *"=== "* && "$out" == *"GATE_FIRST names no stage ghost-stage"* &&
        "$out" == *"entry ok-stage=0 is not"* ]] && return 2
    return 0
}
with_build=0 probe gate-weights plant_marker "GATE_WEIGHTS entry ghost-stage=2 is not <stage>=<GiB>" weights

# G1: a run-phase knob that is not a positive integer (stages at once, memory GiB) fails before any
# stage runs, rc 2 (control: both set).
knobs() {
    local out rc knobs='FVDEP_GATE_JOBS=2 FVDEP_GATE_MEMORY=1'
    [[ -e .planted ]] && knobs='FVDEP_GATE_JOBS=0 FVDEP_GATE_MEMORY=1'
    out="$(run_main $'\nok-stage probe\n' "ok_stage() { return 0; }; $knobs" --shard probe)"
    rc=$?
    printf '%s\n' "$out"
    [[ $rc -eq 0 ]] && return 0
    [[ $rc -eq 2 && "$out" != *"=== "* ]] && return 2
    return 0
}
with_build=0 probe gate-knobs plant_marker "FVDEP_GATE_JOBS + FVDEP_GATE_MEMORY (GiB) must be positive integers" knobs

# G2: an unknown shard → rc 2, no stage runs (control: a real shard).
usage() {
    local out rc shard=probe
    [[ -e .planted ]] && shard=nonesuch
    out="$(run_main $'\nok-stage probe\n' 'ok_stage() { return 0; }' --shard "$shard")"
    rc=$?
    printf '%s\n' "$out"
    [[ $rc -eq 0 ]] && return 0
    [[ $rc -eq 2 && "$out" != *"=== "* ]] && return 2
    return 0
}
with_build=0 probe gate-usage plant_marker "usage: tools/gate.sh" usage

# G5: each stage's verdict + wall-clock lands in the step ledger as it ends (a red row
# `unclassified`; tree = the graded file set, an untracked file included); an unwritable ledger
# fails the run, named.
plant_ledger() { rm -rf .gate && mkdir -p .gate/ledger.tsv; }
ledger_rows() {
    local out rc tree want
    printf 'untracked\n' >probe-untracked
    out="$(run_main $'\nok-stage probe\nred-stage probe\n' \
        'ok_stage() { return 0; }; red_stage() { return 3; }' --shard probe)"
    rc=$?
    printf '%s\n' "$out"
    git add -A && tree="$(git write-tree)" || return 1
    want="$tree"$'\tshard:probe\tok-stage\tgreen\t-\n'"$tree"$'\tshard:probe\tred-stage\tred\tunclassified'
    [[ $rc -eq 1 && "$out" == *"FAILED: red-stage"* && "$out" != *ledger* &&
        "$tree" != "$(git rev-parse 'HEAD^{tree}')" &&
        "$(head -n 1 .gate/ledger.tsv)" == $'date\ttree\tkind\tstep\tseconds\tverdict\tclass' &&
        "$(tail -n +2 .gate/ledger.tsv | cut -f2-4,6,7)" == "$want" ]] &&
        awk -F'\t' 'NR > 1 && !(NF == 7 && $1 ~ /^[0-9-]+T[0-9:]+Z$/ && $5 ~ /^[0-9]+\.[0-9]$/) {
            bad = 1 } END { exit bad }' .gate/ledger.tsv
}
with_build=0 probe gate-ledger plant_ledger "ledger: cannot append" ledger_rows

# tree-clean: a stage that writes into the graded file set fails the run, the file named; a stage
# writing an ignored path does not.
tree_written() {
    run_main $'\nwriter probe\ntree-clean probe\n' \
        'writer() { mkdir -p .gate; printf x >.gate/ignored-output; [[ ! -e .planted ]] || printf x >probe-written.txt; }' \
        --shard probe
}
with_build=0 probe tree-clean plant_marker "probe-written.txt" tree_written

# G3: a stage whose pinned tool has no lock line fails; a changed cached tool binary is not used:
# fetch-tools reinstalls it from the verified download (the planted case fails if corrupt bytes
# survive).
shell_stage() { bash -c 'source tools/gate.sh; shell'; }
plant_no_shellcheck() { sed -i '/^shellcheck /d' tools/tools.lock; }
with_build=0 probe gate-missing-tool plant_no_shellcheck "no pinned tool matches linux-x86_64 shellcheck" shell_stage
cached_tool() {
    local before after recorded
    bash tools/fetch-tools.sh zizmor >/dev/null || return 1
    if [[ -e .planted ]]; then
        printf 'corrupt' >>.tools/bin/zizmor
        before="$(sha256sum .tools/bin/zizmor | cut -d' ' -f1)"
        bash tools/fetch-tools.sh zizmor >/dev/null || return 1
        after="$(sha256sum .tools/bin/zizmor | cut -d' ' -f1)"
        recorded="$(awk '{ print $3 }' .tools/bin/.zizmor.stamp)"
        if [[ "$after" != "$before" && "$after" == "$recorded" ]]; then
            printf 'corrupt cached binary replaced\n'
            return 1
        fi
    fi
    return 0
}
with_build=0 probe tool-identity plant_marker "corrupt cached binary replaced" cached_tool
# shellcheck disable=SC2016  # the planted script's `$1` is literal on purpose
plant_shell() { printf '#!/usr/bin/env bash\necho $1\n' >tools/probe-unquoted.sh; }
with_build=0 probe shellcheck plant_shell "SC2086" shell_stage

# python: both pinned scanners fire inside unannotated helpers; a missing config stays red.
python_stage() { bash -c 'source tools/gate.sh; python'; }
plant_python_lint() {
    printf 'def lint_probe():\n    return ruff_probe_missing_name\n' >tools/python-probe.py
}
plant_python_type() {
    printf 'import importlib.util\ndef type_probe():\n    spec = importlib.util.spec_from_file_location("probe", "probe.py")\n    return spec.loader\n' >tools/python-probe.py
}
plant_python_warning() {
    printf 'def warning_probe():\n    try:\n        int("invalid")\n    except (ValueError, UnicodeError):\n        pass\n' >tools/python-probe.py
}
plant_python_config() { plant_python_type; rm pyrefly.toml; }
plant_python_ruff_missing() { sed -i '/^ruff /d' tools/tools.lock; }
plant_python_pyrefly_missing() { sed -i '/^pyrefly /d' tools/tools.lock; }
with_build=0 probe python-ruff plant_python_lint "F821" python_stage
with_build=0 probe python-pyrefly plant_python_type "[missing-attribute]" python_stage
with_build=0 probe python-warning plant_python_warning "[unreachable-except-clause]" python_stage
with_build=0 probe python-config plant_python_config "pyrefly.toml" python_stage
with_build=0 probe python-ruff-missing plant_python_ruff_missing "no pinned tool matches linux-x86_64 ruff" python_stage
with_build=0 probe python-pyrefly-missing plant_python_pyrefly_missing "no pinned tool matches linux-x86_64 pyrefly" python_stage

# secrets: a planted credential-shaped token in an untracked file.
secrets_stage() { bash -c 'source tools/gate.sh; secrets'; }
# The token is derived at run time: a literal here would itself be a finding in this script.
plant_secret() {
    printf 'token = "ghp_%s"\n' "$(printf probe | sha256sum | head -c 36)" >probe-config.toml
}
with_build=0 probe secrets plant_secret "probe-config.toml" secrets_stage

# vulns: an unlisted lockfile; a listed lockfile that does not exist; a listed lockfile pinning a
# package with published advisories (osv.dev).
vulns_stage() { bash -c 'source tools/gate.sh; vulns'; }
plant_unlisted() { mkdir -p probe && printf '# probe\n' >probe/Cargo.lock; }
plant_missing() { printf 'probe/uv.lock\n' >>tools/lockfiles.txt; }
plant_vulnerable() {
    mkdir -p probe
    cat >probe/package-lock.json <<'JSON'
{
  "name": "probe",
  "version": "1.0.0",
  "lockfileVersion": 3,
  "requires": true,
  "packages": {
    "": { "name": "probe", "version": "1.0.0", "dependencies": { "lodash": "4.17.15" } },
    "node_modules/lodash": {
      "version": "4.17.15",
      "resolved": "https://registry.npmjs.org/lodash/-/lodash-4.17.15.tgz",
      "integrity": "sha512-8xOcRHvCjnocdS5cpwXQXVzmmh5e5+saE2QGoeQmbKmRS6J3VQppPOIt0MpmE+O2jZlvQ+dANzPyUFWSjw+B54ug=="
    }
  }
}
JSON
    printf 'probe/package-lock.json\n' >>tools/lockfiles.txt
}
with_build=0 probe vulns-unlisted plant_unlisted "probe/Cargo.lock: lockfile not listed" vulns_stage
with_build=0 probe vulns-missing plant_missing "probe/uv.lock does not exist" vulns_stage
with_build=0 probe vulns-advisory plant_vulnerable "lodash" vulns_stage
# A vendored commit OSV lists as affected (libxml2 6c128fd5, OSS-Fuzz git ranges).
plant_vendor_vulnerable() {
    sed -i 's/"commit": "f557259007db9933442dde10aa995c1b00bd3446"/"commit": "6c128fd58a0e4641c23a345d413672494622db1b"/' \
        vendor/hacl-star/lock.json
}
with_build=0 probe vulns-vendor plant_vendor_vulnerable "OSV lists" vulns_stage

# workflows: zizmor + actionlint each fire on a planted defect.
workflows_stage() { bash -c 'source tools/gate.sh; workflows'; }
plant_zizmor() { sed -i '/^          persist-credentials: false$/d' .github/workflows/gate.yml; }
plant_actionlint() { sed -i 's/^    runs-on: ubuntu-26.04$/    runs-on: ubuntu-26.04\n    timeout-minutes: soon/' .github/workflows/codeql.yml; }
with_build=0 probe workflows-zizmor plant_zizmor "artipacked" workflows_stage
with_build=0 probe workflows-actionlint plant_actionlint "timeout-minutes" workflows_stage

# imports: a library module importing `Lean`; a tool module importing a foreign package; preview:
# a library module importing the preview tree.
plant_lib_import() { sed -i '1i import Lean' Fvdep/Version.lean; }
plant_tool_import() { sed -i '1i import Mathlib' tool/FvdepCore/Cli.lean; }
plant_preview() { sed -i '1i import FvdepPreview' Fvdep.lean; }
with_build=0 probe imports-library plant_lib_import "Fvdep/Version.lean:1: import Lean" bash tools/check-imports.sh imports
with_build=0 probe imports-tool plant_tool_import "tool/FvdepCore/Cli.lean:1: import Mathlib" bash tools/check-imports.sh imports
# The audit tree reaches the build through the ledger alone: a shipped module + the test driver
# importing it.
plant_audit_shipped() { sed -i '1i import FvdepAudit.Json.Spec' tool/FvdepCore/Json.lean; }
plant_audit_test() { sed -i '1i import FvdepAudit.Json.Spec' tool/Tests.lean; }
with_build=0 probe imports-audit-shipped plant_audit_shipped "tool/FvdepCore/Json.lean:1: import FvdepAudit.Json.Spec" \
    bash tools/check-imports.sh imports
with_build=0 probe imports-audit-test plant_audit_test "tool/Tests.lean:1: import FvdepAudit.Json.Spec" \
    bash tools/check-imports.sh imports
# The dev driver library (U3 F6) never enters a shipped module.
plant_dev_shipped() { sed -i '1i import FvdepDev.Sys' tool/FvdepIO/Run.lean; }
with_build=0 probe imports-dev-shipped plant_dev_shipped "tool/FvdepIO/Run.lean:1: import FvdepDev.Sys" \
    bash tools/check-imports.sh imports
with_build=0 probe preview plant_preview "Fvdep.lean:1: import FvdepPreview" bash tools/check-imports.sh preview
# A module whose name only starts like an allowed root (the `\.`-in-awk-v regression).
plant_prefix() { sed -i '1i import FvdepPlanted' FvdepPreview.lean; }
with_build=0 probe imports-prefix plant_prefix "FvdepPreview.lean:1: import FvdepPlanted" bash tools/check-imports.sh imports
plant_preview_proofs() { sed -i '1i import FvdepProofs' FvdepPreview.lean; }
with_build=0 probe imports-preview-proofs plant_preview_proofs "FvdepPreview.lean:1: import FvdepProofs" \
    bash tools/check-imports.sh imports
plant_proofs_outside() { sed -i '1i import Mathlib' FvdepProofs.lean; }
with_build=0 probe imports-proofs plant_proofs_outside "FvdepProofs.lean:1: import Mathlib" \
    bash tools/check-imports.sh imports

# lean-style: a tab in a Lean source; a misformatted declaration lean-fmt would rewrite.
plant_tab() { printf '\t-- tab\n' >>Fvdep/Version.lean; }
plant_misformat() { printf '\ndef probeFormat(x:Nat):Nat:=x+1\n' >>Fvdep/Version.lean; }
lean_style_stage() { bash -c 'source tools/gate.sh; lean_style'; }
probe lean-style plant_tab ": tab" lean_style_stage
probe lean-fmt plant_misformat "Version.lean" lean_style_stage

# fanout: a missing shard; a disabled gate step; a masked one; SHARD unbound; fail-fast on.
fanout_stage() { bash -c 'source tools/gate.sh; fanout'; }
plant_matrix() { sed -i 's/^\( *shard: \)\[lean, suites, checks\]$/\1[lean, checks]/' .github/workflows/gate.yml; }
with_build=0 probe fanout-shards plant_matrix "matrix shards" fanout_stage
plant_disabled() {
    sed -i 's/^\(      - name: Run the gate shard\)$/\1\n        if: false/' .github/workflows/gate.yml
}
with_build=0 probe fanout-disabled plant_disabled "unconditional, unmasked" fanout_stage
plant_masked() {
    sed -i 's/^\(      - name: Run the gate shard\)$/\1\n        continue-on-error: true/' .github/workflows/gate.yml
}
with_build=0 probe fanout-masked plant_masked "unconditional, unmasked" fanout_stage
plant_unbound() { sed -i '/^      SHARD: \${{ matrix.shard }}$/d' .github/workflows/gate.yml; }
with_build=0 probe fanout-unbound plant_unbound "SHARD bound" fanout_stage
plant_failfast() { sed -i 's/^      fail-fast: false$/      fail-fast: true/' .github/workflows/gate.yml; }
with_build=0 probe fanout-failfast plant_failfast "fail-fast false" fanout_stage
# fanout, job `probes`: its probes step removed → the job no longer runs the probes shard.
plant_probes_job() { sed -i '/^        run: bash tools\/gate.sh --shard probes$/d' .github/workflows/gate.yml; }
with_build=0 probe fanout-probes-job plant_probes_job "job probes needs gate" fanout_stage

# marks: a keyed stage's green mark from another input closure → `marks` refuses it, named (the
# probes job's input: the run shards' marks).
plant_stale_mark() { printf 'stale\n' >.gate/index.green; }
with_build=0 probe marks plant_stale_mark "marks: index holds a mark of another input closure" \
    bash -c 'source tools/gate.sh; marks'

# deps: a pinned tool without a dependency-table row.
plant_tool() {
    printf 'planted 1.0.0 linux-x86_64 %064d https://github.com/planted/planted/releases/download/v1.0.0/planted.tar.gz\n' 0 \
        >>tools/tools.lock
}
with_build=0 probe deps plant_tool "planted has no row" python3 -I tools/check-deps.py
plant_vendor_upstream() {
    sed -i 's#"upstream": "https://github.com/hacl-star/hacl-star"#"upstream": "https://github.com/planted/vendored"#' \
        vendor/hacl-star/lock.json
}
with_build=0 probe deps-vendor plant_vendor_upstream "planted/vendored has no row" python3 -I tools/check-deps.py
plant_afl_upstream() { sed -i 's#github.com/AFLplusplus/AFLplusplus/#github.com/planted/fuzzer/#' tools/afl.lock; }
with_build=0 probe deps-afl plant_afl_upstream "planted/fuzzer has no row" python3 -I tools/check-deps.py

# vendor: one changed byte, a locked file missing, an unlocked file beside the locked ones.
vendor_stage() { bash -c 'source tools/gate.sh; vendor'; }
plant_vendor_byte() { printf 'x' >>vendor/hacl-star/dist/gcc-compatible/Hacl_Hash_SHA2.h; }
plant_vendor_missing() { rm vendor/hacl-star/dist/LICENSE.txt; }
plant_vendor_extra() { printf 'int planted;\n' >vendor/hacl-star/dist/gcc-compatible/planted.c; }
with_build=0 probe vendor-byte plant_vendor_byte "Hacl_Hash_SHA2.h sha256 differs" vendor_stage
with_build=0 probe vendor-missing plant_vendor_missing "dist/LICENSE.txt missing" vendor_stage
with_build=0 probe vendor-extra plant_vendor_extra "planted.c not in" vendor_stage
# vendor-upstream: a commit-only bump to d826c0c9 (its Hacl_Hash_SHA2.c predates the locked one).
plant_vendor_commit() {
    sed -i 's/"commit": "f557259007db9933442dde10aa995c1b00bd3446"/"commit": "d826c0c9fb494f9476aa3449d7a62412fb5be7d6"/' \
        vendor/hacl-star/lock.json
}
with_build=0 probe vendor-upstream plant_vendor_commit "no longer yields the locked bytes" \
    bash -c 'source tools/gate.sh; vendor_upstream'

# renovate: a manager that stops matching; a half-applied version bump; a greedy Lake manager that
# fuses two packages into one match (the two-package fixture catches it).
plant_manager() { sed -i 's/leanprover\/lean4:v(?<currentValue>/leanprover\/lean5:v(?<currentValue>/' renovate.json; }
with_build=0 probe renovate-extract plant_manager "lean-toolchain: extracted" python3 -I tools/check-renovate.py
plant_halfbump() { sed -i 's/^\(zizmor\) \([0-9.]*\) /\1 99.0.0 /' tools/tools.lock; }
with_build=0 probe renovate-repin plant_halfbump "re-pin with tools/pin-tool.sh zizmor 99.0.0" \
    python3 -I tools/check-renovate.py
plant_lake_manager() { sed -i 's/\*?\\"name\\"/*\\"name\\"/' renovate.json; }
with_build=0 probe renovate-lake plant_lake_manager "tests/renovate/lake-manifest.json: extracted" \
    python3 -I tools/check-renovate.py
plant_vendor_manager() { sed -i 's/\\"commit\\"/\\"comit\\"/' renovate.json; }
with_build=0 probe renovate-vendor plant_vendor_manager "vendor/hacl-star/lock.json: extracted" \
    python3 -I tools/check-renovate.py
plant_afl_manager() { sed -i 's/) source /) sauce /' renovate.json; }
with_build=0 probe renovate-afl plant_afl_manager "tools/afl.lock: extracted" python3 -I tools/check-renovate.py
plant_afl_halfbump() { sed -i -E 's/^(\S+) \S+ source /\1 9.99c source /' tools/afl.lock; }
with_build=0 probe renovate-afl-repin plant_afl_halfbump "re-pin with tools/fuzz.sh pin 9.99c" \
    python3 -I tools/check-renovate.py

# meta: version disagreement; an unquoted rule `paths:` entry; a Lake target the gate never builds;
# the library's option list differing between the root lakefile + `FvdepCore.Build`.
meta_stage() { bash -c 'source tools/gate.sh; meta'; }
plant_version() {
    sed -i 's/^def version : String := ".*"$/def version : String := "9.9.9"/' Fvdep/Version.lean
}
with_build=0 probe meta-version plant_version 'version "9.9.9" !=' meta_stage
plant_rule() {
    mkdir -p .claude/rules
    printf -- '---\npaths:\n  - Fvdep/**\n---\n\n# planted\n' >.claude/rules/planted.md
}
with_build=0 probe meta-frontmatter plant_rule "paths entry is not a quoted glob" meta_stage
plant_target() { printf '\nlean_lib FvdepPlanted\n' >>lakefile.lean; }
with_build=0 probe meta-targets plant_target "FvdepPlanted" meta_stage
plant_options() { sed -i 's/, ("warningAsError", "true")//' tool/FvdepCore/Build.lean; }
with_build=0 probe meta-options plant_options "!= FvdepCore.Build.libraryOptions" meta_stage

# spec: a spec missing its Phase section.
plant_spec() { sed -i '/^## Phase/,$d' .agent/spec.md; }
with_build=0 probe spec plant_spec "spec-lint:" bash -c 'source tools/gate.sh; spec'

# coverage: docs/verification.md one byte off the ledger's rendering → the `doc` finding.
plant_doc_drift() { sed -i '1s/^/x/' docs/verification.md; }
probe coverage plant_doc_drift "ledger: root: doc:" bash -c 'source tools/gate.sh; coverage'

# coverage, U6 Q2's freeze: a table atom added under the same profile id → the `freeze` finding.
plant_freeze() {
    sed -i 's/rule "Lean.Parser.Command.open" \["open"\],/rule "Lean.Parser.Command.open" ["open", "probe"],/' \
        tool/FvdepCore/Profile/Table.lean
    # U7 V3 (one coverage run, both freezes): a K2 text drifts under the verification profile's id
    sed -i 's/^def nanodaReject : String := "Error: export file declares unpermitted axiom"$/def nanodaReject : String := "Error: export file declares unpermitted axiom!"/' \
        tool/FvdepCore/Judge/Kernel.lean
}
probe coverage-freeze plant_freeze $'ledger: profile: freeze:\nledger: verification: freeze:' \
    bash -c 'source tools/gate.sh; coverage'

# coverage, extra roots: a further executable's entry not shaped `fun a => interpreter (plan a)`
# (one root per shipped executable, U2 L1 + L4; the helper's root bent to `Cli.plan`) → the `root`
# finding naming it.
# shellcheck disable=SC2016  # Lean's double-backtick names are literal on purpose
plant_extra_root() {
    sed -i 's/^      \[{  main := ``FvdepIO.Step.main$/      [{  main := ``Cli.plan/' \
        tool/FvdepLedger/Rows.lean
}
probe coverage-extra-root plant_extra_root 'FvdepCore.Cli.plan is not `fun a =>' \
    bash -c 'source tools/gate.sh; coverage'

# coverage, extra roots' reach: a definition an extra root alone reaches, outside every row's
# subject (U2 L2 over every root) → the `uncovered` finding naming it.
# shellcheck disable=SC2016  # Lean's double-backtick names are literal on purpose
plant_extra_reach() {
    printf '\n%s\n\n%s\n' 'def probePlan (args : List String) := FvdepCore.Cli.plan ("probe" :: args)' \
        'def probeMain (args : List String) : IO UInt32 := FvdepIO.execute (probePlan args)' \
        >>tool/Main.lean
    sed -i 's/^          plan := ``FvdepIO.Parse.plan }]$/          plan := ``FvdepIO.Parse.plan },\n        { main := ``probeMain, interpreter := ``FvdepIO.execute, plan := ``probePlan }]/' \
        tool/FvdepLedger/Rows.lean
}
probe coverage-extra-reach plant_extra_reach 'uncovered: probePlan: reachable' \
    bash -c 'source tools/gate.sh; coverage'

# coverage, sandbox steps (U2 L1 + L2 + L4: a step's program = shipped source), one plant per check,
# combined into two probes (each coverage run = the checker's ≈ 5 GiB environment + the replay: one
# probe per check took CI's lean shard past 40 min): an instance of a step's class outside every row
# (the `Int` conversions' row dropped) → `uncovered`; a listed class that is no class of the step's
# modules → `step`; `noCaller "step"` on a subject outside every step's reach → `nocaller`; `call` =
# the function itself (not the driver's definition naming it) → `step`; then a driver no root
# reaches + `embedded` of another type → `step` each (an `embedded` that does not decode leaves the
# module checks unrun: `call` stays in the first group).
# shellcheck disable=SC2016  # Lean's double-backtick names are literal on purpose
plant_step_instance() {
    # The row's name wherever the formatter breaks the list's lines (a line-start anchor moves
    # with every row added before it).
    perl -0pi -e 's/\bwireNativeIntRow,\s+//' tool/FvdepLedger/Rows.lean
}
# shellcheck disable=SC2016
plant_step_driver() {
    sed -i 's/^      \[{  driver := ``FvdepCore.Oracle.Driver.driverText$/      [{  driver := ``FvdepCore.Oracle.Wire.decodeArgs/' \
        tool/FvdepLedger/Rows.lean
}
# shellcheck disable=SC2016
plant_step_class() {
    sed -i 's/^            \[``FvdepCore.Oracle.Wire.Native, /            [``FvdepCore.Protocol.Val, ``FvdepCore.Oracle.Wire.Native, /' \
        tool/FvdepLedger/Rows.lean
}
# shellcheck disable=SC2016
plant_step_nocaller() {
    perl -0pi -e 's/(subject := ``FvdepCore\.Oracle\.Driver\.driverText\n    path := \[\]\n    noCaller := )"support"/$1"step"/' \
        tool/FvdepLedger/Rows.lean
}

# shellcheck disable=SC2016
plant_step_embedded() {
    sed -i 's/^          embedded := ``FvdepCore.Oracle.Driver.embedded$/          embedded := ``FvdepCore.Oracle.Driver.typesText/' \
        tool/FvdepLedger/Rows.lean
}
# shellcheck disable=SC2016
plant_step_call() {
    sed -i 's/^          call := ``FvdepCore.Oracle.Driver.call$/          call := ``FvdepCore.Oracle.Wire.answer/' \
        tool/FvdepLedger/Rows.lean
}
plant_step() { plant_step_instance && plant_step_class && plant_step_nocaller && plant_step_call; }
probe coverage-step plant_step $'uncovered: FvdepCore.Oracle.Wire.intNative: reachable\nFvdepCore.Protocol.Val: no class of the step\'s modules\nstep: FvdepCore.Oracle.Driver.driverText inside no step\'s modules\nFvdepCore.Oracle.Driver.driverText never reads FvdepCore.Oracle.Wire.answer' \
    bash -c 'source tools/gate.sh; coverage'
plant_step_binding() { plant_step_driver && plant_step_embedded; }
probe coverage-step-binding plant_step_binding $'FvdepCore.Oracle.Wire.decodeArgs: no root reaches the step\'s driver\nFvdepCore.Oracle.Driver.typesText: not a List (Lean.Name × String) definition' \
    bash -c 'source tools/gate.sh; coverage'

# ledger-suite: a negative case whose expected rc is flipped fails the suite, named (one case).
plant_case_flip() {
    awk -F'\t' -v OFS='\t' '$1 == "T5" { $4 = 0 } 1' tests/ledger/cases.tsv >cases.tmp &&
        mv cases.tmp tests/ledger/cases.tsv
}
probe ledger-suite plant_case_flip "FAIL T5" \
    env FVDEP_LEDGER_ONLY=T5 bash -c 'source tools/gate.sh; ledger_suite'

# codec-suite + manifest-suite: a driver harness answering one case wrong fails it, named (stage
# function, one case; codec's S cases run whole).
plant_codec_harness() { sed -i 's/toString maxDepth$/toString (maxDepth + 1)/' tests/codec/CodecHarness.lean; }
with_suites=1 probe codec-suite plant_codec_harness "FAIL J.limits" \
    env FVDEP_CODEC_CASE=J.limits bash -c 'source tools/gate.sh; codec_suite'
plant_manifest_driver() { sed -i 's/toJson maxBytes)\]$/toJson (maxBytes + 1))]/' tests/manifest/Driver.lean; }
with_suites=1 probe manifest-suite plant_manifest_driver "FAIL T.maxBytes" \
    env FVDEP_MANIFEST_CASE=T.maxBytes bash -c 'source tools/gate.sh; manifest_suite'

# library-suite: its reference encoder dropping the padding fails the 1-byte encodings, named (the
# RFC 4648 vectors are literals: a reference plant reaches the exhaustive + generated cases alone).
plant_library_reference() {
    sed -i 's/^    chars += \["="\] \* ((-len(chars)) % 4)$/    chars += []/' tests/library/reference.py
}
with_suites=1 probe library-suite plant_library_reference "FAIL A.b64.exhaustive.1.encode" \
    env FVDEP_LIBRARY_CASE=A.b64.exhaustive.1.encode bash -c 'source tools/gate.sh; library_suite'

# library-suite's conformance trial (contract U4 A8): an axiom in a trial proof fails its build
# (Conformance.Audit), named.
plant_conformance_axiom() {
    sed -i 's/^  funext encode_list$/  (fun _ => funext encode_list) trialPlant/
s/^theorem encode_eq /axiom trialPlant : True\n\n&/' \
        tests/library/conformance/Conformance/Proof/Encode.lean
}
with_suites=1 probe library-conformance plant_conformance_axiom "encode_eq rests on" \
    env FVDEP_LIBRARY_CASE=A.b64.vector.0.std.encode bash -c 'source tools/gate.sh; library_suite'

# index-suite: a decode case expecting a refusal of a valid index fails, named (one dev-driver case:
# no fixture library is built).
plant_index_case() {
    sed -i 's/^    case("roundtrip.full", base)$/    case("roundtrip.full", base, "planted")/' \
        tests/index/driver_cases.py
}
with_suites=1 probe index-suite plant_index_case "FAIL C11.roundtrip.full" \
    env FVDEP_INDEX_CASE=C11.roundtrip.full bash -c 'source tools/gate.sh; index_suite'

# fuzz-replay: the json target panics on one committed input ⇒ the replay aborts naming it (the
# harness's LEAN_ABORT_ON_PANIC turns a Lean panic into the abort the engine counts).
plant_fuzz_panic() {
    sed -i 's/^  | .ok v =>$/  | .ok v => if v == .str "fvdep-probe" then panic! "planted" else/' \
        tool/FvdepFuzz/Json.lean
    printf '"fvdep-probe"' >tests/fuzz/json-decode/probe-planted
}
probe fuzz-replay plant_fuzz_panic "probe-planted" \
    env FVDEP_FUZZ_TARGET=json-decode bash -c 'source tools/gate.sh; fuzz_replay'

# sys-suite: the dev driver naming one op's record wrong fails that op's records case, named.
plant_sys_driver() { sed -i 's/report "syncdir"/report "syncDir"/' tool/FvdepDev/Sys.lean; }
with_suites=1 probe sys-suite plant_sys_driver "FAIL F.records.syncdir" \
    env FVDEP_SYS_CASE=F.records.syncdir bash -c 'source tools/gate.sh; sys_suite'

# sandbox-suite: a D2 case expecting another code for a child's SIGTERM fails, named (one case).
plant_sandbox_case() {
    sed -i 's/signal.SIGTERM)"), "exited 143")/signal.SIGTERM)"), "exited 144")/' tests/sandbox/run.py
}
probe sandbox-suite plant_sandbox_case "FAIL R.signal" \
    env FVDEP_SANDBOX_CASE=R.signal bash -c 'source tools/gate.sh; sandbox_suite'

# oracle-suite: a help case expecting another exit code fails, named (one case, no fixture build).
plant_oracle_case() {
    sed -i 's/result = c.unread_input(\[str(BIN), \*spell\]).code(0)/result = c.unread_input([str(BIN), *spell]).code(1)/' \
        tests/oracle/protocol_cases.py
}
probe oracle-suite plant_oracle_case "FAIL O.help" \
    env FVDEP_ORACLE_CASE=O.help bash -c 'source tools/gate.sh; oracle_suite'

# judge-suite: a case expecting another verdict line fails, named (one case: semver.parse, the
# fastest).
plant_judge_case() {
    sed -i "s/PROVEN \$id@1.0.0 \$impl/PROVEN \$id@9.9.9 \$impl/" tests/judge/run.sh
}
probe judge-suite plant_judge_case "FAIL E.fn.parse" \
    env FVDEP_JUDGE_CASE=E.fn.parse bash -c 'source tools/gate.sh; judge_suite'

# verification-canaries: a bad control expecting acceptance fails, named (one case).
plant_canary_case() {
    sed -i 's/^\(raw\/bad\/002_badDef\.ndjson\t[0-9a-f]*\t\).*/\1accept accept accept/' \
        tests/canaries/MANIFEST.tsv
}
probe verification-canaries plant_canary_case "FAIL raw/bad/002_badDef.ndjson" \
    env FVDEP_CANARY_CASE=raw/bad/002_badDef.ndjson bash -c 'source tools/gate.sh; verification_canaries'

# profile-suite: a usage case expecting the outcome of a run fails, named (one case, no launch).
plant_profile_case() {
    sed -i 's/        r.usage("profile check", "--role")/        r.code(0)/' tests/profile/boundary_cases.py
}
probe profile-suite plant_profile_case "FAIL usage.empty" \
    env FVDEP_PROFILE_CASE=usage.empty bash -c 'source tools/gate.sh; profile_suite'

# profile-witness: a fixture removed leaves the targets it alone covers uncovered, named (U6 Q).
plant_witness_fixture() { rm tests/profile/witness/Termination.lean; }
probe profile-witness plant_witness_fixture $'uncovered\trule\tLean.Parser.Termination.decreasingBy' \
    bash -c 'source tools/gate.sh; profile_witness'

# profile-witness, P4's pinned scoped namespaces: one dropped from `scopedNamespaces` → the live set
# differs, named (the scoped part alone).
plant_scoped() { sed -i 's/, \["Std", "WP"\]\]$/]/' tool/FvdepCore/Profile/Table.lean; }
probe profile-scoped plant_scoped "differ scoped live-only [Std.WP] pinned-only []" \
    env FVDEP_WITNESS_PART=scoped bash -c 'source tools/gate.sh; profile_witness'

# isolation: a case expecting another environment inside the step fails, named (one case).
plant_isolation_case() { sed -i 's/"HOME,LC_ALL,PATH,PWD,TMPDIR"/"HOME,LC_ALL,PATH,TMPDIR"/' tests/isolation/run.py; }
probe isolation plant_isolation_case "FAIL G1.env" \
    env FVDEP_ISOLATION_CASE=G1.env bash -c 'source tools/gate.sh; isolation'

# isolation's containment check: a job that sees kthreadd (= the host's PID namespace) refuses
# before it builds or runs a step (tools/pidns-check.sh, the default proc root planted + the
# GitHub runner's pass dropped: a CI copy runs the check itself).
plant_isolation_pidns() {
    mkdir -p .planted-proc/1 .planted-proc/2 && echo flock >.planted-proc/1/comm &&
        echo kthreadd >.planted-proc/2/comm &&
        sed -i -e 's|^proc="${1:-/proc}"$|proc="${1:-$PWD/.planted-proc}"|' -e '/GITHUB_ACTIONS/d' \
            tools/pidns-check.sh
}
probe isolation-pidns plant_isolation_pidns "shares the host's PID namespace" \
    env FVDEP_ISOLATION_CASE=G1.env bash -c 'source tools/gate.sh; isolation'

# acceptance: a merged case whose expectation no longer holds fails the stage, named.
plant_acceptance() {
    sed -i '0,/ctx.call("--version").code(0)/s//ctx.call("--version").code(3)/' \
        tests/acceptance/test_invocation.py
}
probe acceptance plant_acceptance "FAIL invocation.version:" \
    env FVDEP_ACCEPTANCE_CASE=invocation.version bash -c 'source tools/gate.sh; acceptance'

# codec-suite's frozen inventories (expected values change only by their own unit): one expected
# value flipped → the freeze guard names the breach before any case runs.
plant_frozen() { # FILE
    awk -F'\t' -v OFS='\t' 'NR == 2 { $NF = (substr($NF, 1, 1) == "0" ? "1" : "0") substr($NF, 2) } 1' \
        "$1" >frozen.tmp && mv frozen.tmp "$1"
}
plant_frozen_jh() { plant_frozen tests/codec/FROZEN-JH.tsv; }
plant_frozen_jhd() { plant_frozen tests/codec/FROZEN-JHD.tsv; }
with_build=0 probe codec-freeze-jh plant_frozen_jh "B2-2 breach" python3 -I tests/codec/freeze_jh.py
with_build=0 probe codec-freeze-jhd plant_frozen_jhd "B3-2 breach" python3 -I tests/codec/freeze_jhd.py

# cli: a binary answering as the contract says passes; one printing a wrong version fails. The fake
# mirrors docs/interface.md §1–§2 whole, failed writes included (exit 2; the message unless the pipe
# broke) — Python, since sh cannot tell a broken pipe from a full device — + the `index` cases
# smoke.sh runs (contract U4 C9: help, a usage refusal, the presence refusal outside a library;
# inside one the fake builds nothing → exit 2).
fake_binary() {
    local version
    version="$(sed -n 's/^def version : String := "\(.*\)"$/\1/p' Fvdep/Version.lean)"
    [[ -e .planted ]] && version=0.0.0-planted
    cat >fake-fvdep <<PY
#!/usr/bin/env python3
import os, sys
usage = "Usage: fvdep <command> [<arguments>]\n"
no_library = 'No fvdep library found here. Run "fvdep index" in a library working copy.\n'
args = sys.argv[1:]
if args == ["--version"]:
    fd, text, code = 1, "fvdep $version\n", 0
elif args in (["help"], ["--help"], ["help", "help"], ["help", "--help"]):
    fd, text, code = 1, usage + "\nCommands:\n  help [<command>]  Show help.\n  index [--check]   Write or check index.json.\n\nOptions:\n  --version         Show the version.\n", 0
elif args in (["index", "--help"], ["help", "index"]):
    fd, text, code = 1, "Usage: fvdep index [--check]\n\nOptions:\n  --check  Compare index.json with the library.\n", 0
elif args in (["index"], ["index", "--check"]):
    library = os.path.exists("lean-toolchain") and os.path.exists("Fvdep/Registry.lean")
    fd, text, code = 2, "Build failed: the fake builds no library\n" if library else no_library, 2
else:
    fd, text, code = 2, usage, 2
try:
    os.write(fd, text.encode())
except BrokenPipeError:
    code = 2
except OSError as e:
    code = 2
    try:
        os.write(2, f"Could not write the output: {e.strerror}.\n".encode())
    except OSError:
        pass
os._exit(code)
PY
    chmod +x fake-fvdep
    bash tests/cli/smoke.sh ./fake-fvdep
}
probe cli plant_marker "FAIL --version" fake_binary

# Compiler options: `autoImplicit` off rejects an implicit variable, `warningAsError` turns a lint
# into a failure, `linter.extra.dupNamespace` rejects a repeated namespace; each plant compiles
# once its owning option is removed (the option, not something else, rejects it).
owned() { # OPTION PLANT-LINE
    local option="$1" line="$2"
    lake build Fvdep >/dev/null 2>&1 || return 0
    [[ -e .planted ]] || return 0
    printf '\n%s\n' "$line" >>Fvdep/Version.lean
    lake build Fvdep >build.log 2>&1 && return 0
    sed -i "s/⟨\`$option, [a-z]*⟩, //; s/, ⟨\`$option, [a-z]*⟩//" lakefile.lean
    lake build Fvdep >/dev/null 2>&1 || return 0
    printf 'rejected only while %s is set\n' "$option"
    return 1
}
implicit() { owned autoImplicit 'def probeImplicit (x : α) : α := x'; }
probe option-autoImplicit plant_marker "rejected only while autoImplicit is set" implicit
warning() { owned warningAsError 'def probeWarning (x : Nat) : Nat := 0'; }
probe option-warningAsError plant_marker "rejected only while warningAsError is set" warning
dupns() { owned linter.extra.dupNamespace 'def Fvdep.Fvdep.probeDup : Nat := 0'; }
probe option-dupNamespace plant_marker "rejected only while linter.extra.dupNamespace is set" dupns

# ci-gate: a run whose shard job was skipped is not green (fixtures of `gh run view --json jobs`).
ci_verdict() {
    local doc missing
    doc='{"jobs":[{"name":"gate (lean)","conclusion":"success"},{"name":"gate (checks)","conclusion":"success"}]}'
    [[ -e .planted ]] && doc='{"jobs":[{"name":"gate (lean)","conclusion":"success"},{"name":"gate (checks)","conclusion":"skipped"}]}'
    missing="$(bash -c 'source tools/ci-gate.sh; ci_missing "$1" lean checks' _ "$doc")" || return 1
    [[ -z "$missing" ]] && return 0
    printf 'not green: %s\n' "$missing"
    return 1
}
with_build=0 probe ci-verdict plant_marker "not green: checks" ci_verdict

# ci-gate: a watch that ends early (a transient API error) is no verdict — `ci_await` watches again
# until the run reports completed (control: a stub `gh` whose first watch fails like an HTTP 502);
# a run never completed within the deadline = no verdict, named (plant).
ci_wait() {
    local bin rc
    bin="$(mktemp -d)"
    cat >"$bin/gh" <<'STUB'
#!/usr/bin/env bash
case "$1 $2" in
"run watch")
    n="$(cat "$GH_STUB/watches" 2>/dev/null || echo 0)"
    echo $((n + 1)) >"$GH_STUB/watches"
    [[ "$n" -ge 1 ]] || {
        echo 'failed to get jobs: HTTP 502: Server Error' >&2
        exit 1
    }
    [[ -e "$GH_STUB/never" ]] || : >"$GH_STUB/done"
    ;;
"run view") if [[ -e "$GH_STUB/done" ]]; then echo completed; else echo in_progress; fi ;;
esac
STUB
    chmod +x "$bin/gh"
    [[ -e .planted ]] && : >"$bin/never"
    GH_STUB="$bin" PATH="$bin:$PATH" bash -c 'source tools/ci-gate.sh; ci_await 1 4 1' 2>"$bin/err"
    rc=$?
    command grep -h 'did not complete' "$bin/err"
    rm -rf "$bin"
    return "$rc"
}
with_build=0 probe ci-await plant_marker "did not complete within 4 s" ci_wait

# fast gate: a failing background stage (deps: a pin without a row) fails the fast gate, named.
probe fast-gate plant_tool "FAILED: deps" bash tools/fast-gate.sh

# fast gate: a build-consuming stage ahead of lean-build in FAST_STAGES (it would run before the
# build) → exit 2 before any stage runs.
plant_fast_order() { sed -i "/^FAST_STAGES=/s/ lean-build lean-style / lean-style lean-build /" tools/gate.sh; }
probe fast-gate-order plant_fast_order "lean-build must lead" bash tools/fast-gate.sh

# index (C7): the committed index.json one byte off the library → drift; a theorem forged in
# FvdepProofs (kernel check skipped at elaboration) → the kernel replay rejects its module; a
# registry list in a form fvdep cannot read → that refusal. A planted run builds the library afresh
# (≈ 3 GB peak on the launch library) ⇒ a run that executes holds one lock across these probes (CI
# runners: 16 GB); a control or restored run (closure = the tree's) reuses the verdict without it
# (waiting there idles a probe slot for another probe's whole planted run).
index_stage() {
    bash -c 'source tools/gate.sh
[[ "$(cat .gate/index.green 2>/dev/null)" == "$(index_key)" ]] || { exec 9>"$1" && flock 9; } || exit 2
index' _ "$scratch/index.lock"
}
plant_index_drift() { printf ' ' >>index.json; }
probe index-drift plant_index_drift "index.json differs from the library" index_stage
plant_index_forged() {
    cat >FvdepProofs/Probe.lean <<'EOF'
import Lean
set_option debug.skipKernelTC true
open Lean Elab Command in
run_cmd liftCoreM <| addDecl (.thmDecl {
  name := `FvdepProofs.Probe.forged
  levelParams := []
  type := mkConst ``False
  value := mkConst ``True.intro
})
EOF
    printf 'import FvdepProofs.Probe\n' >>FvdepProofs.lean
}
probe index-replay plant_index_forged "Kernel replay rejected FvdepProofs.Probe: " index_stage
plant_index_form() {
    sed -i 's/^\(def profiles : .*\) := \[\]$/\1 := List.reverse []/' Fvdep/Registry.lean
}
probe index-registry plant_index_form \
    "The registry uses a form fvdep cannot read: Fvdep.Registry.profiles." index_stage

# index-history (C7 + C9 `history`): each history breach fails the stage, named; every control run
# is the copy's root commit (no committed index.json, or an unchanged one) and passes.
history_stage() { bash -c 'source tools/gate.sh; index_history'; }
hist_d() { local s=''; for _ in {1..64}; do s+="$1"; done; printf '%s' "$s"; }
hist_op() { printf '{"compat":null,"digest":"%s","id":"base64.encode","obligations":[],"version":"1.0.0"}' "$1"; }
hist_notice() { printf '{"id":"base64.encode","reason":"%s","replacement":null,"version":"1.0.0"}' "$1"; }
hist_record() { # LAST_COMMIT TOOLCHAIN
    printf '{"digest":"%s","id":"base64.encode","kind":"operation","last_commit":"%s","toolchain":"%s","version":"1.0.0"}' \
        "$(hist_d 1)" "$1" "$2"
}
hist_index() { # OPERATIONS REMOVED NOTICES TOOLCHAIN
    printf '{"notices":[%s],"operations":[%s],"removed":[%s],"schema":1,"toolchain":"%s"}\n' "$3" "$1" "$2" \
        "$4" >index.json
}
hist_commit() { git add index.json && git -c user.name=probe -c user.email=probe@invalid commit -q -m "$1"; }
hist_tc=leanprover/lean4:v4.35.0
plant_history_digest() {
    hist_index "$(hist_op "$(hist_d 1)")" "" "" "$hist_tc" && hist_commit base &&
        hist_index "$(hist_op "$(hist_d 3)")" "" "" "$hist_tc"
}
plant_history_vanished() {
    hist_index "$(hist_op "$(hist_d 1)")" "" "" "$hist_tc" && hist_commit base && hist_index "" "" "" "$hist_tc"
}
plant_history_toolchain() {
    hist_index "$(hist_op "$(hist_d 1)")" "" "" "$hist_tc" && hist_commit base &&
        hist_index "" "$(hist_record "$(git rev-parse HEAD)" "$hist_tc")" "$(hist_notice r)" "$hist_tc"
}
plant_history_last() {
    hist_index "$(hist_op "$(hist_d 1)")" "" "" "$hist_tc" && hist_commit base &&
        hist_index "" "$(hist_record "$(printf '0%.0s' {1..40})" "$hist_tc")" "$(hist_notice r)" \
            leanprover/lean4:v9.9.9
}
plant_history_notice() {
    hist_index "$(hist_op "$(hist_d 1)")" "" "$(hist_notice first)" "$hist_tc" && hist_commit base &&
        hist_index "$(hist_op "$(hist_d 1)")" "" "$(hist_notice edited)" "$hist_tc"
}
plant_history_diverge() {
    local base left right tree head
    hist_index "$(hist_op "$(hist_d 1)")" "" "" "$hist_tc" && hist_commit base && base="$(git rev-parse HEAD)" &&
        hist_index "$(hist_op "$(hist_d 1)")" "" "$(hist_notice left)" "$hist_tc" && hist_commit left &&
        left="$(git rev-parse HEAD)" && git checkout -q "$base" &&
        hist_index "$(hist_op "$(hist_d 1)")" "" "$(hist_notice right)" "$hist_tc" && hist_commit right &&
        right="$(git rev-parse HEAD)" && git checkout -q "$left" && tree="$(git write-tree)" &&
        head="$(git -c user.name=probe -c user.email=probe@invalid commit-tree "$tree" -p "$left" -p "$right" -m merge)" &&
        git reset -q --hard "$head"
}
plant_history_shallow() { git rev-parse HEAD >.git/shallow; }
probe index-history-digest plant_history_digest "changed its digest" history_stage
probe index-history-vanished plant_history_vanished "base64.encode@1.0.0 vanished" history_stage
probe index-history-toolchain plant_history_toolchain "was removed without a toolchain change" history_stage
probe index-history-last plant_history_last "the removal names lastCommit" history_stage
probe index-history-notice plant_history_notice "the notices do not extend this commit's" history_stage
probe index-history-diverge plant_history_diverge "the parents' notices diverge" history_stage
probe index-history-shallow plant_history_shallow "shallow repository" history_stage

launch
wait
cat "$results"/*
missed="$(cat "$results"/* | grep -c '^PROBE .*: FAILED')"
# A probe job that died before printing its line counts as failed.
reported="$(cat "$results"/* | grep -c '^PROBE ')"
if [[ $reported -ne $n ]]; then
    printf 'gate-probe: %d of %d probes printed no result\n' $((n - reported)) "$n"
    missed=$((missed + n - reported))
fi
printf 'gate-probe: %d probe(s) failed\n' "$missed"
exit "$missed"
