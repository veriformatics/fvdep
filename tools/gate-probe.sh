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

# A git-tracked scratch copy of the worktree (the checks read `git ls-files`); pinned tools come
# along (binaries copied: probes corrupt them; downloads hardlinked: only ever replaced whole) so
# tool stages run offline, and both packages' Lake caches so Lean plants rebuild incrementally.
copy() {
    local dir d
    dir="$(mktemp -d)"
    git ls-files -co --exclude-standard -z | tar --null -T - -cf - | tar -C "$dir" -xf -
    git -C "$dir" init -q && git -C "$dir" add -A &&
        git -C "$dir" -c user.name=probe -c user.email=probe@invalid commit -q -m probe
    if [[ -d "$root/.tools" ]]; then
        mkdir -p "$dir/.tools"
        [[ -d "$root/.tools/bin" ]] && cp -a "$root/.tools/bin" "$dir/.tools/"
        [[ -d "$root/.tools/cache" ]] && cp -al "$root/.tools/cache" "$dir/.tools/"
    fi
    for d in .lake tool/.lake; do
        [[ -d "$root/$d" ]] && cp -a "$root/$d" "$dir/$d"
    done
    # The fixture suite's green mark (keyed on its inputs): the fast gate in a copy reuses it.
    if [[ -f "$root/.gate/ledger-suite.green" ]]; then
        mkdir -p "$dir/.gate" && cp "$root/.gate/ledger-suite.green" "$dir/.gate/"
    fi
    printf '%s' "$dir"
}

# probe NAME PLANT EXPECT CHECK… — CHECK passes on a fresh copy, fails after PLANT with EXPECT in
# its output, passes again after the copy is restored. Probes run in the background, at most
# $jobs at a time (each owns its copy); results print in declaration order once all finish.
jobs=4
results="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
n=0
run_probe() {
    local name="$1" plant="$2" expect="$3" dir pristine control planted restored
    shift 3
    dir="$(copy)"
    pristine="$(mktemp -d)"
    cp -a "$dir/." "$pristine/"
    (cd -- "$dir" && "$@") >"$pristine.control" 2>&1
    control=$?
    (cd -- "$dir" && "$plant") >/dev/null 2>&1
    (cd -- "$dir" && "$@") >"$pristine.planted" 2>&1
    planted=$?
    rsync -a --delete "$pristine/" "$dir/"
    (cd -- "$dir" && "$@") >"$pristine.restored" 2>&1
    restored=$?
    if [[ $control -eq 0 && $planted -ne 0 && $restored -eq 0 ]] &&
        grep -q -F -- "$expect" "$pristine.planted"; then
        printf 'PROBE %s: fired (control 0, planted %d naming "%s", restored 0)\n' \
            "$name" "$planted" "$expect"
    else
        printf 'PROBE %s: FAILED (control %d, planted %d, restored %d; want 0, ≠0 naming "%s", 0)\n' \
            "$name" "$control" "$planted" "$restored" "$expect"
        sed 's/^/    control: /' "$pristine.control" | tail -n 10
        sed 's/^/    planted: /' "$pristine.planted" | tail -n 20
    fi
    rm -rf -- "$dir" "$pristine" "$pristine".{control,planted,restored}
}
probe() {
    while [[ "$(jobs -rp | wc -l)" -ge $jobs ]]; do wait -n; done
    n=$((n + 1))
    run_probe "$@" >"$results/$(printf '%03d' "$n")" 2>&1 &
}

plant_marker() { touch .planted; }

# A gate main() over planted stages; `.planted` switches each scenario's bad case on.
run_main() { # STAGES-text FUNCTIONS-text ARGS…
    local stages="$1" fns="$2"
    shift 2
    bash -c 'source tools/gate.sh
STAGES="$1"
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
probe gate-aggregate plant_marker "FAILED: mid-stage" aggregate

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
probe gate-stage-exit plant_marker "FAILED: first leaver last" exits

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
probe gate-registry plant_marker "has no function ghost_stage" registry

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
probe gate-usage plant_marker "usage: tools/gate.sh" usage

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
probe gate-ledger plant_ledger "ledger: cannot append" ledger_rows

# tree-clean: a stage that writes into the graded file set fails the run, the file named; a stage
# writing an ignored path does not.
tree_written() {
    run_main $'\nwriter probe\ntree-clean probe\n' \
        'writer() { mkdir -p .gate; printf x >.gate/ignored-output; [[ ! -e .planted ]] || printf x >probe-written.txt; }' \
        --shard probe
}
probe tree-clean plant_marker "probe-written.txt" tree_written

# G3: a stage whose pinned tool has no lock line fails; a changed cached tool binary is not used:
# fetch-tools reinstalls it from the verified download (the planted case fails if corrupt bytes
# survive).
shell_stage() { bash -c 'source tools/gate.sh; shell'; }
plant_no_shellcheck() { sed -i '/^shellcheck /d' tools/tools.lock; }
probe gate-missing-tool plant_no_shellcheck "no pinned tool matches linux-x86_64 shellcheck" shell_stage
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
probe tool-identity plant_marker "corrupt cached binary replaced" cached_tool
# shellcheck disable=SC2016  # the planted script's `$1` is literal on purpose
plant_shell() { printf '#!/usr/bin/env bash\necho $1\n' >tools/probe-unquoted.sh; }
probe shellcheck plant_shell "SC2086" shell_stage

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
probe python-ruff plant_python_lint "F821" python_stage
probe python-pyrefly plant_python_type "[missing-attribute]" python_stage
probe python-warning plant_python_warning "[unreachable-except-clause]" python_stage
probe python-config plant_python_config "pyrefly.toml" python_stage
probe python-ruff-missing plant_python_ruff_missing "no pinned tool matches linux-x86_64 ruff" python_stage
probe python-pyrefly-missing plant_python_pyrefly_missing "no pinned tool matches linux-x86_64 pyrefly" python_stage

# secrets: a planted credential-shaped token in an untracked file.
secrets_stage() { bash -c 'source tools/gate.sh; secrets'; }
# The token is derived at run time: a literal here would itself be a finding in this script.
plant_secret() {
    printf 'token = "ghp_%s"\n' "$(printf probe | sha256sum | head -c 36)" >probe-config.toml
}
probe secrets plant_secret "probe-config.toml" secrets_stage

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
probe vulns-unlisted plant_unlisted "probe/Cargo.lock: lockfile not listed" vulns_stage
probe vulns-missing plant_missing "probe/uv.lock does not exist" vulns_stage
probe vulns-advisory plant_vulnerable "lodash" vulns_stage
# A vendored commit OSV lists as affected (libxml2 6c128fd5, OSS-Fuzz git ranges).
plant_vendor_vulnerable() {
    sed -i 's/"commit": "f557259007db9933442dde10aa995c1b00bd3446"/"commit": "6c128fd58a0e4641c23a345d413672494622db1b"/' \
        vendor/hacl-star/lock.json
}
probe vulns-vendor plant_vendor_vulnerable "OSV lists" vulns_stage

# workflows: zizmor + actionlint each fire on a planted defect.
workflows_stage() { bash -c 'source tools/gate.sh; workflows'; }
plant_zizmor() { sed -i '/^          persist-credentials: false$/d' .github/workflows/gate.yml; }
plant_actionlint() { sed -i 's/^    runs-on: ubuntu-26.04$/    runs-on: ubuntu-26.04\n    timeout-minutes: soon/' .github/workflows/codeql.yml; }
probe workflows-zizmor plant_zizmor "artipacked" workflows_stage
probe workflows-actionlint plant_actionlint "timeout-minutes" workflows_stage

# imports: a library module importing `Lean`; a tool module importing a foreign package; preview:
# a library module importing the preview tree.
plant_lib_import() { sed -i '1i import Lean' Fvdep/Version.lean; }
plant_tool_import() { sed -i '1i import Mathlib' tool/FvdepCore/Cli.lean; }
plant_preview() { sed -i '1i import FvdepPreview' Fvdep.lean; }
probe imports-library plant_lib_import "Fvdep/Version.lean:1: import Lean" bash tools/check-imports.sh imports
probe imports-tool plant_tool_import "tool/FvdepCore/Cli.lean:1: import Mathlib" bash tools/check-imports.sh imports
# The audit tree reaches the build through the ledger alone: a shipped module + the test driver
# importing it.
plant_audit_shipped() { sed -i '1i import FvdepAudit.Json.Spec' tool/FvdepCore/Json.lean; }
plant_audit_test() { sed -i '1i import FvdepAudit.Json.Spec' tool/Tests.lean; }
probe imports-audit-shipped plant_audit_shipped "tool/FvdepCore/Json.lean:1: import FvdepAudit.Json.Spec" \
    bash tools/check-imports.sh imports
probe imports-audit-test plant_audit_test "tool/Tests.lean:1: import FvdepAudit.Json.Spec" \
    bash tools/check-imports.sh imports
probe preview plant_preview "Fvdep.lean:1: import FvdepPreview" bash tools/check-imports.sh preview
# A module whose name only starts like an allowed root (the `\.`-in-awk-v regression).
plant_prefix() { sed -i '1i import FvdepPlanted' FvdepPreview.lean; }
probe imports-prefix plant_prefix "FvdepPreview.lean:1: import FvdepPlanted" bash tools/check-imports.sh imports

# lean-style: a tab in a Lean source; a misformatted declaration lean-fmt would rewrite.
plant_tab() { printf '\t-- tab\n' >>Fvdep/Version.lean; }
plant_misformat() { printf '\ndef probeFormat(x:Nat):Nat:=x+1\n' >>Fvdep/Version.lean; }
probe lean-style plant_tab ": tab" bash tools/lean-style.sh
probe lean-fmt plant_misformat "Version.lean" bash tools/lean-style.sh

# fanout: a missing shard; a disabled gate step; a masked one; SHARD unbound; fail-fast on.
fanout_stage() { bash -c 'source tools/gate.sh; fanout'; }
plant_matrix() { sed -i 's/^\( *shard: \)\[lean, checks\]$/\1[lean]/' .github/workflows/gate.yml; }
probe fanout-shards plant_matrix "matrix shards" fanout_stage
plant_disabled() {
    sed -i 's/^\(      - name: Run the gate shard\)$/\1\n        if: false/' .github/workflows/gate.yml
}
probe fanout-disabled plant_disabled "unconditional, unmasked" fanout_stage
plant_masked() {
    sed -i 's/^\(      - name: Run the gate shard\)$/\1\n        continue-on-error: true/' .github/workflows/gate.yml
}
probe fanout-masked plant_masked "unconditional, unmasked" fanout_stage
plant_unbound() { sed -i '/^      SHARD: \${{ matrix.shard }}$/d' .github/workflows/gate.yml; }
probe fanout-unbound plant_unbound "SHARD bound" fanout_stage
plant_failfast() { sed -i 's/^      fail-fast: false$/      fail-fast: true/' .github/workflows/gate.yml; }
probe fanout-failfast plant_failfast "fail-fast false" fanout_stage

# deps: a pinned tool without a dependency-table row.
plant_tool() {
    printf 'planted 1.0.0 linux-x86_64 %064d https://github.com/planted/planted/releases/download/v1.0.0/planted.tar.gz\n' 0 \
        >>tools/tools.lock
}
probe deps plant_tool "planted has no row" python3 -I tools/check-deps.py
plant_vendor_upstream() {
    sed -i 's#"upstream": "https://github.com/hacl-star/hacl-star"#"upstream": "https://github.com/planted/vendored"#' \
        vendor/hacl-star/lock.json
}
probe deps-vendor plant_vendor_upstream "planted/vendored has no row" python3 -I tools/check-deps.py

# vendor: one changed byte, a locked file missing, an unlocked file beside the locked ones.
vendor_stage() { bash -c 'source tools/gate.sh; vendor'; }
plant_vendor_byte() { printf 'x' >>vendor/hacl-star/dist/gcc-compatible/Hacl_Hash_SHA2.h; }
plant_vendor_missing() { rm vendor/hacl-star/dist/LICENSE.txt; }
plant_vendor_extra() { printf 'int planted;\n' >vendor/hacl-star/dist/gcc-compatible/planted.c; }
probe vendor-byte plant_vendor_byte "Hacl_Hash_SHA2.h sha256 differs" vendor_stage
probe vendor-missing plant_vendor_missing "dist/LICENSE.txt missing" vendor_stage
probe vendor-extra plant_vendor_extra "planted.c not in" vendor_stage
# vendor-upstream: a commit-only bump to d826c0c9 (its Hacl_Hash_SHA2.c predates the locked one).
plant_vendor_commit() {
    sed -i 's/"commit": "f557259007db9933442dde10aa995c1b00bd3446"/"commit": "d826c0c9fb494f9476aa3449d7a62412fb5be7d6"/' \
        vendor/hacl-star/lock.json
}
probe vendor-upstream plant_vendor_commit "no longer yields the locked bytes" \
    bash -c 'source tools/gate.sh; vendor_upstream'

# renovate: a manager that stops matching; a half-applied version bump; a greedy Lake manager that
# fuses two packages into one match (the two-package fixture catches it).
plant_manager() { sed -i 's/leanprover\/lean4:v(?<currentValue>/leanprover\/lean5:v(?<currentValue>/' renovate.json; }
probe renovate-extract plant_manager "lean-toolchain: extracted" python3 -I tools/check-renovate.py
plant_halfbump() { sed -i 's/^\(zizmor\) \([0-9.]*\) /\1 99.0.0 /' tools/tools.lock; }
probe renovate-repin plant_halfbump "re-pin with tools/pin-tool.sh zizmor 99.0.0" \
    python3 -I tools/check-renovate.py
plant_lake_manager() { sed -i 's/\*?\\"name\\"/*\\"name\\"/' renovate.json; }
probe renovate-lake plant_lake_manager "tests/renovate/lake-manifest.json: extracted" \
    python3 -I tools/check-renovate.py
plant_vendor_manager() { sed -i 's/\\"commit\\"/\\"comit\\"/' renovate.json; }
probe renovate-vendor plant_vendor_manager "vendor/hacl-star/lock.json: extracted" \
    python3 -I tools/check-renovate.py

# meta: version disagreement; an unquoted rule `paths:` entry; a Lake target the gate never builds.
meta_stage() { bash -c 'source tools/gate.sh; meta'; }
plant_version() {
    sed -i 's/^def version : String := ".*"$/def version : String := "9.9.9"/' Fvdep/Version.lean
}
probe meta-version plant_version 'version "9.9.9" !=' meta_stage
plant_rule() {
    mkdir -p .claude/rules
    printf -- '---\npaths:\n  - Fvdep/**\n---\n\n# planted\n' >.claude/rules/planted.md
}
probe meta-frontmatter plant_rule "paths entry is not a quoted glob" meta_stage
plant_target() { printf '\nlean_lib FvdepPlanted\n' >>lakefile.lean; }
probe meta-targets plant_target "FvdepPlanted" meta_stage

# spec: a spec missing its Phase section.
plant_spec() { sed -i '/^## Phase/,$d' .agent/spec.md; }
probe spec plant_spec "spec-lint:" bash -c 'source tools/gate.sh; spec'

# coverage: docs/verification.md one byte off the ledger's rendering → the `doc` finding.
plant_doc_drift() { sed -i '1s/^/x/' docs/verification.md; }
probe coverage plant_doc_drift "ledger: root: doc:" bash -c 'source tools/gate.sh; coverage'

# ledger-suite: a negative case whose expected rc is flipped fails the suite, named (one case).
plant_case_flip() {
    awk -F'\t' -v OFS='\t' '$1 == "T5" { $4 = 0 } 1' tests/ledger/cases.tsv >cases.tmp &&
        mv cases.tmp tests/ledger/cases.tsv
}
probe ledger-suite plant_case_flip "FAIL T5" env FVDEP_LEDGER_ONLY=T5 bash tests/ledger/run.sh

# cli: a binary answering as the contract says passes; one printing a wrong version fails. The fake
# mirrors docs/interface.md §1–§2 whole, failed writes included (exit 2; the message unless the pipe
# broke) — Python, since sh cannot tell a broken pipe from a full device.
fake_binary() {
    local version
    version="$(sed -n 's/^def version : String := "\(.*\)"$/\1/p' Fvdep/Version.lean)"
    [[ -e .planted ]] && version=0.0.0-planted
    cat >fake-fvdep <<PY
#!/usr/bin/env python3
import os, sys
usage = "Usage: fvdep <command> [<arguments>]\n"
args = sys.argv[1:]
if args == ["--version"]:
    fd, text, code = 1, "fvdep $version\n", 0
elif args in (["help"], ["--help"], ["help", "help"], ["help", "--help"]):
    fd, text, code = 1, usage + "\nCommands:\n  help [<command>]  Show help.\n\nOptions:\n  --version         Show the version.\n", 0
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
probe ci-verdict plant_marker "not green: checks" ci_verdict

# fast gate: a failing background stage (deps: a pin without a row) fails the fast gate, named.
probe fast-gate plant_tool "FAILED: deps" bash tools/fast-gate.sh

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
