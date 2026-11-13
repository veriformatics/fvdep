# U1 Foundation — contract (agent-read)

Sources: `.agent/spec.md` Decisions (Stack, Host, Public interface (`docs/interface.md` §1), Openness, Accepted risks), the IMPLEMENT body (gates: format, lint, type-check, test, spec-lint, tree-clean, scanners; security scanning in gate + CI; update automation), CLAUDE.md `Execution` (gate command, timings, step ledger, fast gate, CI gate, evidence) + `Engineering` (purpose-built checks with planted inputs, verification integrity, tiers). Precedent: fvapi `docs/contracts/U1-foundation.md` (consultant-reviewed); deltas below are fvdep's.

Tiers: **kernel** = gate aggregation + selection, every check predicate that decides green, probe verdicts, runner status + lifecycle + isolation, fan-out wiring, CI-helper completion, the CLI exit mapping. **data** = package metadata + pinned-tool records (revalidated by `tools/fetch-tools.sh` digests + `lake build`).

## Gate verdict (`tools/gate.sh`)

- G1 Registry `STAGES` (stage → shards) nonempty; each row = a unique stage whose function exists + ≥ 1 shard; an invalid registry fails before any stage (rc 2). A run executes the selected stages in order, each in a subshell, to completion after any failure; a stage that exits its process cannot end the run. Each stage prints `=== <stage> ===` then `<stage> rc=<N> <S>s`; the run ends with `gate rc=0 <S>s` iff every selected stage returned 0, else `FAILED: <stage…>` + `gate rc=1 <S>s`, exit 1.
- G2 `--shard NAME` runs exactly the stages tagged NAME; unknown shard or extra argument → usage on stderr, exit 2, no stage runs.
- G3 Every stage verifies the tools it consumes: pinned tools (`tools/tools.lock`) run by their installed path after `tools/fetch-tools.sh` confirms version + archive digest + installed-binary digest (a changed cached binary is reinstalled from the verified archive; an ambient same-named executable never stands in); Lake packages are pinned by commit in their `lake-manifest.json`; a missing tool fails its stage — unavailable = gate incomplete, never green.
- G4 Sourcing `tools/gate.sh` defines the stage functions + `registry_ok` without running a stage.
- G5 Step ledger: each stage end appends one TSV row to `.gate/ledger.tsv` (gitignored; header `date tree kind step seconds verdict class`): date = run start (UTC); tree = tree object of the graded file set (tracked + untracked-unignored; `unknown` outside git); kind = `gate` | `shard:<name>` | `fast`; verdict `green` | `red`; class `-`, a red `unclassified` until `tools/gate-ledger.sh classify LINE product|gate|flake|planted`. Unwritable ledger → `ledger: cannot append …` + `FAILED: … ledger`, rc 1.
- G6 Stage predicates (U1 set; later units register theirs):
  - `tools` = every pinned tool verifies (G3).
  - `lean-build` = `lake build` of every target in both packages under `leanOptions` autoImplicit off, relaxedAutoImplicit off, warningAsError on + the non-default core linters `linter.extra.{dupNamespace, unnecessarySeqFocus, unreachableTactic, unusedDecidableInType}` + `linter.redundantVisibility` (type-check + lint in one build: a separate `lake lint --linters` build rebuilds every module twice per run, measured 4 → 4 → 4 modules; `lake lint --builtin-only` alone runs no linter).
  - `lean-style` = Lean sources: no tab, no trailing whitespace, no line over 100 characters, final LF; + lean-fmt (`tools/lean-fmt`, pinned `v4.35.0` commit) `format --check` + `check` in both packages report no drift + no finding (a file that does not compile = red). Qualified at U1: deterministic (a second format run leaves bytes identical) + idempotent (check after format = clean), build + tests green after formatting, planted misformat caught (P1).
  - `lean-test` = `lake test` in `tool/` (driver: per-case PASS/FAIL, slowest case, rc = failures; generators seeded, seed printed).
  - `cli` = the built `fvdep` binary through every K2 case (rc, stream used, other stream empty, `--version` = `Fvdep/Version.lean`).
  - `imports` = library modules (`Fvdep*`, `FvdepPreview*`, later `FvdepProofs*`) import Init, Std + library modules alone; tool shipped modules (`tool/FvdepCore*`, `tool/FvdepIO*`, `tool/Main.lean`) import Init, Std, Lean, Lake, Fvdep*, FvdepCore*, FvdepIO* alone; test modules may import more; rejection names file + line.
  - `preview` = no module under `Fvdep` imports `FvdepPreview` or `FvdepProofs`.
  - `spec` = `.agent/spec-lint .agent/spec.md`.
  - `shell` = shellcheck (pinned) over every tracked or untracked-unignored shell file (`*.sh` + shebang sh/bash) outside `prototype/` (disposable, outside the gate until retired at U14).
  - `python` = ruff + pyrefly (pinned, explicit configs) over stdlib-only Python outside `prototype/` (gate helpers, test drivers).
  - `secrets` = betterleaks over git history + every tracked or untracked-unignored file (no live validation).
  - `vulns` = osv-scanner over the declared lockfile set (`tools/lockfiles.txt`; every listed file exists, every lockfile in the tree is listed); an empty set passes only with the list's explicit `none` line; scanner rc 128 (no packages) ≠ success.
  - `workflows` = zizmor (offline) + actionlint over `.github/`.
  - `fanout` = `gate.yml` matrix = the shards of `STAGES`, every stage has a shard, job `gate` runs exactly one unconditional, unmasked `bash tools/gate.sh --shard "$SHARD"` step with fail-fast off.
  - `deps` = every pin (lean-toolchain, `tools/tools.lock`, workflow actions by digest, Lake packages of every `lake-manifest.json`) has a row in `docs/dependencies.md` naming its update path + scanner.
  - `renovate` = each `renovate.json` custom manager extracts exactly the pins of the real files (+ a synthetic two-package Lake manifest), as Renovate's regex manager would; a `tools.lock` line whose URL lacks its version fails naming `tools/pin-tool.sh`.
  - `meta` = one nonempty version, equal in `Fvdep/Version.lean` + both lakefiles; every `.claude/rules/*.md` frontmatter closes + keeps `paths:` as a list of double-quoted globs.
  - `tree-clean` = the run leaves the graded file set unchanged: its tree object (tracked + untracked-unignored, content + mode) before the first stage = after the last stage (a stage writing outside ignored paths fails it); outside git = red.
  - `probes` = P1.

## Remote run (`tools/vflab-run`; fvdep's own runner — never `~/gate/repo.git`)

- R1 Normal command exits 0–255 propagate exactly; signal, OOM kill, timeout, failed start or lost connection → nonzero, never 0; command + output filter both failing → the command's status; failed filter or local archive with the command at 0 → 125. Unit `Type=oneshot`, deadline `TimeoutStartSec`, `TimeoutStopSec=30`, `IgnoreSIGPIPE=no`.
- R2 Argv passes as a vector, systemd environment expansion off; working directory = the workspace; PATH = elan (toolchain from `lean-toolchain`) + `.tools/bin` + system; stdin = /dev/null; stdout + stderr separate + live, the remote workspace path rewritten to the local worktree path.
- R3 Workspace `~/gate/ws/fvdep-<worktree>-<8 hex>` (one per worktree, reset before every run): inside the unit + under its lock, a git repository at the worktree's `HEAD` fetched from a per-run `git bundle` uploaded beside it (full history; no controller `.git` pointer) + exactly the worktree's tracked (minus deleted) + untracked-unignored files (deleted removed, ignored absent, executable bits + symlinks kept); every `.lake/` + `.tools/` persist as caches, `.gate/` as the ledger. A workspace recorded for another worktree path → 125. Different worktrees run concurrently.
- R4 Runs as `eturkes` in `fvapi_gate.slice` (exists + active, else 125 naming it) with its own `MemoryMax` (default 24G, below the slice's 40 GiB; `FVDEP_VFLAB_MEMORY` overrides with a K/M/G/T size, one at or above the slice's live cap → 125 naming it) + `MemorySwapMax=0` so an OOM stays in the unit; a malformed `FVDEP_VFLAB`, `FVDEP_VFLAB_TIMEOUT` (whole seconds ≥ 1) or `FVDEP_VFLAB_MEMORY` → exit 2 before any remote action; touches only `~/gate/ws/fvdep-*` + the unit; prints the unit's resource summary (runtime, CPU time, memory peak) on stderr after the command.
- R5 Qualification = `bash tools/vflab-run-probe.sh` from the desktop (exit statuses, signals, OOM, timeout, malformed settings, a MemoryMax above the slice's cap, literal argv, path mapping on both streams, deleted tracked + untracked + ignored files, executable bits + symlinks, same-worktree serialization, a linked worktree, origin collision, failing filter, ledger kept across runs, resource summary printed), reported in the commit body.
- R6 `tools/vflab-reclaim.sh [--dry-run]` (desktop): removes `~/gate/ws/fvdep-*` workspaces (+ `.origin`, `.lock`, stray bundles) whose recorded origin is no worktree on this machine or that hold no origin record; touches no other `~/gate/ws/` entry; prints each removal + bytes freed.

## Skeleton (data; K2's exit mapping = kernel)

- K1 Root Lake package `fvdep` (lean_libs `Fvdep`, `FvdepPreview`; version module `Fvdep/Version.lean`) + `tool/` package `fvdeptool` (lean_libs `FvdepCore`, `FvdepIO`; exe target `fvdep-cli` with `exeName := "fvdep"` (the `require fvdep` already declares the name `fvdep`); test exe `fvdep-tests` = `testDriver`; requires `fvdep` by path); `lean-toolchain` = `leanprover/lean4:v4.35.0` in both; both `lake-manifest.json` committed; licence Apache-2.0 (`LICENSE`). Probes: a planted implicit variable, a planted warning + a planted `dupNamespace` each rejected only while its option is set.
- K2 `fvdep --version` → exactly `fvdep <version>` + LF on stdout, rc 0; `fvdep help`, `--help`, `help help`, `help --help` → usage on stdout, rc 0; no argument, unknown command, unknown option or extra argument → usage on stderr, rc 2 (`docs/interface.md` §1); a failed write of either stream (full device) → rc 2 + `Could not write the output: <reason>.` on stderr while it accepts writes; a broken pipe (no reader left) → rc 2, stderr empty; the handler writes nothing to stdout (output already accepted before a failed write stays; §2; smoke cases). Theorem `FvdepCore.Cli.run_streams`: every invocation writes one stream alone (exit 0 + stderr empty, or exit 2 + stdout empty + usage on stderr).
- K3 `lake test` (in `tool/`) runs the driver; `cli` drives the built binary through every K2 case.

## CI + updates

- C1 `.github/workflows/gate.yml`: push to `main` + `ci/**`, pull requests, weekly schedule; one job per shard (`fail-fast: false`), `SHARD` = the matrix value, one unconditional `bash tools/gate.sh --shard "$SHARD"` step; `fetch-depth: 0`; GitHub-hosted runners; `permissions: contents: read`; `persist-credentials: false`; actions pinned by digest; no secrets; bounded steps + job.
- C2 `.github/workflows/codeql.yml`: CodeQL `security-extended` over `actions` (languages join as their code lands: c-cpp, rust, python, javascript-typescript) on `main` + `ci/**` pushes, pull requests, weekly; `tools/ci-gate.sh` fails a `ci/**` run with an open CodeQL alert on its ref. Lean has no CodeQL extractor: a declared coverage boundary.
- C3 `renovate.json`: digest-pinned actions; custom managers for `lean-toolchain`, `tools/tools.lock`, every `lake-manifest.json` (lean-fmt grouped with the Lean toolchain); `renovate-config-validator --strict` rc 0 recorded per edit. Activation (installing the Renovate app on the repo) = the user's action, named in the unit's close.
- C4 `tools/ci-gate.sh <unit>`: dirty tree or invalid unit → rc 2; pushes only `ci/<unit>`; green iff the gate run's commit = HEAD + every shard has exactly one `gate (<shard>)` job with conclusion success + the CodeQL run on that commit succeeded + no open CodeQL alert on `ci/<unit>`; prints commit, tree, per-job conclusion + wall-clock; deletes the branch only while it still names the tested commit; never pushes `main`.

## Fast gate + timings

- F1 `tools/fast-gate.sh` runs `FAST_STAGES` (declared in `tools/gate.sh`): independent checks in parallel, then `lean-build` → `lean-style` → `lean-test` → `cli`; reports every selected stage; ledger rows kind `fast`; rc 0 iff all returned 0 + the ledger took every row; prints selected + skipped stages; never claims full-gate green.
- F2 Commit body + `CLAUDE.local.md` (timings = machine facts, CLAUDE.md `Authoring`): caller wall-clock + in-gate time on vflab for cold, warm, no-op + one content-changing Lean edit.

## Probes (`tools/gate-probe.sh`, stage `probes`)

- P1 Each purpose-built check passes on a clean scratch copy, fails on its planted input with its own diagnostic, passes again once restored byte for byte: registry, stage exit + several failures, shard usage, missing + tampered tools, `imports` (both policies), `preview`, `lean-style` (style rule + lean-fmt misformat), `fanout` breaches, `deps`, `renovate` breaches, `meta` invariants, `spec`, `cli`, `vulns` list breaches + a planted vulnerable lockfile, `tree-clean`, the three compiler-option probes (K1), `ci_missing`, a failing fast-gate background stage, the ledger (rows + unwritable).

## Boundary + records

- U1's green covers this contract alone; later units register their stages in the same gate.
- `tools/gate.sh` runs from a clean public clone (no vflab, no private path); vflab + desktop specifics stay in `CLAUDE.local.md`.
- `.agent/review.md` = review ledger (Unit | Check | Status | Evidence) with U1's fixed check set; the commit body records each credited red run (revision + command), mutation evidence where behaviour passed before its test, and checks not run.
