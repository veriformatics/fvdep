# U6 blind profile suite — tester-8

Base product `9e31b4f`; suite checkpoint `7b67085`. Oracle = U6 D/T/K/P/B/C/I/Q/R, U5 T/R/S/K/D, U3 J/H/T3, interface §1. U6 implementation unread. `COVERAGE.tsv` = runner registrations; `PLAN.tsv` = clause-to-ID map.

| part | cases | pre-unit red |
|---|---:|---:|
| Syntax, grammar, scope, names, ordering and corpus | 264 | 264 |
| Invocation, source snapshots and parse budgets | 42 | 42 |
| Record decoder and request attribution | 66 | 66 |
| Child step disposition and frame caps | 9 | 9 |
| Phase entry, refusal and compile barrier | 39 | 39 |
| Total | 420 | 420 |

## Verification

| check | result |
|---|---|
| Coverage and plan | `python3 -I tests/profile/run.py --validate-plan`: rc 0, 25 rows, 420 IDs; coverage bytes = registrations. Seed `grep -c unknown` → 24, rc 0; filled → 0, rc 1. |
| Pinned static checks | Ruff 0.17.4 (`check --config ruff.toml --output-format concise tests/profile`), Pyrefly 1.4.1 (`check --config pyrefly.toml --output-format=min-text --min-severity=warn tests/profile`), ShellCheck 0.11.0 (`-- tests/profile/run.sh`): rc 0 each, Pyrefly 0 diagnostics. First lint run: Ruff B905 (zip strictness), Pyrefly 26 `dict` invariance diagnostics, ShellCheck green; fixed before the green run. |
| D4 fixture qualification | `fvdep-dev profile positions` under each fixture's declared grammar: 260 observations, 0 differences on the final run. Initial run 259/260: D4 returns only the later parse error of `order.command` and drops the parsed prefix; qualify that prefix alone, keep C1's mixed-order case unchanged. Cap anchor from the pre-unit parse tree: `def deep := (((7)))` = 48 occurrences; first depth 9 = ordinal 38 at `1:15`. First depth 6 of `def a := (sorry)` = ordinal 26 at `1:9`. |
| Raw phase control | U5 D1 without `--profile`: both phases built, their exports/handoff and all artifacts matched the witness, one cold library fill, eight real bwrap launches. This validates the fixture, not U6 acceptance. |
| Raw step controls | `fvdep-dev sandbox run` (U5 D2): nine scripts; correct statuses and file/frame witnesses. `no-record`/`extra-file` exit 0, nonzero exits 3, signal 137, timeout, over-frame `overflow`, over-file exit 153, frame/file at the bound complete. Combined D4 + phase + step controls rc 0. |
| Pre-unit red | `tools/vflab-run bash tests/profile/run.sh --evidence tests/profile/.runs/red.jsonl` (relay the artifact out in the same unit): seed 5008001, 2 jobs, 420 FAIL, 0 PASS, 0 harness errors, rc 255 (failure count capped for a process exit). Service runtime 60.215 s, peak `141.7M` as reported. No product change from `9e31b4f`. |
| Narrowed replay | `FVDEP_PROFILE_JOBS=1 FVDEP_TEST_SEED=5008021 bash tests/profile/run.sh --case record.generated.00 --case usage.empty` in vflab: printed seed 5008021, exactly 2 FAIL, 0 harness errors, rc 2. |
| Red transcript | `RED.jsonl`: 1 metadata row, 420 invocations, 420 case verdicts. Each invocation reached a built binary; all rc 2 with empty stdout and old usage on stderr, no bwrap/build trace. Coverage, invoked IDs and failed IDs match; `<run>`/`<repo>` replace private paths. |
| Not run | U6 green, full gate, CI. Pre-unit red grades the command's absence, not the later implementation's correctness or green runtime. |

## Replay and readings

- `tools/vflab-run bash tests/profile/run.sh [--case <id-prefix>]`. Repeat `--case`; `FVDEP_PROFILE_JOBS=1..8` (default 2), `FVDEP_TEST_SEED` (printed), `FVDEP_DEV_BIN` and `FVDEP_BIN` go inside the remote command. `python3 -I tests/profile/run.py --coverage` regenerates `COVERAGE.tsv` without calling the driver. Per-case cache starts without builds; the runner seeds only U5 T1's toolchain record once per suite.
- P5a `modules[].path` = `A/B.lean` for `A.B`; library rows in module-name byte order, with explicit imports in source order, no implicit `Init` in those rows. P5b grammar lines for every nonempty grammar once all headers pass, including later bodies not walked; none after a header refusal. The request oracle uses J4 serialization + Python SHA-256 over independent fixtures and U5 T1's observed fingerprint; never D1/D2's returned request hash.
- D3 observes ordered stdout, the cold-cache K7 trace, and argv from a real forwarding bwrap wrapper. Setup/preflight controls return synthetic faults without running a step. The frozen-source control changes only its private live input to another valid definition after the parse launch; the proof must still build against the frozen first definition. Fixtures pin syntactic refusals, not an operational proof forgery, build rewrite or sandbox escape.

## Register

| clause | limit / ruling |
|---|---|
| D4 controls | First final-control rerun lacked `.runs/` because vflab excludes/deletes ignored outputs during sync. Recreate it inside the run. Scratch regex and an initial no-op escaped-key edit were corrected before replay. |
| P2/P5a | No syscall-complete claim about parser mounts, or source tampering through the staging boundary. D2 observes argv + trace; the live-file edit exercises B2 without altering staging. The wrong request/source and module-digest cases grade intake independently. |
| P3 | Distinct imports, reversing their order, sibling isolation and transitive roots are pinned. Repeats at the P3 grammar boundary (including explicit `Init` alongside implicit `Init`) are not pinned until the contract fixes duplication semantics. P5b still accepts a shape-correct reported list. |
| P5 | Logged parse failures (including `public import` and unfinished commands) have exact cases. No source fixture triggers the unlogged no-progress / recovered-missing / premature-eoi fallbacks without a parser fault. |
| P5c | A `--child` writes files; the step helper generates the transport frame. No invalid-frame fixture (MAIN's disposition `lake test`); duplicate bwrap status is outside the child seam. Setup/preflight controls leave the sandbox intact. |
| P6 | Node/depth/batch/frame/file caps have inclusive and +1 inputs (node count includes the header). Deadlines use a slow source and a sleeping child, not equality to wall-clock time. D1 does not fix validation for an override beyond J's safe integer range. |
| I1 | `header modifier …` is a pure-tree branch: source reports earlier `module` or the parser's own refusal. Invalid modifier record shapes have a separate case. |
| K1/K2 | Positive choices and documentation are covered; no fixture isolates a forbidden later choice arm or injects a malformed doc tree. That requires a tree-level seam. |
| K4/K6 | Every named R control has a case. Additional unsupported declaration roles (`computedFields`, `contractDeclVal`, `whereFinally`) are not individually qualified; quoted antiquotations and deeper forbidden configuration nodes can be hidden by an earlier ancestor finding. This is not exhaustive coverage of the parser's generated grammar. |
| Q1/Q2 | Freeze probe, scoped-set equality, frontend differential, and compile/deriving qualifications = U6-D. Corpus cases here grade profile acceptance, not elaboration or proof. |

tester-8-DONE-1
