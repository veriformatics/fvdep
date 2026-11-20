# U5b blind oracle suite — tester-7

| part | cases | pre-unit red |
|---|---:|---:|
| P projects | 8 | 8 |
| L local git, selection, storage and limits | 26 | 26 |
| X export-profile diagnostic | 1 | 1 |
| E entry resolution | 10 | 10 |
| W typed wire bridge and independent references | 12 | 12 |
| V evaluation, merge and budgets | 12 | 12 |
| O invocation and observable effects | 6 | 6 |
| Q snapshot history and build reuse | 1 | 1 |
| Total | 76 | 76 |

Source = U5b contract at `3218be6`; interface §§1–3, 7–8; library Naming, Operations and Registry; inherited U3 J/H/T, U4 B/C and U5 K/R clauses those sources name. U5b implementation unread. FVDEP_CACHE and git sources are private per case; the only shared setup is the untouched two-commit fixture template and a copyable U5 T1 toolchain record. All fvdep/Lean execution = vflab.

## Verification

| check | result |
|---|---|
| Trusted fixture build | `tools/vflab-run bash tests/oracle/run.sh --qualify-fixture`: exit 0. `fvdep index` ×2; independent SHA-256/H2 matches three generated entry rows. Existing fixture rows unchanged across the second commit. First run: 279.8 s including a cold build, 3.8G peak. |
| Coverage | `COVERAGE.tsv` = runner registrations, asserted on replay. 76 IDs match the union of IDs in the plan. Seeded plan: 22 rows plus X5; no empty/waived row; counter → 0 (grep exit 1). |
| Pinned static checks | Ruff 0.17.4 (`check --config ruff.toml … tests/oracle`), Pyrefly 1.4.1 (`check --config pyrefly.toml … tests/oracle`, 0 diagnostics), ShellCheck 0.11.0 (`tests/oracle/run.sh`): exit 0 each. Fixture line width ≤100: exit 0. |
| Pre-unit red | Suite checkpoint `92a5e47`, product bytes `3218be6`. `bash tests/oracle/run.sh --evidence tests/oracle/.runs/red.jsonl` in `tools/vflab-run`: seed 5007001; 76 FAIL, 0 PASS, 0 harness errors, exit 76. Vflab unit incl. lint: 136.0 s, 3.4G peak. Initial replay before fixture refinements: same counts and exit. |
| Evidence | `RED.jsonl`: 1 metadata row, 86 driver calls, 76 case verdicts. Each case reached a built binary; all calls exit 2 with empty stdout and pre-unit usage on stderr. Coverage, called IDs and failed IDs match. Paths and synthetic URL userinfo redacted. |
| Full gate, CI, U5b green | Not run. This branch has no U5b product code; red proves the commands and predicates are not already satisfied by the pre-unit tree, not that later effects pass. |

## Cases and replay

- `tools/vflab-run bash tests/oracle/run.sh [--case <id-prefix>]`. `--case` repeatable; `FVDEP_ORACLE_JOBS` sets workers inside the remote command (default 2), `FVDEP_TEST_SEED` overrides the printed seed. `FVDEP_BIN` and `FVDEP_DEV_BIN` can select binaries.
- `--evidence <path>` writes invocations and verdicts; the full red run additionally relayed them from its worktree workspace. `python3 -I tests/oracle/run.py --coverage` regenerates `COVERAGE.tsv` without a driver call.
- Fixture v1 is a noncommutative `Int × Int × Int → Option Int` operation whose registered name is not derived from its id. Its second version computes a different result. The suite checks the old and new heads, the warmed old pin, and `FVDEP_BUILD_TRACE` before/after the version addition. Other entries exercise `ByteArray`, UTF-16, text, Nat, Int, Ordering and Version; launch specs cover `List UInt8`. Generated inputs compare to the independent Python fixture/RFC/SemVer references, not any product output table. Examples pin representation, decimal, UTF-8, padding, bounds, wrong values and exact canonical reply bytes.
- Git and bwrap wrappers are case-local trusted observations. MAIN confirmed the PATH seam for Git diagnostics and deadlines. The bwrap observer always execs the genuine binary with unchanged arguments. Git wrappers delegate successful local fetch/plumbing to Git, except for explicitly simulated diagnostics, timeout or transcript checkpoints. The 4,096-byte and 4 MiB path checks stop before materialization, so a local filesystem's absolute-path bound cannot confound the policy boundary. For a real bad mode, MAIN's ruling is fsck failure + no fallback when caught first; a shaped listing pins the exact L4 text separately.

## Contract readings and coverage limits

- MAIN ruled `fvdep oracle <target> --project <dir>`; interface §1 at the baseline left the position open. L4 `snapshotBytes` is the cumulative blob-size override; the fixed 1 MiB per-file edge is separate. L4's `treeEntries` counts the top listing and its recursive tree/blob records, not blobs alone.
- Pin the supplied text and named stages, not free wording: usage, U3 syntax/type details, most L4 control/cap failures, E2/E3 inconsistency reasons and the U5 typed deadline cause. Public `invalid` reasons follow U4 B3: check string type, canonical spelling and placement; do not prescribe their free text. V4's error index advances by driver rank; the contract does not fix zero- versus one-based numbering. L5's record is checked against canonical J text, allowing one final LF because the file terminator is not stated.
- MAIN left E5's exact zeta-size count open until U5b-O: `decodeNodes=1` refusal and a default-success control, not exact `n`/`n+1`. Q3 cannot force an X5 refusal through the command: it can inject a result, not an export. Q4 `lake test` and fuzz `export-decode` own direct X5 coverage. `X.profile-text` retains one genuine-source probe outside that seam: an oversized Lean literal intended to exceed the export profile. Its export outcome remains unverified until the command exists. MAIN's Q4 tests also own the record-level Git and wire validation matrices, proofs and campaigns.
- `requestBytes`, `stagingBytes`, `batchBytes`, Git capture and tree/byte caps get inclusive boundaries. Deadlines/locks get induced timeouts, not wall-clock equality. Q3 does not override the inherited U5 frame or per-file output caps, so this suite does not force a 128 MiB result or a SIGXFSZ evaluation. The stdin lifetime witness observes a drained pipe and one second with no output or evaluation while its writer stays open.
- No live remote, default network source, SSH authentication, crash-cut fsync ordering or syscall-complete tracing. The local snapshots test published bytes and observable ordering/cleanup; the wrappers are not evidence of actual remote timing or that no additional supervisor-internal read occurred.
