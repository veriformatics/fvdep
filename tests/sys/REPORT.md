## Batch 2 (F)

| item | verdict | evidence |
|---|---|---|
| F1–F6 blind batch | complete | 20/20 coverage rows, 2,817 cases; cell validator = 0 unknown |
| Stub I `a146394` | expected red | 2,116 FAIL / 701 PASS; every row committed separately |
| Per-case record | complete | `RESULTS.F.stubI.tsv`: id, row, expected, verdict, rerun command, output, reason, seconds, method, notes |
| Green ids | pending credit | `GREEN.F.stubI.txt`: 701 ids; J or a specified-behavior mutant owed |
| Fault controls | pass | all 13 logical operations + open/open64/openat/__open_2; scripted errno, retries, short/zero/overreported I/O, virtual reads, before/after crash + post-rename errno; root scope control |
| Sanitizer qualification | pass | runtime-only init; ASan/UBSan + leak controls fire; no suppression; leak detection enabled |
| Static/build checks | pass | GCC 15.2.0 `-Wall -Wextra -Werror`; Lean drivers compile; pinned Ruff/Pyrefly (0 diagnostics), ShellCheck; Lean layout (2 files, 160 lines, no over-width line) |
| Evidence validator | pass | `evidence.py --complete`: 2,817 unique source-defined ids, all groups complete, matching counts/methods/commands/greens; rc 0 |
| Frozen T | unchanged | all 12 hashes in MAIN's `FROZEN-T.sha256` match; rc 0 |
| J / real F / fuzz / full gate | not run | MAIN owns complementary-stub + real-code grading, mutation credit, `sys-actions` + the full gate |

Source = `docs/contracts/U3-codecs.md` F1–F6 + Acceptance evidence; `docs/interface.md` §2/§6; public Sys signatures/docstrings + `c/fvdep_sys.h`; MAIN's B2-1–8 semantic rulings. Fixed seed `0xF4DE6F02` = `4108218114`; `FVDEP_TEST_SEED` overrides exploration. No alternate seed run. F5 interpreter cases = U8, outside this batch.

### Run + evidence

From `/home/eturkes/Projects/fvdep/.scratch/worktrees/tester-4`:

```sh
tools/vflab-run bash tests/sys/run.sh
tools/vflab-run bash tests/sys/run.sh --case F.read.primary-secondary --full
tools/vflab-run python3 -I tests/sys/evidence.py --complete
```

`run.sh` builds the public dev driver, the extra API driver, the fault library + the native/sanitizer harnesses. It creates one owned gate-workspace directory + one private `f6.*` child of `/srv/data/fvdep/sys-test` (provisioned by `tools/vflab-provision.sh`; on a host without `/srv/data/fvdep` the `filesystem=zfs` case reports SKIP by name). It removes both on exit. `--full` prints the complete selected case observation; normal result cells above 2,400 UTF-8 bytes carry SHA-256, byte count + a prefix. Assertions compare complete values before abbreviation.

Recorded I invocation, per coverage row:

```sh
tools/vflab-run env FVDEP_SYS_REPORT=tests/sys/RESULTS.F.stubI.tsv \
  FVDEP_SYS_LABEL=stubI bash tests/sys/run.sh --row <row-id> --append
```

Each row returned rc 1 (failed assertions on I). `tests/sys/grade-I.sh` collected the row, ran `evidence.py --freeze`, then committed coverage/results/greens on `wt/tester-4`. It stops on changed directives, missing RESULT, setup failure or another branch. Evidence-source checkpoint = `f549257`; coordinator = `5584a71`; final row = `d9cb13d`. The row commits record their exact commands + rcs. Assertions/oracles stayed fixed during that 19-row batch.

Repeated `evidence.py --freeze --complete` leaves all three evidence files byte-identical (`cmp`, rc 0). Aggregate: 2,817 cases, 2,116 FAIL / 701 PASS. Sum of recorded case times = 37.110 s (excludes builds + per-row controls; descriptive, not a performance promise).

Requested validator:

```sh
awk -F '\t' 'NR>1 && ($3=="unknown" || $4=="unknown" || $5=="unknown" || $6=="unknown") {n++} END {print n+0}' tests/sys/COVERAGE-F.tsv
```

Output = `0`. `COVERAGE-F.tsv` has 20 rows; `RESULTS.F.stubI.tsv` has 2,817 cases; the green list has 701 ids.

### Oracles + domain

- Independent F2/F3 trace predicates check phase order, create ownership, descriptor identity, bounds, retry budgets + resets, close once, temp attempts, rename as the sole target-path touch, cleanup order + the reported primary/secondary errors. Error expectations come from the contract, not observations of F. A fixed-error/no-syscall stub cannot pass an errno case by returning the chosen errno alone.
- Errno matrix = 13 logical operations × slots 1–133 + 5 seeded positive values (1,794 cases). Named exceptions: EINTR retries, create/EEXIST next temp, open-read/ENOENT absence, flock/EWOULDBLOCK busy. The generated errno values test preservation; they do not claim every number is a naturally occurring errno for every syscall.
- Payloads exercise empty/nonempty writes, every byte value, read sizes across 1 MiB, prefix failures, zero EOF, short progress + two 64-EINTR runs, write offset/count + unsigned-overflow bounds. Strings exercise Unicode, control characters, NUL rejection, reserved basenames, 0–512 modes + large Nat bounds, MODE/N grammar, slot-state + early-stdin stops.
- Crash cases use a one-byte replacement: its 8 interposed protocol calls each receive a before + after `_exit(99)` cut, for both absent + present targets. The test requires the cut to be reached (no vacuous old/new pass), checks exact old/new bytes + names every leftover temp. This is process-interruption evidence, not power-loss evidence.
- Foreign temps are physically created using the child PID while its leading `wait` blocks. Symlink cases keep both the foreign temp link + its victim intact; replacing a target link replaces the link itself.
- Lock contention uses the successful-flock trace as readiness, then a second process. Tests cover busy/no action, ordinary region release, SIGKILL release, path aliases, one action/value, exception propagation, permanent empty metadata + B2-8's ignored close failure after a completed action.
- Native guard tests check live/closed finalization, persistent closed state, forced descriptor-number reuse + blocking ownership. Eight public-API race runs each schedule 16 write/sync tasks against close. They check joined outcomes, exact complete successful writes, one close + no syscall after close. These are bounded schedules, not exhaustive interleaving exploration.
- The native C harness calls the public shim/guard header alone. Plain runs check one libc attempt, exact flags/mode/count/fd + effects, errno identity, input borrowing + bounds. GCC ASan/UBSan runs cover vectors/bounds + guard lifecycle. The Lean runtime/shared libraries + the fault interposer are not sanitizer-instrumented.
- Virtual read streams test exactly 2^30 bytes + one byte over it without a giant JSON response. The extra driver returns length + first/middle/last samples. Large-stream payload verification is sampled; smaller read cases compare every returned byte. I refuses before reading, so neither large-stream behavior nor real F's memory/time cost was measured here.
- Gate filesystem reports `ext2/ext3`; `/srv/data/fvdep` reports `zfs`. Both test roots were created. Their F integration cases are red on I; this batch does not claim that the real persistence policy passed on either filesystem. Final cleanup control created one matching ZFS child (expected/observed 1), removed it, then observed 0 remaining task-prefix directories.
- A target deadline is 90 s/case; lock readiness is bounded. Timeouts would be reported as infrastructure observations, not proof of a functional diagnosis. No timeout occurred on I. Root paths + child PIDs normalize only in reporting after complete assertions.

### Sanitizer initialization + canaries

B2-10a held. The raw C harness calls no Lean-compiled function. `native.c` initializes `lean_initialize_runtime_module` + `lean_initialize_thread`, then pairs `lean_finalize_thread`; its worker thread also pairs initialization/finalization. Initial full Init/kernel setup exposed unrelated persistent GMP/C++ allocations; runtime-only setup removes that residue without a suppression or a disabled check.

All C sanitizer targets use GCC `-fsanitize=address,undefined -fno-omit-frame-pointer` with the same `native.c` + `c/fvdep_sys.c` and Lean runtime link flags in `build.sh`. `native-leak-canary` adds `leak-canary.c` + `--wrap=fvdep_sys_open_file`: the wrapper calls the real export and deliberately leaks one 8,193-byte owned malloc allocation.

Controller environment:

```text
ASAN_OPTIONS=detect_leaks=1:abort_on_error=1
UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1
LSan suppression file: none
```

Commands below run through `tools/vflab-run` after `bash tests/sys/build.sh`; `<owned-dir>` is a fresh test-owned directory. Recorded return codes are Python `Popen.returncode` (SIGABRT = -6; a shell reports 134):

| executable + arguments | rc | observation |
|---|---:|---|
| `tests/sys/.build/native runtime-thread <owned-dir>` | 0 | allocation + worker-thread control passes |
| `tests/sys/.build/native-asan runtime-thread <owned-dir>` | 0 | same control, no sanitizer finding |
| `tests/sys/.build/san-control-address clean` | 0 | clean control |
| `tests/sys/.build/san-control-address asan` | -6 | AddressSanitizer fires on the planted out-of-bounds access |
| `tests/sys/.build/san-control-undefined clean` | 0 | clean control |
| `tests/sys/.build/san-control-undefined ubsan` | 1 | UBSan fires on planted signed overflow |
| `tests/sys/.build/san-control-address leak` | -6 | LSan fires on an owned malloc leak |
| `tests/sys/.build/native-leak-canary create <owned-dir>` | -6 | LSan identifies `owned_leak`, 8,193 bytes through the shim-entry path |

Every row's run qualified these controls first. Leaks inside Lean's small-object pool remain outside LSan's view. No F memory-safety or leak result is claimed from the runtime-only control; F's sanitizer assertions are red on I and await the real-code run.

### Green on I

All 701 ids are in `GREEN.F.stubI.txt`; every green case is in F6-names:

| family | PASS | why |
|---|---:|---|
| named Path/Name values | 20 | I already satisfies these validation/preservation cases |
| generated Path/Name/Mode values | 128 | same pure API predicates |
| mode boundary/domain values | 518 | all 0–512 + selected large values |
| invalid count/mode/name + stateless CLI stops | 34 | the existing dev parser already refuses them |
| early stdin | 1 | the driver stops before the op |

I credit = 2,116/2,817. The 701 greens need J or MAIN's behavior-killing mutants; none is silently credited. Representative red: `F.crash.0.0.1` requires the first selected syscall + exit 99; I returns a fixed error without a syscall. This catches the stub without relying on a guessed error message.

## Questions

- No unresolved semantic ruling. B2-1–8 are encoded: exact optional record fields + enums; completed rc 0 / usage rc 2; ASCII N + octal MODE + exact stdin length; no unlink after reported rename success; unlink/ENOENT secondary after committed-but-reported-failed rename; secondary errno 4 after cleanup retry exhaustion; completed lock action result survives a lock-close error.
- Blindness disclosure: initial signature extraction displayed equation bodies of the dev command parser + Op/Cause string maps in this worktree's stub `tool/FvdepDev/Sys.lean`. B2-4 classifies that driver as the test interface, not the policy. No F policy/native body, real F, or fvapi implementation was opened. Expectations derive from the contract + directives; subsequent extraction hides equation bodies.
- LSP has no server for `.c` or `.lean`; GCC/Lean + Pyrefly supplied actual diagnostics. No J/real-F run, mutation credit, coverage-guided fuzz campaign, formal-proof audit or full gate here.

tester-DONE-4.2

## Batch 3 (robustness)

| check | verdict | evidence |
|---|---|---|
| R1 exception containment | pass | 10 injected exception sites → FAIL with type/message; 10 following cases → PASS; RESULT printed |
| R2 output-read audit | pass | absent bytes/size/mode/listings = None; absent trace = []; snapshots record vanished entries/root |
| R3 I verdict identity | pass | 2,817 ids; 0 verdict differences from `76a79ea`, including the three ruling ids |
| R4 J completion | pass | RESULT 2,817 cases; 712 PASS / 2,105 FAIL; rc 1; no abort |
| R5 checks | pass | pinned Ruff/Pyrefly (0 diagnostics), ShellCheck, Lean layout + evidence validator rc 0 |
| R6 alias names | pass | caller DIR text retained in the shared trace oracle; positive/negative synthetic traces |
| R7 close-before-rename | pass | both retained scripts checked against the F2 phase-order expectation |

`ROBUST-B3.tsv` = all seven rows resolved, validator 0. Source-repair checkpoint = `89337fd`. No real F or fvapi code was inspected; only tests/sys changed. The detached J worktree was used only at `12e82eb`, with tests/sys copied from wt/tester-4 HEAD, and receives no commit.

### Red → repaired runs

Unfixed `76a79ea` tests copied to J `12e82eb`:

```sh
tools/vflab-run bash tests/sys/run.sh --case F.errno.openLock.4
```

Build + controls passed; the suite then aborted with `FileNotFoundError` at the missing target read (rc 1, no RESULT). This is a harness defect, not a product finding.

Repaired full runs, in the I worktree and the own detached J worktree respectively:

```sh
tools/vflab-run env FVDEP_SYS_REPORT=tests/sys/RESULTS.F.stubI.tsv \
  FVDEP_SYS_LABEL=stubI bash tests/sys/run.sh
tools/vflab-run env FVDEP_SYS_REPORT=tests/sys/RESULTS.F.stubJ.tsv \
  FVDEP_SYS_LABEL=stubJ bash tests/sys/run.sh
```

- I: `RESULT 2817 cases; 701 PASS; 2116 FAIL`, rc 1; case wall 36.740 s. Every id's verdict equals `76a79ea`. `F.lock.contention.alias` + `F.cleanup.rename.13.{0,28}` remain FAIL.
- J: `RESULT 2817 cases; 712 PASS; 2105 FAIL`, rc 1; case wall 60.240 s. All 2,817 verdicts recorded in `RESULTS.F.stubJ.tsv`; every PASS id is in `GREEN.F.stubJ.txt`. Three no-flock contention waits reach their bounded readiness refusal (about 8 s each), not a suite abort.
- Builds + fault/runtime/sanitizer controls passed before both runs. These are assertion verdicts on fixed-value stubs, not findings on real F.

Validation:

```sh
tools/vflab-run python3 -I tests/sys/b3-check.py --canaries
tools/vflab-run python3 -I tests/sys/b3-check.py --compare-i --check-j
tools/vflab-run python3 -I tests/sys/evidence.py --complete
```

All return 0. The canary CLI deliberately returns 1 with `RESULT 20 cases; 10 PASS; 10 FAIL`. It covers assertion, missing-file, absence-value, missing-listing, JSON decode, subprocess error, timeout, permission, cleanup + render failures. It confirms that the next case still runs. Fixture mistakes/output rendering errors also become case failures; normal cancellation/process termination is not turned into a verdict.

### Repairs + source rulings

- B3-1/2: the per-case barrier catches ordinary exceptions from execution, cleanup + reporting; reasons include the exception class + message. Output bytes/stat/mode/listing reads treat absence as a value. Snapshot/trace readers tolerate files or directories disappearing between listing and reading. Other read errors are case failures, not suite aborts. Expected bytes/values + all other assertions stay unchanged.
- B3-4, `F.lock.contention.alias`: the error expectation already used `<root>/alias/.fvdep-writer.lock`; the shared trace oracle incorrectly checked the canonical root's lock path. It now takes the caller's DIR for open/unlink paths. The busy/contention criterion is unchanged. The synthetic alias trace passes; substituting a canonicalized open path fails.
- B3-5, `F.cleanup.rename.13.0`: the script remains rename/errno5 + first-close/posterrno13. F2 closes before rename, so that close failure is the primary `(close, temp, errno13)`; unlink succeeds; secondary is empty; rename never runs.
- B3-5, `F.cleanup.rename.13.28`: same pre-rename close primary; the scripted cleanup unlink/errno28 becomes its sole secondary. The rename rule remains unreachable. Both scripts + expectations are checked by the canaries. No closing step is invented after a failed rename.
- B3-6: F.records.* and canonical key-order expectations remain unchanged.
- B3-7: the native-shim opcode has an explicit string type guard; contention initializes its event list before the bounded wait. Ruff/Pyrefly remain clean.

No real-F rerun, mutation campaign, fuzz campaign or full gate is claimed in B3. The B2 sanitizer coverage limits remain in force. The stub-J green list is an observation, not automatic credit.

tester-DONE-4.3
