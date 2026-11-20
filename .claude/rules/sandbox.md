---
paths:
  - "c/fvdep_spawn.*"
  - "tool/FvdepIO/Spawn.lean"
  - "tool/FvdepIO/Step.lean"
  - "tool/FvdepIO/Sandbox.lean"
  - "tool/StepMain.lean"
  - "tests/isolation/**"
  - "tests/sandbox/**"
  - "tools/pidns-check.sh"
---

# Sandbox runner + step helper (contract `docs/contracts/U5-sandbox.md` R, G)

- `fvdep_step_killall` = `kill(-1, SIGKILL)` reaches every process of the caller's PID namespace it may signal: outside the step's fresh namespace that is every process of the login (vflab: fvapi's jobs + services share it) ⇒ the C export refuses (`EPERM`) unless `getpid() == 2` (the helper behind bwrap's init; in the host namespace PID 2 = kthreadd). Keep that guard in C, below every caller; the supervisor's `fvdep_spawn_kill` likewise refuses pid ≤ 0 (`EINVAL`: it signals its own bwrap child alone), + every string the shim hands the kernel refuses an interior NUL (`EINVAL`). `ESRCH` = no other process left, the usual end: never a warning (the step's stderr carries the helper's lines).
- `fvdep_spawn_killpg` (git's group kill, residue `git`) refuses in C a pgid ≤ 1 (0 = the caller's group, a value read as negative) + the caller's own group (`EINVAL`); its tests call it with signal 0, so a mutant dropping a guard sends nothing. A vflab job's PID namespace shows the caller's group as 0 ⇒ the own-group case runs under `setsid` (`fvdep-dev library killgroup self`).
- `fvdep-step` = its own executable: every script that runs steps builds `«fvdep-step»` by name (`extraDepTargets` on the runner's executable leaves a stale helper in place).
- vflab = one login shared with fvapi: every `tools/vflab-run` job = its own PID namespace + `RLIMIT_CORE` = 1 (`.claude/rules/gate.md`), and both suites' `run.sh` refuse a job sharing the host's namespace (`tools/pidns-check.sh`; CI runners pass) ⇒ the guarded suites run freely (stages `sandbox-suite`, `isolation`). Weakening the runner (stub, mutant, a dropped namespace) = `tests/isolation/mutants.py` alone: it re-checks containment, no mode crashes a process without `RLIMIT_CORE` = 1 (none reaches apport); announce each run to the fvapi session first, with `FVDEP_VFLAB_MEMORY=6G`.
- The helper takes descriptor 4 only as an inherited pipe (no `FD_CLOEXEC` + a FIFO): started without one, its own Lean runtime opens an io_uring at 4.
- Inside a step: bwrap adds `PWD` (= the cwd) at `--chdir`; `/usr/bin/{awk,editor,pager}` → `/etc/alternatives` = dangling (no `/etc`) ⇒ probes use sh, coreutils, bash, python3; python ignores `SIGXFSZ` (`EFBIG` past the per-file cap), coreutils + Lean die by it.
