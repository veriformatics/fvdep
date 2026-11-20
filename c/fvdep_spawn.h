/* Sandbox spawn shim (docs/contracts/U5-sandbox.md R2, R4, R8; ledger residue `sandbox-spawn`):
 * mechanism alone, each export answering errno at once (no retry, no policy): results are
 * `Except Nat (Array Nat)` (`.error errno` | `.ok values`) or `Except Nat Unit`. Which descriptors
 * carry what, deadlines, retention + framing stay in Lean (`FvdepIO.Sandbox`, `FvdepIO.Step`).
 * Lean ABI: `b_lean_obj_arg` = borrowed. */
#ifndef FVDEP_SPAWN_H
#define FVDEP_SPAWN_H

#include <lean/lean.h>
#include <stdint.h>

/* Supervisor (R2): four pipes, then posix_spawn(path, argv, envp = {}) with stdin = /dev/null,
 * stdout, stderr, 3, 4 = the pipes' write ends, every descriptor ≥ 5 closed, signal mask empty +
 * every catchable signal at its default; → .ok #[pid, stdout, stderr, status (3), output (4)] (the
 * read ends, close-on-exec). */
LEAN_EXPORT lean_obj_res fvdep_spawn_bwrap(b_lean_obj_arg path, b_lean_obj_arg argv);
/* Git (U5b L3–L4, residue `git`): posix_spawnp(file, argv, envp) in its own process group, stdin =
 * the file at stdin_path ("" = /dev/null), stdout + stderr = pipes, every descriptor ≥ 3 closed →
 * .ok #[pid, stdout, stderr] (the read ends, close-on-exec). */
LEAN_EXPORT lean_obj_res fvdep_spawn_proc(b_lean_obj_arg file, b_lean_obj_arg argv,
                                          b_lean_obj_arg envp, b_lean_obj_arg stdin_path);
/* killpg(pgid, sig); pgid ≤ 1 or the caller's own group → .error EINVAL */
LEAN_EXPORT lean_obj_res fvdep_spawn_killpg(uint32_t pgid, uint32_t sig);
/* poll(fds, timeout ms) → .ok #[revents per fd] */
LEAN_EXPORT lean_obj_res fvdep_spawn_poll(b_lean_obj_arg fds, uint32_t timeout);
/* kill(pid, sig) */
LEAN_EXPORT lean_obj_res fvdep_spawn_kill(uint32_t pid, uint32_t sig);
/* waitpid(pid, 0) → .ok #[0, exit code] | .ok #[1, signal] */
LEAN_EXPORT lean_obj_res fvdep_spawn_wait(uint32_t pid);

/* Helper (R8), inside the sandbox. */
/* prctl(PR_SET_DUMPABLE, 0) */
LEAN_EXPORT lean_obj_res fvdep_step_nodump(lean_obj_arg unit);
/* fd = an inherited pipe (no FD_CLOEXEC yet, S_ISFIFO) → fcntl(fd, F_SETFD, FD_CLOEXEC); anything
 * else (absent, opened by this process, another file type) → .error EBADF */
LEAN_EXPORT lean_obj_res fvdep_step_channel(uint32_t fd);
/* setrlimit(RLIMIT_CORE, {limit, limit}) */
LEAN_EXPORT lean_obj_res fvdep_step_core_limit(uint32_t limit);
/* setrlimit(RLIMIT_FSIZE, {bytes, bytes}) */
LEAN_EXPORT lean_obj_res fvdep_step_file_limit(uint64_t bytes);
/* posix_spawnp(argv[0], argv, environ) with stdout = open(stdout_path, O_WRONLY | O_CREAT | O_EXCL |
 * O_NOFOLLOW, 0644) unless the path is empty, signal mask empty + defaults → .ok #[pid] */
LEAN_EXPORT lean_obj_res fvdep_step_spawn(b_lean_obj_arg argv, b_lean_obj_arg stdout_path);
/* kill(-1, SIGKILL): every process the caller may signal but itself + the namespace's init; refused
 * (EPERM) unless the caller is PID 2, i.e. the helper inside a fresh PID namespace */
LEAN_EXPORT lean_obj_res fvdep_step_killall(lean_obj_arg unit);
/* statvfs(path) → .ok #[f_bavail] */
LEAN_EXPORT lean_obj_res fvdep_step_statvfs(b_lean_obj_arg path);
/* open(path, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC) + fstat → .ok #[fd, size] for a
 * regular file; a link = .error ELOOP; any other file type: closed, .error 0 */
LEAN_EXPORT lean_obj_res fvdep_step_open_regular(b_lean_obj_arg path);

#endif
