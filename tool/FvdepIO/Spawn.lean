/-! The sandbox spawn shim's externs (contract `docs/contracts/U5-sandbox.md` R2, R4, R8; C
`c/fvdep_spawn.c`, ledger residue `sandbox-spawn`): one mechanism each, errno answered at once; a
string with an interior NUL (which C would cut there) → `EINVAL`. The policy over them =
`FvdepIO.Sandbox` (supervisor) + `FvdepIO.Step` (helper). -/

namespace FvdepIO.Spawn

/-- R2: `bwrap` spawned on four pipes → `#[pid, stdout, stderr, status, output]` (read ends). -/
@[extern "fvdep_spawn_bwrap"]
opaque bwrap (path : @& String) (argv : @& Array String) : IO (Except Nat (Array Nat))

/-- `poll` for input → each descriptor's `revents`. -/
@[extern "fvdep_spawn_poll"]
opaque poll (fds : @& Array Nat) (timeout : UInt32) : IO (Except Nat (Array Nat))

/-- `kill(pid, sig)` for the supervisor's own child: pid 0 or one that reads as negative (-1 = every
process it may signal) → `EINVAL`. -/
@[extern "fvdep_spawn_kill"]
opaque kill (pid sig : UInt32) : IO (Except Nat Unit)

/-- `waitpid` → `#[0, exit code]` | `#[1, signal]`. -/
@[extern "fvdep_spawn_wait"]
opaque wait (pid : UInt32) : IO (Except Nat (Array Nat))

@[extern "fvdep_step_nodump"]
opaque nodump : Unit → IO (Except Nat Unit)

@[extern "fvdep_step_channel"]
opaque channel (fd : UInt32) : IO (Except Nat Unit)

@[extern "fvdep_step_core_limit"]
opaque coreLimit (limit : UInt32) : IO (Except Nat Unit)

@[extern "fvdep_step_file_limit"]
opaque fileLimit (bytes : UInt64) : IO (Except Nat Unit)

/-- The helper's child: `argv` through `PATH`, stdout to `stdoutPath` unless empty → `#[pid]`. -/
@[extern "fvdep_step_spawn"]
opaque spawn (argv : @& Array String) (stdoutPath : @& String) : IO (Except Nat (Array Nat))

/-- `kill(-1, SIGKILL)`, refused (`EPERM`) unless the caller is PID 2 (a fresh PID namespace). -/
@[extern "fvdep_step_killall"]
opaque killAll : Unit → IO (Except Nat Unit)

/-- `statvfs` → `#[blocks available]`. -/
@[extern "fvdep_step_statvfs"]
opaque available (path : @& String) : IO (Except Nat (Array Nat))

/-- A regular file opened without following a link → `#[fd, size]`; another type = `.error 0`. -/
@[extern "fvdep_step_open_regular"]
opaque openRegular (path : @& String) : IO (Except Nat (Array Nat))

/-- The text of the errno values a step reports, else the number. -/
def errnoText : Nat → String
  | 0 => "not a regular file"
  | 1 => "Operation not permitted"
  | 2 => "No such file or directory"
  | 8 => "Exec format error"
  | 9 => "Bad file descriptor"
  | 12 => "Cannot allocate memory"
  | 13 => "Permission denied"
  | 17 => "File exists"
  | 20 => "Not a directory"
  | 21 => "Is a directory"
  | 22 => "Invalid argument"
  | 28 => "No space left on device"
  | 38 => "posix_spawn cannot close inherited descriptors here (glibc before 2.34)"
  | 40 => "Too many levels of symbolic links"
  | n => s!"errno {n}"

end FvdepIO.Spawn
