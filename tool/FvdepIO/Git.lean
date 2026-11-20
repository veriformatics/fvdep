import FvdepIO.Spawn
import FvdepIO.Sys

/-! git as a process (contract `docs/contracts/U5b-oracle.md` L3–L4; ledger residue `git`): one run
= `git` spawned in its own process group with an exact environment + stdin from a file, stdout +
stderr pumped together (stdout kept to its cap, stderr's head), the group killed at the deadline
or past the stdout cap — only before the reap (an unreaped leader keeps its group id from reuse) —
then reaped. Decisions over the results = `FvdepCore.Library`. -/

namespace FvdepIO.Git

/-- `file` (through the caller's `PATH` when it holds no `/`) spawned in its own process group,
`envp` its whole environment, stdin = the file at `stdinPath` (`""` = `/dev/null`) →
`#[pid, stdout, stderr]` (read ends). -/
@[extern "fvdep_spawn_proc"]
opaque spawn (file : @& String) (argv envp : @& Array String) (stdinPath : @& String) :
    IO (Except Nat (Array Nat))

/-- `killpg(pgid, sig)` for a git child's own group: 0, 1, a value that reads as negative + the
caller's own group → `EINVAL`. -/
@[extern "fvdep_spawn_killpg"]
opaque killGroup (pgid sig : UInt32) : IO (Except Nat Unit)

/-- One git process as observed: its exit code (`none` = a signal ended it), whether the deadline
killed it, stdout (at most `outCap` bytes) + whether it passed that cap, stderr's first bytes. -/
structure Run where
  exit : Option Nat
  timedOut : Bool
  out : ByteArray
  outOver : Bool
  err : ByteArray

/-- Milliseconds the pipes get to close after the group kill (a member that left the group keeps
them open: closed here, never a hang). -/
def drainGrace : Nat := 5000

structure State where
  out : ByteArray := .empty
  over : Bool := false
  err : ByteArray := .empty
  killedAt : Option Nat := none
  timedOut : Bool := false

/-- A chunk of stdout (channel 0: kept while within `outCap`, else the over flag) or stderr (its
first `errCap` bytes). -/
def State.add (outCap errCap : Nat) (s : State) (ch : Nat) (chunk : ByteArray) : State :=
  if ch == 0 then
    if s.over || outCap < s.out.size + chunk.size then { s with over := true }
    else { s with out := s.out ++ chunk }
  else { s with err := s.err ++ chunk.extract 0 (errCap - s.err.size) }

/-- Both pipes read to their end; the deadline (monotonic ms) or the stdout cap kills the group
once, then the pipes drain for at most `drainGrace`. -/
partial def pump (pid : UInt32) (chans : Array (Nat × Nat)) (deadline outCap errCap : Nat)
    (s : State) : IO State := do
  if chans.isEmpty then
    return s
  let now ← IO.monoMsNow
  if let some t := s.killedAt then
    if t + drainGrace ≤ now then
      for (fd, _) in chans do
        discard <| FvdepIO.Sys.Native.close fd.toUInt32
      return s
  let s ←
    if s.killedAt.isNone && (deadline ≤ now || s.over) then
      do
        discard <| killGroup pid 9
        pure
            { s with
              killedAt := some now
              timedOut := !s.over }
    else
      pure s
  let wait := if s.killedAt.isSome then 1000 else min (deadline - now) 1000
  match ← FvdepIO.Spawn.poll (chans.map (·.1)) wait.toUInt32 with
  | .error 4 =>
    pump pid chans deadline outCap errCap s
  | .error e =>
    throw (IO.userError s!"poll: {FvdepIO.Spawn.errnoText e}")
  | .ok revents =>
    let mut s := s
    let mut left := #[]
    for (fd, ch) in chans, ev in revents do
      if ev == 0 then
        left := left.push (fd, ch)
      else
        match ← FvdepIO.Sys.Native.read fd.toUInt32 65536 with
        | .ok chunk =>
          if chunk.isEmpty then
            discard <| FvdepIO.Sys.Native.close fd.toUInt32
          else
            s := s.add outCap errCap ch chunk
            left := left.push (fd, ch)
        | .error 4 =>
          left := left.push (fd, ch)
        | .error _ =>
          discard <| FvdepIO.Sys.Native.close fd.toUInt32
    pump pid left deadline outCap errCap s

/-- `waitpid` with `EINTR` retried. -/
partial def reap (pid : UInt32) : IO (Except Nat (Array Nat)) := do
  match ← FvdepIO.Spawn.wait pid with
  | .error 4 =>
    reap pid
  | r =>
    return r

/-- `git` (`program`: `"git"` = through `PATH`) with `args`, the environment `env`, stdin from
`stdinPath`: stdout kept to `outCap` bytes, stderr's first `errCap`, the group killed at `deadline`
(monotonic ms) or past `outCap`, then reaped; `.error` = it could not start. -/
def run (program : String) (env args : List String) (stdinPath : String)
    (deadline outCap errCap : Nat) : IO (Except String Run) := do
  match ← spawn program (program :: args).toArray env.toArray stdinPath with
  | .error e =>
    return .error s!"git could not start: {FvdepIO.Spawn.errnoText e}"
  | .ok #[pid, o, e] =>
    let pid := pid.toUInt32
    let s ←
      tryCatch (pump pid #[(o, 0), (e, 1)] deadline outCap errCap {}) fun ex => do
          discard <| killGroup pid 9
          discard <| reap pid
          throw ex
    let exit :=
      match ← reap pid with
      | .ok #[0, c] => some c
      | _ => none
    return .ok
        { exit
          timedOut := s.timedOut
          out := s.out
          outOver := s.over
          err := s.err }
  | .ok _ =>
    return .error "git answered no process"

end FvdepIO.Git
