import FvdepCore.Step
import FvdepIO.Spawn
import FvdepIO.Sys

/-! The step helper `fvdep-step` (contract `docs/contracts/U5-sandbox.md` R8; ledger residue
`step-helper`): pid 2 of every sandbox step. It runs its child, kills every other process of the
step, then frames the child's status + every regular file under `/fvdep/work/out` (`frameOf`) onto
descriptor 4 and exits with the child's code. `StepMain.main` = `main`. -/

namespace FvdepIO.Step

open FvdepCore.Step FvdepCore.Phase

/-- R8's request: output directories + the child's stdout file (paths under `/fvdep/work`), then
the child's argv. -/
structure Request where
  mkdirs : List String := []
  stdoutPath : Option String := none
  fileBytes : Option Nat := none
  argv : List String := []

/-- `[--mkdir <dir>]… [--stdout <path>] [--file-bytes <n>] -- <argv>`, every path safe (`safePath`),
1 ≤ `n` ≤ 2^64 − 2: `RLIMIT_FSIZE` = `n` exactly (a `u64`, 2^64 − 1 = `RLIM_INFINITY` = no limit;
past it `toUInt64` wraps). -/
def plan (args : List String) : Except String Request := go {} args
where go (r : Request) : List String → Except String Request
    | "--mkdir" :: d :: rest =>
      if safePath d then go { r with mkdirs := r.mkdirs ++ [d] } rest
      else .error s!"unsafe directory {d}"
    | "--stdout" :: p :: rest =>
      if r.stdoutPath.isNone && safePath p then go { r with stdoutPath := some p } rest
      else .error s!"bad --stdout {p}"
    | "--file-bytes" :: n :: rest =>
      match n.toNat? with
      | some b =>
        if r.fileBytes.isNone && 0 < b && b < 2 ^ 64 - 1 then go { r with fileBytes := some b } rest
        else .error s!"bad --file-bytes {n}"
      | none => .error s!"bad --file-bytes {n}"
    | "--" :: a :: rest => .ok { r with argv := a :: rest }
    | _ =>
      .error "usage: fvdep-step [--mkdir <dir>]… [--stdout <path>] [--file-bytes <n>] -- <argv>"

def work : System.FilePath := "/fvdep/work"

def warn (m : String) : IO Unit := do
  let err ← IO.getStderr
  err.putStr s!"fvdep-step: {m}\n"
  err.flush

/-- The child's status (`waitpid`; `EINTR` = 4 retried). -/
partial def waitFor (pid : UInt32) : IO Child := do
  match ← Spawn.wait pid with
  | .ok #[1, n] =>
    return .signaled n
  | .ok #[_, c] =>
    return .exited c
  | .ok _ =>
    return .notStarted "waitpid answered no status"
  | .error 4 =>
    waitFor pid
  | .error e =>
    return .notStarted s!"waitpid: {Spawn.errnoText e}"

/-- R8: the child, stdout inherited or written to its file; a refused spawn = not started. -/
def runChild (r : Request) : IO Child := do
  let out :=
    match r.stdoutPath with
    | some p => (work / p).toString
    | none => ""
  match ← Spawn.spawn r.argv.toArray out with
  | .ok #[pid] =>
    waitFor pid.toUInt32
  | .ok _ =>
    return .notStarted "posix_spawn answered no process"
  | .error e =>
    return .notStarted (Spawn.errnoText e)

/-- A descriptor's bytes to its end (`EINTR` retried). -/
partial def readAll (fd : UInt32) (acc : ByteArray) : IO (Except Nat ByteArray) := do
  match ← FvdepIO.Sys.Native.read fd 65536 with
  | .error 4 =>
    readAll fd acc
  | .error e =>
    return .error e
  | .ok chunk =>
    if chunk.isEmpty then
      return .ok acc
    else
      readAll fd (acc ++ chunk)

/-- A regular file's bytes through a descriptor opened without following a link (a link →
`ELOOP`, another type → `0`). -/
def readRegular (path : System.FilePath) : IO (Except Nat ByteArray) := do
  match ← Spawn.openRegular path.toString with
  | .ok #[fd, _] =>
    let r ← readAll fd.toUInt32 .empty
    let _ ← FvdepIO.Sys.Native.close fd.toUInt32
    return r
  | .ok _ =>
    return .error 0
  | .error e =>
    return .error e

/-- R8: every regular file under `/fvdep/work/out/<rel>` with its path relative to `out`; a link,
special file or unreadable entry → not framed, named on stderr. Runs after every other process of
the step is killed: nothing changes the tree underneath. -/
partial def collect (rel : String) : IO (List (String × ByteArray)) := do
  let dir := if rel.isEmpty then work / "out" else work / "out" / rel
  match ← dir.readDir.toBaseIO with
  | .error e =>
    unless rel.isEmpty do
      warn s!"not framed: {rel} ({e})"
    return []
  | .ok entries =>
    let mut files := []
    for e in entries do
      let r := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
      match ← e.path.symlinkMetadata.toBaseIO with
      | .error err =>
        warn s!"not framed: {r} ({err})"
      | .ok md =>
        match md.type with
        | .dir =>
          files := files ++ (← collect r)
        | .file =>
          match ← readRegular e.path with
          | .ok b =>
            files := files ++ [(r, b)]
          | .error n =>
            warn s!"not framed: {r} ({Spawn.errnoText n})"
        | _ =>
          warn s!"not framed: {r} (a link or special file)"
    return files

/-- R8: no free block in the helper's sample after the child. -/
def full (path : String) : IO Bool := do
  match ← Spawn.available path with
  | .ok #[0] =>
    return true
  | _ =>
    return false

/-- All of `b` from `off` onto `fd` (`EINTR` retried); `false` = not delivered. -/
partial def writeAll (fd : UInt32) (b : ByteArray) (off : Nat) : IO Bool := do
  if b.size ≤ off then
    return true
  match ← FvdepIO.Sys.Native.write fd b off.toUSize (b.size - off).toUSize with
  | .ok 0 =>
    return false
  | .ok n =>
    writeAll fd b (off + n)
  | .error 4 =>
    writeAll fd b off
  | .error _ =>
    return false

/-- R8 in order: non-dumpable; descriptor 4 = the inherited pipe, made close-on-exec (else no frame:
never another file at that number); `RLIMIT_CORE` = 1 (the kernel then skips a `core_pattern` pipe)
+ `RLIMIT_FSIZE` = `--file-bytes` (a file past it ends its writer by `SIGXFSZ`), both inherited; the
output directories; the child; every other process of the step killed; the frame; the child's
code. -/
def execute : Except String Request → IO UInt32
  | .error m => do
    warn m
    return 125
  | .ok r => do
    match ← Spawn.nodump () with
    | .error e =>
      warn s!"prctl: {Spawn.errnoText e}"
    | .ok _ =>
      pure ()
    let channel ← Spawn.channel 4
    match ← Spawn.coreLimit 1 with
    | .error e =>
      warn s!"setrlimit: {Spawn.errnoText e}"
    | .ok _ =>
      pure ()
    if let some n := r.fileBytes then
      match ← Spawn.fileLimit n.toUInt64 with
      | .error e =>
        warn s!"setrlimit RLIMIT_FSIZE: {Spawn.errnoText e}"
      | .ok _ =>
        pure ()
    for d in r.mkdirs do
      try
        IO.FS.createDirAll (work / d)
      catch e =>
        warn s!"mkdir {d}: {e}"
    let child ← runChild r
    -- `kill(-1)` answers `ESRCH` (3) when no other process is left: the usual end of a step.
    match ← Spawn.killAll () with
    | .error 3 | .ok _ =>
      pure ()
    | .error e =>
      warn s!"kill-all refused: {Spawn.errnoText e}"
    let status : Status := ⟨child, ← full "/fvdep/work", ← full "/tmp"⟩
    let files ← collect ""
    match channel with
    | .ok _ =>
      unless ← writeAll 4 (frameOf status files) 0 do
        warn "the frame could not be written"
    | .error _ =>
      warn "no descriptor 4: no frame"
    return child.helperExit.toUInt32

def main (args : List String) : IO UInt32 := execute (plan args)

end FvdepIO.Step
