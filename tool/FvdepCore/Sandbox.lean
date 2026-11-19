import FvdepCore.Ids
import FvdepCore.Json.Decode

/-! A sandbox step's bwrap arguments + its outcome (contract `docs/contracts/U5-sandbox.md` R1, R5,
R6): pure. bwrap itself = residue `bwrap` (`FvdepAudit.Sandbox.Spec.bwrapRead` models how it reads
these arguments; G1 + the smoke test it against the real tool). -/

namespace FvdepCore.Sandbox

/-- The layout's read-only destinations below `/fvdep` (contract R layout). -/
inductive Mount where
  | sysroot
  | step
  | src
  | lib
  | phase1
  | prior
  deriving DecidableEq, Repr

def Mount.path : Mount → String
  | .sysroot => "/fvdep/sysroot"
  | .step => "/fvdep/step"
  | .src => "/fvdep/src"
  | .lib => "/fvdep/lib"
  | .phase1 => "/fvdep/phase1"
  | .prior => "/fvdep/prior"

/-- One bwrap operation: the subset fvdep emits (bwrap ≥ 0.8.0). No constructor opens a writable
host path, the network or an outside namespace. -/
inductive Op where
  | unshareAll
  | unshareUser
  | disableUserns
  | dieWithParent
  | newSession
  | capDropAll
  | clearenv
  | setenv (key value : String)
  | roBind (src dest : String)
  | symlink (target dest : String)
  | sizedTmpfs (bytes : Nat) (dest : String)
  | proc (dest : String)
  | dev (dest : String)
  | remountRo (dest : String)
  | chdir (dir : String)
  | jsonStatusFd (fd : Nat)
  deriving DecidableEq, Repr

/-- A number as bwrap reads it: decimal digits (`FvdepCore.Ids.decimal`, round trip proven). -/
def num (n : Nat) : String := String.ofList (FvdepCore.Ids.decimal n)

/-- The arguments of one operation: its option name, then exactly its values. -/
def Op.render : Op → List String
  | .unshareAll => ["--unshare-all"]
  | .unshareUser => ["--unshare-user"]
  | .disableUserns => ["--disable-userns"]
  | .dieWithParent => ["--die-with-parent"]
  | .newSession => ["--new-session"]
  | .capDropAll => ["--cap-drop", "ALL"]
  | .clearenv => ["--clearenv"]
  | .setenv k v => ["--setenv", k, v]
  | .roBind s d => ["--ro-bind", s, d]
  | .symlink t d => ["--symlink", t, d]
  | .sizedTmpfs n d => ["--size", num n, "--tmpfs", d]
  | .proc d => ["--proc", d]
  | .dev d => ["--dev", d]
  | .remountRo d => ["--remount-ro", d]
  | .chdir d => ["--chdir", d]
  | .jsonStatusFd n => ["--json-status-fd", num n]

/-- One step (R1): the read-only binds (host path, destination), the environment, the two tmpfs
sizes, the command the helper runs. -/
structure Spec where
  ro : List (String × Mount)
  env : List (String × String)
  workBytes : Nat
  tmpBytes : Nat
  argv : List String
  deriving DecidableEq, Repr

/-- The helper every step runs as its command (R8). -/
def helper : String := "/fvdep/step/fvdep-step"

/-- R1's namespace + process operations. -/
def isolation : List Op :=
  [.unshareAll, .unshareUser, .disableUserns, .dieWithParent, .newSession, .capDropAll]

/-- R1's environment: cleared, then exactly the spec's variables. -/
def envOps (s : Spec) : List Op := .clearenv :: s.env.map fun e => .setenv e.1 e.2

/-- R1's mounts: `/usr` + its three links, the spec's read-only binds at their layout paths, the
two sized tmpfs, `/proc`, `/dev`. -/
def mounts (s : Spec) : List Op :=
  [.roBind "/usr" "/usr", .symlink "usr/lib" "/lib", .symlink "usr/lib64" "/lib64",
      .symlink "usr/bin" "/bin"] ++
    s.ro.map (fun b => .roBind b.1 b.2.path) ++
    [.sizedTmpfs s.workBytes "/fvdep/work", .sizedTmpfs s.tmpBytes "/tmp", .proc "/proc",
      .dev "/dev"]

/-- R1's last operations: `/` + `/dev` read-only (bwrap's root + `/dev` are writable, unsized tmpfs
otherwise), the cwd, the status descriptor. -/
def finish : List Op := [.remountRo "/", .remountRo "/dev", .chdir "/fvdep/src", .jsonStatusFd 3]

/-- R1's operations, in bwrap's order. -/
def ops (s : Spec) : List Op := isolation ++ envOps s ++ mounts s ++ finish

/-- R1: the argument list fvdep passes to bwrap. -/
def bwrapArgs (s : Spec) : List String := (ops s).flatMap Op.render ++ "--" :: helper :: s.argv

/-! ## Outcome (R5, R6) -/

/-- One line bwrap writes on the status descriptor, as R5 reads it. -/
inductive StatusLine where
  | exitCode (code : Nat)
  | other
  deriving DecidableEq, Repr

/-- R6: how a step ended. -/
inductive Outcome where
  | exited (code : Nat)
  | timedOut
  | setupFailed (detail : String)
  | protocol
  deriving DecidableEq, Repr

def exitCodeOf : StatusLine → Option Nat
  | .exitCode n => some n
  | .other => none

/-- R6 in precedence order: one exit-code line → `exited` (a later deadline kill changes nothing);
two or more → `protocol`; none → `timedOut` when the supervisor killed the step, else
`setupFailed` with bwrap's first stderr line. -/
def classify (lines : List StatusLine) (killed : Bool) (firstErr : String) : Outcome :=
  match lines.filterMap exitCodeOf with
  | [n] => .exited n
  | [] => if killed then .timedOut else .setupFailed firstErr
  | _ :: _ :: _ => .protocol

/-- R5: bwrap's status lines, each decoded by J (a line J refuses = `other`): an object whose
`exit-code` member is a nonnegative integer → `exitCode`. -/
def statusLines (b : ByteArray) : List StatusLine :=
  (splitLines b).map fun l =>
    match FvdepCore.Json.decode l with
    | .ok v =>
      match v.get? "exit-code" with
      | some (.int n) => if 0 ≤ n then .exitCode n.toNat else .other
      | _ => .other
    | .error _ => .other
where
  /-- The bytes between line feeds (a final unterminated line kept). -/
  splitLines (b : ByteArray) : List ByteArray :=
    Id.run do
      let mut out := #[]
      let mut start := 0
      for i in [0:b.size] do
        if b[i]! == 0x0A then
          out := out.push (b.extract start i)
          start := i + 1
      if start < b.size then
        out := out.push (b.extract start b.size)
      return out.toList

/-! ## Limits (T3) -/

/-- T3: a step's limits (U5's defaults; U7 qualifies the production values under stated load):
the deadline in seconds, the two tmpfs sizes, the bytes a diagnostic stream keeps, the frame cap,
each ≥ 1 (`bwrap --size 0` = a setup failure), the tmpfs sizes ≤ `tmpfsMax`; `fileBytes` = every
step process's `RLIMIT_FSIZE` (default `workBytes / 8`, `fileCap`); `exportBytes` = the export's
cap (P4; default the per-file cap, `exportCap`: the export file is written through it). -/
structure Limits where
  deadline : Nat := 600
  workBytes : Nat := 1073741824
  tmpBytes : Nat := 268435456
  diagnosticBytes : Nat := 65536
  frameBytes : Nat := 268435456
  fileBytes : Option Nat := none
  exportBytes : Option Nat := none
  deriving DecidableEq, Repr

/-- The per-file cap a step runs under (`RLIMIT_FSIZE`). -/
def Limits.fileCap (l : Limits) : Nat := l.fileBytes.getD (l.workBytes / 8)

/-- P4's export cap (default: the per-file cap). -/
def Limits.exportCap (l : Limits) : Nat := l.exportBytes.getD l.fileCap

/-- bwrap's tmpfs size cap: bubblewrap 0.11.1 refuses a larger `--size` at setup (`--size (for
tmpfs) is limited to 9223372036854775807`), like `--size 0`. -/
@[noinline]
def tmpfsMax : Nat := 9223372036854775807

/-- T3's bounds + relation (A1): each tmpfs size ≤ `tmpfsMax`; the per-file cap ≥ 1 and 8 × it ≤
`workBytes` ⇒ a compile's artifact family (≤ 7 files) never fills `/fvdep/work`: a file past the cap
ends its writer by `SIGXFSZ` first (a signal death, P5's resource case); the export cap ≥ 1 and ≤
the per-file cap (the export is one file written under it) — `none` = holds, else the reason. -/
def Limits.check (l : Limits) : Option String :=
  if tmpfsMax < l.workBytes then
    some s!"--work-bytes {l.workBytes} is above bwrap's tmpfs cap {tmpfsMax}"
  else
    if tmpfsMax < l.tmpBytes then
      some s!"--tmp-bytes {l.tmpBytes} is above bwrap's tmpfs cap {tmpfsMax}"
    else
      if l.fileCap == 0 then some "the per-file cap is 0 (--work-bytes below 8)"
      else
        if l.workBytes < 8 * l.fileCap then
          some s!"--file-bytes {l.fileCap} is above --work-bytes / 8"
        else
          if l.exportCap == 0 then some "the export cap is 0"
          else
            if l.fileCap < l.exportCap then
              some s!"--export-bytes {l.exportCap} is above the per-file cap {l.fileCap}"
            else none

end FvdepCore.Sandbox
