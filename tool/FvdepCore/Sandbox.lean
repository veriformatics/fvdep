import FvdepCore.Ids

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

end FvdepCore.Sandbox
