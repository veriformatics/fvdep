import FvdepCore.Sandbox

/-! Specs for a sandbox step (contract `docs/contracts/U5-sandbox.md` R1 + R6), written from the
contract + bwrap 0.11.1's manual apart from `FvdepCore.Sandbox`'s code: how bwrap reads an argument
list (each option by its name, then exactly its values; `--` ends the options; `--size` binds to
the `--tmpfs` after it), which operations make storage writable, + R6's precedence. -/

namespace FvdepAudit.Sandbox.Spec

open FvdepCore.Sandbox

/-- bwrap's reading of an argument list over fvdep's option subset: the operations in order + the
command after `--`; an option outside the subset or a missing value → `none`. `acc` = the
operations read so far, newest first. -/
def readOps : List String → List Op → Option (List Op × List String)
  | "--" :: cmd, acc => some (acc.reverse, cmd)
  | "--unshare-all" :: r, acc => readOps r (.unshareAll :: acc)
  | "--unshare-user" :: r, acc => readOps r (.unshareUser :: acc)
  | "--disable-userns" :: r, acc => readOps r (.disableUserns :: acc)
  | "--die-with-parent" :: r, acc => readOps r (.dieWithParent :: acc)
  | "--new-session" :: r, acc => readOps r (.newSession :: acc)
  | "--cap-drop" :: "ALL" :: r, acc => readOps r (.capDropAll :: acc)
  | "--clearenv" :: r, acc => readOps r (.clearenv :: acc)
  | "--setenv" :: k :: v :: r, acc => readOps r (.setenv k v :: acc)
  | "--ro-bind" :: s :: d :: r, acc => readOps r (.roBind s d :: acc)
  | "--symlink" :: t :: d :: r, acc => readOps r (.symlink t d :: acc)
  | "--size" :: n :: "--tmpfs" :: d :: r, acc =>
    (FvdepCore.Ids.parseNat n.toList).bind fun b => readOps r (.sizedTmpfs b d :: acc)
  | "--proc" :: d :: r, acc => readOps r (.proc d :: acc)
  | "--dev" :: d :: r, acc => readOps r (.dev d :: acc)
  | "--remount-ro" :: d :: r, acc => readOps r (.remountRo d :: acc)
  | "--chdir" :: d :: r, acc => readOps r (.chdir d :: acc)
  | "--json-status-fd" :: n :: r, acc =>
    (FvdepCore.Ids.parseNat n.toList).bind fun fd => readOps r (.jsonStatusFd fd :: acc)
  | _, _ => none

/-- bwrap's reading of a whole argument list (residue `bwrap`: the real tool reads fvdep's
arguments this way; G1 + the smoke test it). -/
def bwrapRead (args : List String) : Option (List Op × List String) := readOps args []

/-- A mount operation: it changes the sandbox's file tree. -/
def isMount : Op → Bool
  | .roBind _ _ | .symlink _ _ | .sizedTmpfs _ _ | .proc _ | .dev _ | .remountRo _ => true
  | _ => false

/-- A writable storage mount the sandbox keeps writable: a sized tmpfs (`/dev`'s tmpfs is bwrap's,
covered by its read-only remount). -/
def writableStorage : Op → Bool
  | .sizedTmpfs _ _ => true
  | _ => false

/-- The environment operations, in order. -/
def isEnv : Op → Bool
  | .clearenv | .setenv _ _ => true
  | _ => false

/-- The destination an operation names inside the sandbox. -/
def dest? : Op → Option String
  | .roBind _ d | .symlink _ d | .sizedTmpfs _ d | .proc d | .dev d | .remountRo d | .chdir d =>
    some d
  | _ => none

/-- The layout's destinations (contract R layout). -/
def layout : List String :=
  ["/usr", "/lib", "/lib64", "/bin", "/fvdep/sysroot", "/fvdep/step", "/fvdep/src", "/fvdep/lib",
    "/fvdep/phase1", "/fvdep/prior", "/fvdep/work", "/tmp", "/proc", "/dev", "/"]

/-- U5 T3 + U7 part B L1: a step's limits are usable, over the effective values (the per-file +
export caps after their defaults): every bound ≥ 1, each tmpfs size within bwrap's cap, eight files
at the per-file cap fit the work tmpfs, the export within the per-file cap. -/
def LimitsValid (l : Limits) : Prop :=
  1 ≤ l.deadline ∧
    1 ≤ l.tmpBytes ∧
    1 ≤ l.diagnosticBytes ∧
    1 ≤ l.frameBytes ∧
    l.workBytes ≤ tmpfsMax ∧
    l.tmpBytes ≤ tmpfsMax ∧
    1 ≤ l.fileCap ∧ 8 * l.fileCap ≤ l.workBytes ∧ 1 ≤ l.exportCap ∧ l.exportCap ≤ l.fileCap

end FvdepAudit.Sandbox.Spec
