import FvdepCore.Build
import FvdepCore.Evidence
import FvdepCore.Manifest
import FvdepCore.Sandbox

/-! A phase's pure parts (contract `docs/contracts/U5-sandbox.md` P1, P5, P8): the compile argv,
each step's verdict from what the supervisor observed, the driver that stops at the first step
that does not pass, + the phase observation. Running a step = residue (`FvdepIO.Phase`). -/

namespace FvdepCore.Phase

open FvdepCore.Build FvdepCore.Sandbox FvdepCore.Evidence

/-- A step of a phase (P1, P4): one module's compile, the roots checks, the export. -/
inductive Step where
  | compile (module : String)
  | consumerRoots
  | libraryRoots
  | exportStep
  deriving DecidableEq, Repr

/-- The step's child as the frame records it (R8). -/
inductive Child where
  | exited (code : Nat)
  | signaled (signal : Nat)
  | notStarted (reason : String)
  deriving DecidableEq, Repr

/-- The helper's exit code for its child's status (R8). -/
def Child.helperExit : Child → Nat
  | .exited c => c
  | .signaled n => 128 + n
  | .notStarted _ => 127

/-- What descriptor 4 delivered (R3, R8). -/
inductive Frame where
  | missing
  | invalid
  | overflow
  | ok (child : Child) (complete : Bool)
  deriving DecidableEq, Repr

/-- What the supervisor observed of one step: bwrap's outcome (R6), the frame, whether the step hit
a size cap (a tmpfs full in the helper's sample after the child, or the export over its cap), + the
step's first diagnostic (B1, presentation). -/
structure StepResult where
  outcome : Outcome
  frame : Frame
  exhausted : Bool
  diagnostic : String
  deriving DecidableEq, Repr

/-- A step's verdict (P5). -/
inductive Verdict where
  | pass
  | failed (reason : String)
  | infra (code : Infra) (detail : String)
  deriving DecidableEq, Repr

/-- P5: a step's verdict. Infrastructure (never a verdict on the input): setup failure, a
protocol violation, the deadline, a missing or invalid frame, a frame over its cap, a child status
the helper's exit code contradicts, a size cap hit (whatever the child's exit code), a signal death,
a child that never started, an absent library root. The input's own failure: a child exiting
nonzero (Lean refusing the input), an incomplete artifact family. -/
def stepVerdict (s : Step) (r : StepResult) : Verdict :=
  match r.outcome with
  | .setupFailed d => .infra .sandboxSetup d
  | .protocol => .infra .sandboxSetup "the step reported two exit codes"
  | .timedOut => .infra .io "the phase deadline was exceeded"
  | .exited n =>
    match r.frame with
    | .missing | .invalid => .infra .io "the step helper failed"
    | .overflow => .infra .io "the step's outputs exceeded their cap"
    | .ok child complete =>
      if child.helperExit != n then .infra .io "the step helper failed"
      else
        if r.exhausted then .infra .io "the step exceeded a size cap"
        else
          match child with
          | .signaled k => .infra .io s!"the step was killed by signal {k}"
          | .notStarted why => .infra .io s!"the step did not start: {why}"
          | .exited 0 => if complete then .pass else .failed "a build output is missing"
          | .exited _ =>
            if s == .libraryRoots then .infra .io "the library does not define a required constant"
            else .failed r.diagnostic

/-- P8: run `steps` in order; the first step whose verdict is not `pass` stops the phase (later
steps never run) + is returned with its verdict; `none` = every step passed. -/
def drive {m : Type → Type} [Monad m] (exec : Step → m StepResult) :
    List Step → m (Option (Step × Verdict))
  | [] => pure none
  | s :: rest => do
    let r ← exec s
    match stepVerdict s r with
    | .pass =>
      drive exec rest
    | v =>
      pure (some (s, v))

/-- P5: phase 1's observation from its driver's outcome + its export's digest. -/
def observe1 (outcome : Option (Step × Verdict)) (e1 : Digest) : Obs :=
  match outcome with
  | none => .phase1 (.ok e1)
  | some (_, .failed reason) => .phase1 (.failed reason)
  | some (_, .infra code detail) => .infra code detail
  | some (_, .pass) => .infra .io "internal: a passing step stopped the phase"

/-- P5: phase 2's observation, bound to the e1 it was built on. -/
def observe2 (e1 : Digest) (outcome : Option (Step × Verdict)) (e2 : Digest) : Obs :=
  match outcome with
  | none => .phase2 e1 (.ok e2)
  | some (_, .failed reason) => .phase2 e1 (.failed reason)
  | some (_, .infra code detail) => .infra code detail
  | some (_, .pass) => .infra .io "internal: a passing step stopped the phase"

/-! ## P1 compile argv -/

/-- Module `A.B`'s relative path stem `A/B` (U3 T3 names: plain components, no `/`). -/
def stem (module : String) : String := module.map fun c => if c == '.' then '/' else c

/-- S2: the source files a digest frames + a step compiles: each module's `A/B.lean` + its bytes,
read once. -/
def sourceFiles (modules : List (String × ByteArray)) : List (String × ByteArray) :=
  modules.map fun m => (stem m.1 ++ ".lean", m.2)

/-- P1 / T2: a module's compile argv: the recipe's command + flags, its three output files under
`/fvdep/work/out`, its source as `./A/B.lean` (never read as an option). -/
def compileArgv (r : Recipe) (module : String) : List String :=
  r.argv ++ compileFlags r ++
    ["-o", "/fvdep/work/out/" ++ stem module ++ ".olean", "-i",
      "/fvdep/work/out/" ++ stem module ++ ".ilean", "-c",
      "/fvdep/work/out/" ++ stem module ++ ".c", "./" ++ stem module ++ ".lean"]

/-- P2: the artifact family a module's header implies. -/
def family (isModule : Bool) (module : String) : List String :=
  let p := stem module
  (if isModule then
      [p ++ ".olean", p ++ ".olean.server", p ++ ".olean.private", p ++ ".ir", p ++ ".ir.sig"]
    else [p ++ ".olean"]) ++
    [p ++ ".ilean", p ++ ".c"]

/-! ## S1 project snapshot: the decision per path component -/

/-- T3 `sourceBytes`: the supported checking inputs (not the spec's domain) — one source file's
bytes + a snapshot's, over its implementation and proof modules together. -/
structure SourceLimits where
  fileBytes : Nat := 1048576
  totalBytes : Nat := 16777216
  deriving DecidableEq, Repr

/-- A path component's file type as `fstat` reports it. -/
inductive Kind where
  | directory
  | regular
  | fifo
  | socket
  | charDevice
  | blockDevice
  | link
  | other (mode : Nat)
  deriving DecidableEq, Repr

/-- Linux's `st_mode & S_IFMT` values (`<sys/stat.h>`). -/
def Kind.ofMode : Nat → Kind
  | 0o040000 => .directory
  | 0o100000 => .regular
  | 0o010000 => .fifo
  | 0o140000 => .socket
  | 0o020000 => .charDevice
  | 0o060000 => .blockDevice
  | 0o120000 => .link
  | m => .other m

/-- What `openat` + `fstat` answered for one path component (S1). -/
inductive Opened where
  | error (errno : Nat)
  | file (kind : Kind) (size : Nat)
  deriving DecidableEq, Repr

/-- S1: why the snapshot refuses a module (its text: `FvdepIO.Snapshot.causeText`). -/
inductive Refusal where
  | notModuleName
  | listedTwice
  | unopened (errno : Nat)
  | unread (errno : Nat)
  | kind (k : Kind)
  | fileOver (size cap : Nat)
  | totalOver (total cap : Nat)
  | grewFile (cap : Nat)
  | grewTotal (cap : Nat)
  deriving DecidableEq, Repr

/-- S1: the snapshot's step at one path component. -/
inductive Snap where
  | descend
  | read (cap : Nat)
  | refuse (r : Refusal)
  deriving DecidableEq, Repr

/-- S1: the step at one path component (`leaf` = the module's file) from what `openat` + `fstat`
answered + the bytes the snapshot already holds (`used`): a directory on the way → descend; the leaf
a regular file within the per-file cap + the remaining total → read at most that much; anything
else (an open error — a link, a missing name, a socket —, a FIFO or device, a directory as the leaf,
another file on the way) → refuse. -/
def snapDecide (l : SourceLimits) (used : Nat) (leaf : Bool) : Opened → Snap
  | .error n => .refuse (.unopened n)
  | .file k size =>
    if leaf then
      if k == .regular then
        if l.fileBytes < size then .refuse (.fileOver size l.fileBytes)
        else
          if l.totalBytes < used + size then .refuse (.totalOver (used + size) l.totalBytes)
          else .read (min l.fileBytes (l.totalBytes - used))
      else .refuse (.kind k)
    else if k == .directory then .descend else .refuse (.kind k)

/-- S1: a leaf read under `cap` delivered `n` bytes (the read stops once past `cap`: more = the file
grew after `fstat`, or never ends) → the snapshot's new total, else the refusal naming the cap that
bound the read. -/
def snapRead (l : SourceLimits) (used cap n : Nat) : Except Refusal Nat :=
  if n ≤ cap then .ok (used + n)
  else
    if l.fileBytes ≤ l.totalBytes - used then .error (.grewFile l.fileBytes)
    else .error (.grewTotal l.totalBytes)

/-- S1: the first listed module (implementation, then proof) outside U3 T3's component grammar
(`[A-Za-z_][A-Za-z0-9_']*`, dot-separated) or listed twice — decided before any path is opened. -/
def snapNames (modules : List String) : Option (String × Refusal) := go [] modules
where go (seen : List String) : List String → Option (String × Refusal)
    | [] => none
    | m :: rest =>
      if !((m.splitOn ".").all fun c => FvdepCore.Manifest.isComponent c.toList) then
        some (m, .notModuleName)
      else if seen.contains m then some (m, .listedTwice) else go (m :: seen) rest

/-- S1: module `A.B`'s path components under the project directory, `.lean` on the last
(`["A", "B.lean"]`). -/
def snapPath (module : String) : List String := go (module.splitOn ".")
where go : List String → List String
    | [] => []
    | [c] => [c ++ ".lean"]
    | c :: cs => c :: go cs

/-! ## P1 the step plan, K2's import classes, P4's roots check (U5-D) -/

/-- P1: a phase's deadline window — every planned compile in K2's order, the consumer roots check,
the export. Phase 1's library roots check runs before it, outside the window: it imports library
modules alone, so no consumer code reaches its exit. -/
def steps (order : List String) : List Step := order.map .compile ++ [.consumerRoots, .exportStep]

/-- K2 + P5: how a phase reads one import of a consumer module. -/
inductive ImportClass where
  | listed
  | built
  | toolchain
  | library
  | absent
  deriving DecidableEq, Repr

/-- K2 + P5: an import `m` in a phase listing `listed` (phase 2: `built` = phase 1's modules), the
library holding a source for each module `present` names; the first match wins. `absent` = no source
anywhere: the consumer's own refusal (the phase's `failed`), never infrastructure. -/
def importClass (listed built : List String) (present : String → Bool) (m : String) : ImportClass :=
  if listed.contains m then .listed
  else
    if built.contains m then .built
    else
      if FvdepCore.Build.toolchainModule m then .toolchain
      else if present m then .library else .absent

/-- P4: the roots check's module — the export's imports, a blank line, one `#check @<root>` per
root ⇒ root k (from 1) sits on line `imports.length + 1 + k`. -/
def rootsSource (imports roots : List String) : String :=
  String.join (imports.map fun m => s!"import {m}\n") ++ "\n" ++
    String.join (roots.map fun r => s!"#check @{r}\n")

/-- P4: the root a roots-check diagnostic at `line` names (`rootsSource`'s layout). -/
def rootAt (imports roots : List String) (line : Nat) : Option String :=
  if imports.length + 1 < line then roots[line - imports.length - 2]? else none

end FvdepCore.Phase
