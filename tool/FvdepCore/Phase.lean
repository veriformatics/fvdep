import FvdepCore.Build
import FvdepCore.Evidence
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

end FvdepCore.Phase
