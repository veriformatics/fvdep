import Fvdep.Version
import FvdepCore.Plan

/-! Command-line dispatch as a pure function (`docs/interface.md` §1; contract U1 K2): the IO layer
writes the outcome verbatim, so these theorems are about what the binary prints + returns whenever
its writes succeed (a failed write → exit 2, `FvdepIO.run`). -/

namespace FvdepCore.Cli

/-- One invocation's whole observable result. -/
structure Outcome where
  stdout : String
  stderr : String
  exit : UInt32
  deriving Repr, DecidableEq

/-- Human-facing usage text (CLI help). -/
def usage : String :=
  "Usage: fvdep <command> [<arguments>]\n\n" ++
    "Checks Lean implementations against fvdep's formal specifications.\n\n" ++
    "Commands:\n" ++
    "  help [<command>]  Show this help, or the help for one command.\n\n" ++
    "Options:\n" ++
    "  --help            Show this help.\n" ++
    "  --version         Show the fvdep version.\n"

/-- Success: `out` on stdout, nothing on stderr, exit 0. -/
def ok (out : String) : Outcome := ⟨out, "", 0⟩

/-- A call outside the grammar: usage on stderr, nothing on stdout, exit 2. -/
def usageError : Outcome := ⟨"", usage, 2⟩

/-- `--version`, `--help`, `help`, `help help`, `help --help`; anything else is a usage error. -/
def run : List String → Outcome
  | ["--version"] => ok s!"fvdep {Fvdep.version}\n"
  | ["--help"] | ["help"] | ["help", "help"] | ["help", "--help"] => ok usage
  | _ => usageError

/-- Every invocation writes one stream alone: exit 0 with stderr empty, or exit 2 with usage on
stderr + stdout empty. -/
theorem run_streams (args : List String) :
    ((run args).exit = 0 ∧ (run args).stderr = "") ∨
      ((run args).exit = 2 ∧ (run args).stdout = "" ∧ (run args).stderr = usage) := by
  unfold run
  split <;> simp [ok, usageError]

/-- The output effects an outcome's plan performs: stdout, then stderr, each when nonempty. -/
def outputs (o : Outcome) : List (Eff × Response) :=
  (if o.stdout.isEmpty then [] else [(.out o.stdout, .done)]) ++
    (if o.stderr.isEmpty then [] else [(.err o.stderr, .done)])

/-- Stderr (when nonempty), then the exit code. -/
def emitErr (o : Outcome) : Plan UInt32 :=
  if o.stderr.isEmpty then .pure o.exit else .step (.err o.stderr) fun _ => .pure o.exit

/-- An outcome as a plan (contract U2 X5): stdout, then stderr (each when nonempty), then its exit
code. -/
def emit (o : Outcome) : Plan UInt32 :=
  if o.stdout.isEmpty then emitErr o else .step (.out o.stdout) fun _ => emitErr o

/-- The whole command line as a plan: `main` = `FvdepIO.execute (plan args)`. -/
def plan (args : List String) : Plan UInt32 := emit (run args)

/-- A completed run of the plan performs exactly the outcome's outputs + ends with its exit code; it
never reads or replaces a file. -/
theorem plan_complete (args : List String) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (plan args) evs (some code) ↔ evs = outputs (run args) ∧ code = (run args).exit := by
  unfold plan
  generalize run args = o
  unfold emit emitErr outputs
  cases o.stdout.isEmpty <;> cases o.stderr.isEmpty <;>
    simp [Plan.runs_step_iff, Plan.runs_pure_iff, Plan.fits_out, Plan.fits_err, eq_comm]
  case false.false =>
    constructor
    · rintro ⟨_, _, rfl, rfl, _, _, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨_, _, rfl, rfl, _, _, rfl, rfl, rfl, rfl⟩
  case false.true =>
    constructor
    · rintro ⟨_, _, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  case true.false =>
    constructor
    · rintro ⟨_, _, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- An interrupted run performs a prefix of the outcome's outputs. -/
theorem plan_interrupted (args : List String) (evs : List (Eff × Response)) :
    Plan.Runs (plan args) evs none → evs <+: outputs (run args) := by
  unfold plan
  generalize run args = o
  unfold emit emitErr outputs
  cases o.stdout.isEmpty <;> cases o.stderr.isEmpty <;>
    simp [Plan.runs_step_iff, Plan.runs_pure_iff, Plan.fits_out, Plan.fits_err] <;>
    rintro (h | h) <;>
    simp_all

end FvdepCore.Cli
