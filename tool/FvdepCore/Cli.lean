import Fvdep.Version
import FvdepCore.Index.Command
import FvdepCore.Oracle.Command
import FvdepIO.Sha256

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
    "  help [<command>]  Show this help, or the help for one command.\n" ++
    "  index [--check]   Write index.json for a library working copy, or check it.\n" ++
    "  oracle <id>@<version>\n" ++
    "                    Answer adapter protocol requests with a library spec.\n\n" ++
    "Options:\n" ++
    "  --help            Show this help.\n" ++
    "  --version         Show the fvdep version.\n"

/-- Human-facing usage text of `fvdep index` (contract U4 C9 help). -/
def indexUsage : String :=
  "Usage: fvdep index [--check]\n\n" ++
    "Builds the fvdep library in the current directory and writes index.json.\n" ++
    "Run this command in a library working copy: a directory that holds\n" ++
    "lean-toolchain and Fvdep/Registry.lean.\n\n" ++
    "Options:\n" ++
    "  --check  Compare index.json with the library. Do not change index.json.\n" ++
    "           Exit code 1 if they differ.\n" ++
    "  --help   Show this help.\n"

/-- Success: `out` on stdout, nothing on stderr, exit 0. -/
def ok (out : String) : Outcome := ⟨out, "", 0⟩

/-- A call outside the grammar: usage on stderr, nothing on stdout, exit 2. -/
def usageError : Outcome := ⟨"", usage, 2⟩

/-- `--version`, `--help`, `help`, `help help`, `help --help`, `index --help`, `help index`,
`oracle --help`, `help oracle`; any other `oracle` line = its usage error; anything else is a usage
error (`fvdep index [--check]` + a well-formed `fvdep oracle` itself = `plan`). -/
def run : List String → Outcome
  | ["--version"] => ok s!"fvdep {Fvdep.version}\n"
  | ["--help"] | ["help"] | ["help", "help"] | ["help", "--help"] => ok usage
  | ["index", "--help"] | ["help", "index"] => ok indexUsage
  | ["oracle", "--help"] | ["help", "oracle"] => ok Oracle.Command.usage
  | "oracle" :: _ => ⟨"", Oracle.Command.usage, 2⟩
  | _ => usageError

/-- The usage a failing command line gets: `oracle`'s own for an `oracle` line, else fvdep's. -/
def usageOf : List String → String
  | "oracle" :: _ => Oracle.Command.usage
  | _ => usage

/-- Every invocation writes one stream alone: exit 0 with stderr empty, or exit 2 with its usage on
stderr (`oracle`'s own for an `oracle` line) + stdout empty. -/
theorem run_streams (args : List String) :
    ((run args).exit = 0 ∧ (run args).stderr = "") ∨
      ((run args).exit = 2 ∧ (run args).stdout = "" ∧ (run args).stderr = usageOf args) := by
  unfold run
  split <;> simp_all [ok, usageError, usageOf]

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

/-- C4's digest function = H3's hash step (HACL*, residue `hacl-sha256`): over an entry's frame it
equals `FvdepIO.Hash.digest .entry` of the entry's closure files (`tool/Tests.lean`, by `rfl`). -/
def sha (b : ByteArray) : String := FvdepIO.Hash.sha256Hex b

/-- A well-formed `fvdep oracle` line: its target + `--project` (contract U5b E1 + P1), else
`none`. -/
def oracleArgs : List String → Option (Oracle.Target × Option String)
  | "oracle" :: rest =>
    (Oracle.Command.parseArgs rest).bind fun (t, p) => (Oracle.Target.parse t).map fun x => (x, p)
  | _ => none

/-- The whole command line as a plan: `main` = `FvdepIO.execute (plan args)`; `fvdep index
[--check]` (contract U4 C1) + a well-formed `fvdep oracle` (contract U5b O1, T's default limits) =
their own plans, every other command line = its outcome. -/
def plan (args : List String) : Plan UInt32 :=
  match args with
  | ["index"] => Index.Command.plan sha false
  | ["index", "--check"] => Index.Command.plan sha true
  | _ =>
    match oracleArgs args with
    | some (t, p) => Oracle.Command.plan sha {} t p
    | none => emit (run args)

/-- The command lines `plan` runs as its own plans: `fvdep index [--check]`, a well-formed
`fvdep oracle`. -/
def PlanArgs (args : List String) : Prop :=
  args = ["index"] ∨ args = ["index", "--check"] ∨ (oracleArgs args).isSome

/-- `fvdep index [--check]` runs the index plan with SHA-256 hex digests. -/
theorem plan_index :
    plan ["index"] = Index.Command.plan sha false ∧
      plan ["index", "--check"] = Index.Command.plan sha true := ⟨rfl, rfl⟩

/-- A well-formed `fvdep oracle` runs the oracle plan with SHA-256 hex digests + T's default
limits. -/
theorem plan_oracle (args : List String) (t : Oracle.Target) (p : Option String)
    (h : oracleArgs args = some (t, p)) : plan args = Oracle.Command.plan sha {} t p := by
  unfold plan
  split
  · simp [oracleArgs] at h
  · simp [oracleArgs] at h
  · simp [h]

/-- U5b O1's grammar: a well-formed `oracle` line = `oracle <target>`, or with one `--project <dir>`
on either side of the target (a first `--project` = the option), the target parsing (E1). -/
theorem oracleArgs_eq (args : List String) (t : Oracle.Target) (p : Option String) :
    oracleArgs args = some (t, p) ↔
      ∃ s,
        Oracle.Target.parse s = some t ∧
          (args = ["oracle", s] ∧ p = none ∨
            ∃ d,
              p = some d ∧
                (args = ["oracle", "--project", d, s] ∨
                  s ≠ "--project" ∧ args = ["oracle", s, "--project", d])) := by
  cases args with
  | nil => simp [oracleArgs]
  | cons a rest =>
    by_cases ha : a = "oracle"
    · subst ha
      simp only [oracleArgs, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq,
        List.cons.injEq, true_and]
      constructor
      · rintro ⟨⟨s, p'⟩, hp, x, hx, rfl, rfl⟩
        refine ⟨s, hx, ?_⟩
        match rest, hp with
        | [_], hp =>
          simp only [Oracle.Command.parseArgs, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact .inl ⟨rfl, rfl⟩
        | [a, b, c], hp =>
          simp only [Oracle.Command.parseArgs] at hp
          by_cases h1 : a = "--project"
          · subst h1
            simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            exact .inr ⟨b, rfl, .inl rfl⟩
          · have h1' : (a == "--project") = false := by simpa using h1
            simp only [h1', Bool.false_eq_true, ↓reduceIte] at hp
            by_cases h2 : b = "--project"
            · subst h2
              simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, rfl⟩ := hp
              exact .inr ⟨c, rfl, .inr ⟨h1, rfl⟩⟩
            · have h2' : (b == "--project") = false := by simpa using h2
              simp [h2'] at hp
        | [], hp => simp [Oracle.Command.parseArgs] at hp
        | [_, _], hp => simp [Oracle.Command.parseArgs] at hp
        | _ :: _ :: _ :: _ :: _, hp => simp [Oracle.Command.parseArgs] at hp
      · rintro ⟨s, hx, ⟨rfl, rfl⟩ | ⟨d, rfl, rfl | ⟨hs, rfl⟩⟩⟩
        · exact ⟨(s, none), rfl, t, hx, rfl, rfl⟩
        · exact ⟨(s, some d), by simp [Oracle.Command.parseArgs], t, hx, rfl, rfl⟩
        · have hs' : (s == "--project") = false := by simpa using hs
          exact ⟨(s, some d), by simp [Oracle.Command.parseArgs, hs'], t, hx, rfl, rfl⟩
    · have hne : ∀ r, a :: rest ≠ "oracle" :: r := fun r h => ha (List.cons.inj h).1
      constructor
      · intro h
        unfold oracleArgs at h
        split at h
        · rename_i r heq
          exact absurd heq (hne r)
        · cases h
      · rintro ⟨s, _, ⟨h, _⟩ | ⟨d, _, h | ⟨_, h⟩⟩⟩ <;> exact absurd h (hne _)

/-- An `oracle` line outside the grammar (`oracleArgs`), `oracle --help` aside: exit 2, `oracle`'s
usage on stderr, stdout empty (contract U5b O1; its plan performs that outcome: `plan_complete`). -/
theorem run_oracle_malformed (rest : List String) (help : rest ≠ ["--help"])
    (_ : oracleArgs ("oracle" :: rest) = none) :
    (run ("oracle" :: rest)).exit = 2 ∧
      (run ("oracle" :: rest)).stdout = "" ∧
      (run ("oracle" :: rest)).stderr = Oracle.Command.usage := by
  unfold run
  split <;> simp_all

theorem plan_outcome (args : List String) (h : ¬PlanArgs args) : plan args = emit (run args) := by
  unfold plan
  split
  · exact absurd (.inl rfl) h
  · exact absurd (.inr (.inl rfl)) h
  · match ho : oracleArgs args with
    | some _ => exact absurd (.inr (.inr (by simp [ho]))) h
    | none => rfl

/-- Outside `fvdep index [--check]` + a well-formed `fvdep oracle`, a completed run of the plan
performs exactly the outcome's outputs + ends with its exit code; it never reads or replaces a
file. -/
theorem plan_complete (args : List String) (hi : ¬PlanArgs args) (evs : List (Eff × Response))
    (code : UInt32) :
    Plan.Runs (plan args) evs (some code) ↔ evs = outputs (run args) ∧ code = (run args).exit := by
  rw [plan_outcome args hi]
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

/-- Outside `fvdep index [--check]` + a well-formed `fvdep oracle`, an interrupted run performs a
prefix of the outcome's outputs. -/
theorem plan_interrupted (args : List String) (hi : ¬PlanArgs args) (evs : List (Eff × Response)) :
    Plan.Runs (plan args) evs none → evs <+: outputs (run args) := by
  rw [plan_outcome args hi]
  generalize run args = o
  unfold emit emitErr outputs
  cases o.stdout.isEmpty <;> cases o.stderr.isEmpty <;>
    simp [Plan.runs_step_iff, Plan.runs_pure_iff, Plan.fits_out, Plan.fits_err] <;>
    rintro (h | h) <;>
    simp_all

end FvdepCore.Cli
