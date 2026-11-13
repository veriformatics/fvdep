import Fvdep.Version

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

end FvdepCore.Cli
