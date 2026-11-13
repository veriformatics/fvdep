import FvdepCore

/-! `lake test` driver (contract U1 K3): PASS/FAIL per case, the slowest case, exit = failures.
Generated cases use a fixed seed (printed; `FVDEP_TEST_SEED` overrides it for exploration), so a
red reruns from committed state. -/

open FvdepCore.Cli

/-- One case: name, verdict, wall-clock (ms). -/
structure Result where
  name : String
  ok : Bool
  ms : Nat

def check (name : String) (ok : Unit → Bool) : IO Result := do
  let t0 ← IO.monoMsNow
  let held := ok ()
  let t1 ← IO.monoMsNow
  IO.println s!"{if held then "PASS" else "FAIL"} {name}"
  return ⟨name, held, t1 - t0⟩

/-- splitmix64: next output + next state. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- Tokens near the grammar's edges: real names, case + spacing variants, options, empties. -/
def tokens : Array String :=
  #["help", "--help", "--version", "-h", "-v", "version", "check", "--json", "", " ", "HELP",
    "help ", "--", "-", "fvdep", "--version=1", "--Help", "x"]

/-- `count` argument lists of 0–3 tokens from `seed`. -/
def argLists (seed : UInt64) (count : Nat) : List (List String) :=
  Id.run do
    let mut s := seed
    let mut out := []
    for _ in [0:count] do
      let (r, s') := splitmix s
      s := s'
      let mut args := []
      for _ in [0:(r % 4).toNat] do
        let (t, s'') := splitmix s
        s := s''
        args := tokens[(t % tokens.size.toUInt64).toNat]! :: args
      out := args :: out
    return out

/-- The contract's outcome for `args` (K2 + `docs/interface.md` §1), stated as a table. -/
def expected (args : List String) : Outcome :=
  if args == ["--version"] then ⟨s!"fvdep {Fvdep.version}\n", "", 0⟩
  else
    if [["--help"], ["help"], ["help", "help"], ["help", "--help"]].contains args then
      ⟨usage, "", 0⟩
    else ⟨"", usage, 2⟩

def main : IO UInt32 := do
  let seed : UInt64 ←
    do
      match (← IO.getEnv "FVDEP_TEST_SEED").bind String.toNat? with
      | some n =>
        pure n.toUInt64
      | none =>
        pure 0x5EEDF0DE00000001
  IO.println s!"seed {seed}"
  let generated := argLists seed 2000
  let results ←
    [check "cli: --version prints exactly \"fvdep <version>\" + LF on stdout, rc 0" fun _ =>
              run ["--version"] == ⟨s!"fvdep {Fvdep.version}\n", "", 0⟩,
            check "cli: help + --help print usage on stdout, rc 0" fun _ =>
              run ["help"] == ⟨usage, "", 0⟩ && run ["--help"] == ⟨usage, "", 0⟩,
            check "cli: help <command> + <command> --help print usage on stdout, rc 0" fun _ =>
              run ["help", "help"] == ⟨usage, "", 0⟩ && run ["help", "--help"] == ⟨usage, "", 0⟩,
            check "cli: no argument → usage on stderr, rc 2" fun _ => run [] == ⟨"", usage, 2⟩,
            check "cli: unknown command, unknown option, extra argument → usage on stderr, rc 2"
              fun _ =>
              run ["frobnicate"] == ⟨"", usage, 2⟩ && run ["--frobnicate"] == ⟨"", usage, 2⟩ &&
                run ["--version", "extra"] == ⟨"", usage, 2⟩ &&
                run ["help", "help", "x"] == ⟨"", usage, 2⟩,
            check "cli: usage starts with the usage line + names every command and option" fun _ =>
              usage.startsWith "Usage: fvdep <command>" &&
                ["help [<command>]", "--help", "--version"].all fun s =>
                  (usage.splitOn s).length > 1,
            check s!"cli: {generated.length} generated argument lists match the contract table"
              fun _ => generated.all fun args => run args == expected args,
            check "cli: generated lists reach every outcome class" fun _ =>
              [0, 2].all fun rc => generated.any fun args => (run args).exit == rc].mapM
        id
  let slowest := results.foldl (fun a r => if r.ms > a.ms then r else a) ⟨"none", true, 0⟩
  let failed := (results.filter (!·.ok)).length
  IO.println s!"slowest: {slowest.name} ({slowest.ms} ms)"
  IO.println s!"tests: {results.length - failed} passed, {failed} failed"
  return failed.toUInt32
