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

/-! Core regressions (contract U2 E3, E5, P7, P9): named cases from reviewer-2's counterexamples. -/

namespace Core

open FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status

def seg : Seg := ⟨⟨0, by decide⟩, []⟩

def modId : ModuleId := ⟨seg, seg, []⟩

def commit : Commit := ⟨List.replicate 40 ⟨0, by decide⟩, by decide⟩

def decl : Decl := ⟨modId, ⟨1, 0, 0⟩, some .fn, .proof, some "Impl.f", some "Proof.eq"⟩

def request : RequestKey := ⟨decl, "spec", some "impl", some "proof", none⟩

def profile : Profile := ⟨"qualified-v1", ["propext", "Classical.choice", "Quot.sound"]⟩

def key : ChallengeKey := ⟨request, commit, profile, "statement"⟩

/-- Phases 0–2 passed; the statement did not match. -/
def statementFailed : List Observation :=
  [Obs.implProfile none, .phase1 (.ok "e1"), .phase2 "e1" (.ok "e2"),
        .statement "e1" "e2" false].map
    fun o => ⟨key, o⟩

def base : FvdepCore.Evidence.Result := result key statementFailed

def diffKey : ChallengeKey :=
  { key with
    request :=
      { request with
        decl :=
          { decl with
            kind := .differential
            shape := none
            impl := none
            proof := none }
        implSources := none
        proofSources := none
        adapter := some "adapter" } }

def comparison : Observation :=
  ⟨diffKey, .compare "adapter" "encode" "00" (.mismatch "wrong" "right")⟩

def common : Common := ⟨request, commit, profile.id, .required, "now"⟩

/-- An empty manifest + a lock with one entry: the files disagree. -/
def emptyManifest : Manifest := ⟨commit, []⟩

def extraLock : Lock := ⟨commit, [.proof common "e1" "e2"]⟩

def outOfDateNamed : LockState → Bool
  | .outOfDate cs => !cs.isEmpty
  | _ => false

def cases : List (String × (Unit → Bool)) :=
  [("core: a failed statement is NOT PROVEN with statement_mismatch", fun _ =>
      match base with
      | .verdict .notProven rs => rs.any (·.code == .statementMismatch)
      | _ => false),
    ("core E3: an observation bound to other exports never changes the result", fun _ =>
      result key (statementFailed ++ [⟨key, .graph "other-e1" "other-e2" true⟩]) == base),
    ("core E5: a protocol violation keeps the failed phase's reasons", fun _ =>
      match base, result key (statementFailed ++ [⟨key, .graph "e1" "e2" true⟩]) with
      | .verdict .notProven rs, .infra cause ns => cause.code == .internal && ns == rs
      | _, _ => false),
    ("core E3: an identical comparison counts once", fun _ =>
      result diffKey [comparison, comparison] == result diffKey [comparison]),
    ("core P7: files that disagree → development status exit 1, no manifest module too", fun _ =>
      statusExit .development emptyManifest extraLock ⟨[]⟩ [] == .negative),
    ("core P7: files that disagree → required status exit 1, no manifest module too", fun _ =>
      statusExit .required emptyManifest extraLock ⟨[]⟩ [] == .negative),
    ("core P9: an export-only lock difference names its change", fun _ =>
      outOfDateNamed (lockState (some (.proof common "e1" "e2")) (.proof common "e1'" "e2"))),
    ("core P9: a policy-only lock difference names its change", fun _ =>
      outOfDateNamed
        (lockState (some (.proof common "e1" "e2"))
          (.proof { common with policy := .development } "e1" "e2")))]

end Core

/-! Compiled-code smoke for the JSON codec (contract U3 J3, J5): the proofs cover the definitions,
these run the compiled C, incl. the error-path loops over 10^6 siblings (stack safety). -/

namespace Json

open FvdepCore.Json

def text (s : String) : ByteArray := s.toUTF8

/-- `decode` names this duplicate-key site. -/
def siteIs (s : String) (site : List PathSeg × String) : Bool :=
  match decode (text s) with
  | .error (.duplicateKey got) => got == site
  | _ => false

/-- 10^6 integers, then an object repeating a key. -/
def longArray : String :=
  "[" ++ String.intercalate "," (List.replicate 1000000 "0") ++ ",{\"a\":1,\"a\":2}]"

/-- An object with 10^6 distinct keys + one late repeat of `k500000`. -/
def flatObject : String :=
  "{" ++ String.intercalate "," ((List.range 1000000).map fun i => s!"\"k{i}\":0") ++
    ",\"k500000\":1}"

def cases : List (String × (Unit → Bool)) :=
  [("json: J3 site example 1: {\"a\":{\"b\":1,\"b\":2},\"a\":3} → ([], a)", fun _ =>
      siteIs "{\"a\":{\"b\":1,\"b\":2},\"a\":3}" ([], "a")),
    ("json: J3 site example 2 → ([1], c)", fun _ =>
      siteIs "[{\"x\":1},{\"y\":1,\"y\":2,\"c\":3,\"c\":4}]" ([.index 1], "c")),
    ("json: a nested site names its key + index path", fun _ =>
      siteIs "{\"p\":[{\"q\":{\"z\":0,\"z\":1}}]}" ([.key "p", .index 0, .key "q"], "z")),
    ("json: an escaped alias repeats its key", fun _ => siteIs "{\"a\":1,\"\\u0061\":2}" ([], "a")),
    ("json: decode → canonical value; print → canonical text; decode ∘ print = id", fun _ =>
      match decode (text "{ \"b\" : [1, -2, \"\\u00e9\"], \"a\" : null }") with
      | .ok v =>
        (print v).data == (text "{\"a\":null,\"b\":[1,-2,\"é\"]}").data &&
          match decode (print v) with
          | .ok w => w == v
          | .error _ => false
      | .error _ => false),
    ("json: a site after 10^6 array elements (no stack overflow)", fun _ =>
      siteIs longArray ([.index 1000000], "a")),
    ("json: a late repeat among 10^6 object keys", fun _ => siteIs flatObject ([], "k500000"))]

end Json

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
    ([check "cli: --version prints exactly \"fvdep <version>\" + LF on stdout, rc 0" fun _ =>
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
              check "cli: usage starts with the usage line + names every command and option"
                fun _ =>
                usage.startsWith "Usage: fvdep <command>" &&
                  ["help [<command>]", "--help", "--version"].all fun s =>
                    (usage.splitOn s).length > 1,
              check s!"cli: {generated.length} generated argument lists match the contract table"
                fun _ => generated.all fun args => run args == expected args,
              check "cli: generated lists reach every outcome class" fun _ =>
                [0, 2].all fun rc => generated.any fun args => (run args).exit == rc] ++
            (Core.cases ++ Json.cases).map fun c => check c.1 c.2).mapM
        id
  let slowest := results.foldl (fun a r => if r.ms > a.ms then r else a) ⟨"none", true, 0⟩
  let failed := (results.filter (!·.ok)).length
  IO.println s!"slowest: {slowest.name} ({slowest.ms} ms)"
  IO.println s!"tests: {results.length - failed} passed, {failed} failed"
  return failed.toUInt32
