import FvdepCore.Build
import FvdepCore.Doc
import FvdepCore.Sandbox
import FvdepCore.Step
import Lean.Data.Json

/-! The failure bundle's pure parts (contract `docs/contracts/U5-sandbox.md` B1, B2): B1's reason —
tested presentation, outside the claims (P5 classifies, never this text) —, B2's picks (which inputs
a bounded bundle omits, which bundles retention keeps) + `bundle.json`'s value. -/

namespace FvdepCore.Bundle

open FvdepCore.Json FvdepCore.Build

/-! ## B1 reason -/

/-- B1: one diagnostic as the pumps captured it (Lean's `--json` message or its text form). -/
structure Diag where
  file : Option String
  line : Option Nat
  message : String
  deriving DecidableEq, Repr

def firstLine (s : String) : String := (s.splitOn "\n").headD s

def dropPrefix (n : Nat) (s : String) : String := String.ofList (s.toList.drop n)

/-- B1: a `lean --json` line on stdout → its diagnostic when its severity is `error`. -/
def ofJson (line : String) : Option Diag := do
  let j ← (Lean.Json.parse line).toOption
  let sev ← (j.getObjValAs? String "severity").toOption
  guard (sev == "error")
  let message ← (j.getObjValAs? String "data").toOption
  let pos := (j.getObjVal? "pos").toOption
  return {
      file := (j.getObjValAs? String "fileName").toOption
      line := pos.bind fun p => (p.getObjValAs? Nat "line").toOption
      message }

/-- B1: a stderr line in Lean's text form `<path>:<line>:<col>: error[(<name>)]: <message>`. -/
def ofText (line : String) : Option Diag :=
  match line.splitOn ": error" with
  | head :: rest@(_ :: _) =>
    let tail := ": error".intercalate rest
    let message :=
      match tail.splitOn ": " with
      | _ :: m@(_ :: _) => ": ".intercalate m
      | _ => tail
    match (head.splitOn ":").reverse with
    | _ :: ln :: path@(_ :: _) =>
      some { file := some (":".intercalate path.reverse), line := ln.toNat?, message }
    | _ => none
  | _ => none

/-- B1: a path inside a step as the project names it — `./X` + `/fvdep/src/X` → `X`; an artifact
under `/fvdep/lib`, `/fvdep/phase1` or `/fvdep/prior` (`A/B.<ext>`) → its module `A.B`. -/
def mapPath (p : String) : String :=
  if p.startsWith "./" then dropPrefix 2 p
  else
    if p.startsWith "/fvdep/src/" then dropPrefix 11 p
    else
      match
        ["/fvdep/lib/", "/fvdep/phase1/", "/fvdep/prior/"].find? fun pre => p.startsWith pre with
      | some pre =>
        let rel := dropPrefix pre.length p
        ((rel.splitOn ".").headD rel).map fun c => if c == '/' then '.' else c
      | none => p

/-- B1: a phase's reason from its failing step's first error diagnostic — `<label> build failed
(<path>:<line>: <message>)`, `(<message>)` without a position, `(<tool> exited with code <n>)`
without any; the message = its first line; the path mapped first, interface §1's line rule last. -/
def reason (label : String) (d : Option Diag) (tool : String) (code : Nat) : String :=
  let inner :=
    match d with
    | some { file := some f, line := some n, message } => s!"{mapPath f}:{n}: {firstLine message}"
    | some d => firstLine d.message
    | none => s!"{tool} exited with code {code}"
  FvdepCore.Doc.escapeControls s!"{label} build failed ({inner})"

/-! ## B2 picks + record -/

/-- B2: the inputs a bounded bundle omits — the largest first (ties by path), until the kept total
fits `budget`. -/
def omitOrder (inputs : List (String × Nat)) (budget : Nat) : List String :=
  let sorted := inputs.mergeSort fun a b => b.2 < a.2 || (a.2 == b.2 && decide (a.1 ≤ b.1))
  let rec go (total : Nat) : List (String × Nat) → List String
    | [] => []
    | x :: xs => if total ≤ budget then [] else x.1 :: go (total - x.2) xs
  go (inputs.foldl (· + ·.2) 0) sorted

/-- B2: the bundles retention removes — all but the newest `keep` by (time, name). -/
def retainPick (bundles : List (String × Nat)) (keep : Nat) : List String :=
  let sorted := bundles.mergeSort fun a b => a.2 < b.2 || (a.2 == b.2 && decide (a.1 ≤ b.1))
  (sorted.take (sorted.length - keep)).map (·.1)

/-- B2: one required input of the failing step: its role (`src`, `lib`, `prior`:
`FvdepIO.Phase.inputsOf`), path under that role's directory, size + digest, whether its copy is in
the bundle. -/
structure Input where
  role : String
  path : String
  size : Nat
  sha256 : String
  kept : Bool
  deriving DecidableEq, Repr

/-- B2: `bundle.json` (schema 1): the toolchain, recipe + limits, the failing step (phase, kind,
module), the roots check's or export's request, a graph refusal's presence facts (each import → its
class), every required input. Complete iff every input is kept. -/
structure Record where
  recipe : Recipe
  limits : FvdepCore.Sandbox.Limits
  phase : Nat
  step : String
  module : String
  imports : List String
  roots : List String
  presence : List (String × String)
  inputs : List Input
  deriving DecidableEq, Repr

def Record.complete (r : Record) : Bool := r.inputs.all (·.kept)

def strs (xs : List String) : Value := .arr (xs.map .str)

def limitsValue (l : FvdepCore.Sandbox.Limits) : Value :=
  .obj
    [("deadline", .int l.deadline), ("diagnosticBytes", .int l.diagnosticBytes),
      ("exportBytes", .int l.exportCap), ("fileBytes", .int l.fileCap),
      ("frameBytes", .int l.frameBytes), ("tmpBytes", .int l.tmpBytes),
      ("workBytes", .int l.workBytes)]

def inputValue (i : Input) : Value :=
  .obj
    [("kept", .bool i.kept), ("path", .str i.path), ("role", .str i.role),
      ("sha256", .str i.sha256), ("size", .int i.size)]

def Record.value (r : Record) : Value :=
  .obj
    [("complete", .bool r.complete), ("imports", strs r.imports),
      ("inputs", .arr (r.inputs.map inputValue)), ("limits", limitsValue r.limits),
      ("module", .str r.module), ("phase", .int r.phase),
      ("presence", .arr (r.presence.map fun p => strs [p.1, p.2])),
      ("recipe", recipeValue r.recipe), ("roots", strs r.roots), ("schema", .int 1),
      ("step", .str r.step)]

/-- B2: a record's limits back (each cap as the record resolved it). -/
def limitsOf (v : Value) : Option FvdepCore.Sandbox.Limits := do
  let [deadline, diagnosticBytes, exportBytes, fileBytes, frameBytes, tmpBytes, workBytes] ←
    members
        ["deadline", "diagnosticBytes", "exportBytes", "fileBytes", "frameBytes", "tmpBytes",
          "workBytes"]
        v | none
  pure {
        deadline := ← natOf deadline
        workBytes := ← natOf workBytes
        tmpBytes := ← natOf tmpBytes
        diagnosticBytes := ← natOf diagnosticBytes
        frameBytes := ← natOf frameBytes
        fileBytes := some (← natOf fileBytes)
        exportBytes := some (← natOf exportBytes) }

def inputOf (v : Value) : Option Input := do
  let [kept, path, role, sha256, size] ← members ["kept", "path", "role", "sha256", "size"] v | none
  pure {
        role := ← strOf role
        path := ← strOf path
        size := ← natOf size
        sha256 := ← strOf sha256
        kept := ← boolOf kept }

/-- B2 + D4: `bundle.json` back — its canonical text alone (another spelling of the same value, an
unknown or missing member, another schema, a `complete` its inputs contradict or an input outside
B2's roles `src`, `lib`, `prior` or at an unsafe path (D4 reads `inputs/<role>/<path>`) = no
record). -/
def Record.ofBytes (b : ByteArray) : Option Record := do
  let v ← (FvdepCore.Json.decode b).toOption
  let [complete, imports, inputs, limits, module, phase, presence, recipe, roots, schema, step] ←
    members
        ["complete", "imports", "inputs", "limits", "module", "phase", "presence", "recipe",
          "roots", "schema", "step"]
        v | none
  let r : Record :=
    { recipe := ← recipeOf recipe
      limits := ← limitsOf limits
      phase := ← natOf phase
      step := ← strOf step
      module := ← strOf module
      imports := ← strsOf imports
      roots := ← strsOf roots
      presence := ← (← arrOf presence).mapM pairOf
      inputs := ← (← arrOf inputs).mapM inputOf }
  guard ((← natOf schema) == 1 && (← boolOf complete) == r.complete && print r.value == b)
  guard
      (r.inputs.all fun i =>
        ["src", "lib", "prior"].contains i.role && FvdepCore.Step.safePath i.path)
  pure r

end FvdepCore.Bundle
