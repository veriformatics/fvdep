import FvdepCore.Profile.Check
import FvdepDev.Parse

/-! Never shipped. U6-B2's seam (contract `docs/contracts/U6-profile.md` C1, I, P3–P5): the pure
checks over the trees Lean's parser builds — each module's header parsed + checked (batch order),
its grammar computed (P3), then its body parsed under that grammar + walked — with no child, cap or
record (U6-C's `fvdep-parse` runs the same stages under P6's caps). Prints D1's tail lines:
`grammar <M> <G>…`, then `accepted` | `refused <M> <line>:<column> <cause>`. -/

namespace FvdepDev.Walk

open Lean FvdepCore.Profile

def parts : Name → List String := FvdepDev.Parse.parts

def posOf (fm : FileMap) (info : SourceInfo) : Option Pos :=
  info.getPos?.map fun p =>
    let q := fm.toPosition p
    ⟨q.line, q.column⟩

/-- `stx` as the profile's tree (dev: uncapped). -/
partial def treeOf (fm : FileMap) : Syntax → Tree
  | .missing => .missing
  | .atom info v => .atom v (posOf fm info)
  | .ident info _ n _ => .ident (parts n) (posOf fm info)
  | .node _ kind args => .node (parts kind) (args.toList.map (treeOf fm))

/-- Lean's first error line without its `file:line:col: error:` prefix, at its position. -/
def firstError (log : MessageLog) : IO (Option Finding) := do
  match log.toList.find? (·.severity == .error) with
  | some m =>
    let t ← m.data.toString
    let line := (t.splitOn "\n").headD t
    return some ⟨⟨m.pos.line, m.pos.column⟩, "parse", [line]⟩
  | none =>
    return none

/-- A module's header: its tree + the parser state after it, or its parse finding. -/
def parseHead (path text : String) :
    IO (Parser.InputContext × Except Finding (Tree × Parser.ModuleParserState)) := do
  let input := Parser.mkInputContext text path
  let (h, st, log) ← Parser.parseHeader input
  match ← firstError log with
  | some f =>
    return (input, .error f)
  | none =>
    return (input, .ok (treeOf input.fileMap h.raw, st))

/-- The header's imports (I1's names, in source order). -/
def importsOf : Tree → List String
  | .node _ kids =>
    match (kids[2]? : Option Tree) with
    | some (.node _ imps) =>
      imps.filterMap fun
        | .node _ ks =>
          match (ks[4]? : Option Tree) with
          | some (.ident n _) => some (dotted n)
          | _ => none
        | _ => none
    | _ => []
  | _ => []

/-- P5: a module's body, command by command under `env`, as C1's items (a parse failure ends the
list as its finding). -/
partial def bodyItems (env : Environment) (input : Parser.InputContext)
    (st : Parser.ModuleParserState) (acc : Array Item) : IO (List Item) := do
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let start := input.fileMap.toPosition st.pos
  let (cmd, st', log) := Parser.parseCommand input pmctx st {}
  match ← firstError log with
  | some f =>
    return (acc.push (.stop f)).toList
  | none =>
    if cmd.isOfKind ``Parser.Command.eoi then
      if input.atEnd st'.pos then
        return acc.toList
      let q := input.fileMap.toPosition st'.pos
      return (acc.push
            (.stop
              ⟨⟨q.line, q.column⟩, "parse",
                ["the input continues after the end of the module"]⟩)).toList
    if st'.pos == st.pos then
      return (acc.push
            (.stop ⟨⟨start.line, start.column⟩, "parse", ["the parser made no progress"]⟩)).toList
    let acc := acc.push (.tree (treeOf input.fileMap cmd) ⟨start.line, start.column⟩)
    -- Lean's frontend stops at these; their walk refuses them by kind (U6 P5).
    if cmd.isOfKind ``Parser.Command.exit || cmd.isOfKind ``Parser.Command.import then
      return acc.toList
    bodyItems env input st' acc

def refusedLine (m : String) (f : Finding) : String :=
  s!"refused {m} {f.pos.line}:{f.pos.col} {" ".intercalate (f.rule :: f.detail)}"

/-- `fvdep-dev profile walk [--library] [--lib <M>=<I>,…]… <file>…`: module = the file's stem. -/
def run (args : List String) : IO UInt32 := do
  let mut role : Role := .consumer
  let mut libRows : List (String × List String) := []
  let mut files : List String := []
  for a in args do
    if a == "--library" then
      role := .library
    else if a.startsWith "--lib=" then
      match (String.ofList (a.toList.drop 6)).splitOn "=" with
      | [m, is] =>
        libRows := libRows ++ [(m, if is.isEmpty then [] else is.splitOn ",")]
      | _ =>
        IO.eprintln s!"usage: --lib=<M>=<I>,…";
        return 2
    else
      files := files ++ [a]
  let stem := fun (f : String) =>
    let b := ((f.splitOn "/").getLast?.getD f).toList
    String.ofList (b.take (b.length - 5))
  let named := (files.map fun f => (stem f, f)).toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let batch := named.map (·.1)
  let lib := libRows.map (·.1)
  let mut heads : List (String × Parser.InputContext × Tree × Parser.ModuleParserState) := []
  for (m, f) in named do
    let (input, r) ← parseHead f (← IO.FS.readFile f)
    match r with
    | .error e =>
      IO.println (refusedLine m e);
      return 1
    | .ok (h, st) =>
      match header role lib batch m h with
      | some e =>
        IO.println (refusedLine m e);
        return 1
      | none =>
        heads := heads ++ [(m, input, h, st)]
  let importsMap := fun (x : String) =>
    match heads.find? (·.1 == x) with
    | some (_, _, h, _) => importsOf h
    | none => (libRows.lookup x).getD []
  let fuel :=
    heads.length + libRows.length + 1 + (heads.map fun (_, _, h, _) => (importsOf h).length).sum +
      (libRows.map (·.2.length)).sum
  let grammars := heads.map fun (m, _) => (m, grammar importsMap fuel m)
  for (m, g) in grammars do
    IO.println s!"grammar {m} {" ".intercalate g}"
  let mut envs : List (List String × Environment) := []
  for ((m, input, _, st), (_, g)) in heads.zip grammars do
    let env ←
      match envs.lookup g with
      | some e =>
        pure e
      | none =>
        do
          let e ← FvdepDev.Parse.grammar (g.map String.toName)
          envs := envs ++ [(g, e)]
          pure e
    let items ← bodyItems env input st #[]
    match body ⟨role, (m.splitOn ".").headD ""⟩ items with
    | some f =>
      IO.println (refusedLine m f);
      return 1
    | none =>
      pure ()
  IO.println "accepted"
  return 0

end FvdepDev.Walk
