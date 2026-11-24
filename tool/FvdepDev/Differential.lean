import FvdepCore.Profile.Batch
import FvdepDev.Parse
import FvdepIO.Parse
import Lean.Elab.Frontend

/-! Never shipped. `fvdep-dev profile differential [--lib=<M>=<I>,…]… [--path=<dir>]… <file>…`
(contract U6 P3 + P4, Q1: the parse's fidelity evidence). Per consumer module: the child's trees —
its grammar per P3 (`grammar` over the module's header imports + the `--lib` rows), each command
parsed in that initial context + converted by the shipped converter — against the frontend's
(`Lean.Elab.processHeader` over the real imports, `--path` dirs searched, + `IO.processCommands`:
each command parsed after the earlier ones elaborated, converted alike), + the grammar order: the
toolchain's modules of `allImportedModuleNames`, both ways. Prints `same <file> …` or
`differ <file> …`; exit 1 on a difference. Elaborates its inputs (the frontend runs them). -/

namespace FvdepDev.Differential

open Lean FvdepCore.Profile

/-- The toolchain's modules among `env`'s imports, in import order. -/
def toolchainModules (env : Environment) : List String :=
  (env.allImportedModuleNames.toList.map toString).filter toolchainModule

/-- `text`'s command trees, each command parsed in `env`'s initial context (the child's way). -/
def childTrees (env : Environment) (path text : String) : IO (Except String (List Tree)) := do
  let input := Parser.mkInputContext text path
  let (item, pst?, c0) ← FvdepIO.Parse.headItem {} ⟨0, 0⟩ input
  let (.tree _ _, some pst0) := (item, pst?) | return .error "the child's header stops"
  let mut pst := pst0
  let mut c := c0
  let mut out := #[]
  repeat
    let q := input.fileMap.toPosition pst.pos
    let (cmd, pst', log) := Parser.parseCommand input { env, options := {} } pst {}
    if log.hasErrors then
      return .error s!"the child's parse fails at {q.line}:{q.column}"
    if cmd.isOfKind ``Parser.Command.eoi then
      break
    match FvdepIO.Parse.convert input.fileMap {} ⟨q.line, q.column⟩ c cmd with
    | (.ok t, c') =>
      out := out.push t
      c := c'
    | (.error _, _) =>
      return .error s!"the child's converter caps at {q.line}:{q.column}"
    pst := pst'
  return .ok out.toList

/-- The frontend's command trees + its environment after the header (`paths` searched too). Lean's
`withImporting` clears the initializer flag after every import + the child's grammar load resets
the search path ⇒ both set again here. -/
unsafe def frontendTrees (paths : List System.FilePath) (path text : String) :
    IO (Except String (List Tree × Environment)) := do
  enableInitializersExecution
  initSearchPath (← findSysroot) paths
  let input := Parser.mkInputContext text path
  let (header, pst, msgs) ← Parser.parseHeader input
  let (env, msgs) ← Elab.processHeader header {} msgs input
  if msgs.hasErrors then
    let first ←
      match msgs.toList.find? (·.severity == .error) with
      | some m =>
        m.data.toString
      | none =>
        pure ""
    return .error s!"the frontend's header fails: {(first.splitOn "\n").headD first}"
  let s ← Lean.Elab.IO.processCommands input pst (Elab.Command.mkState env msgs {})
  let mut out := #[]
  let mut c : FvdepIO.Parse.Counts := ⟨0, 0⟩
  for cmd in s.commands do
    unless cmd.isOfKind ``Parser.Command.eoi do
      let p := input.fileMap.toPosition (cmd.getPos?.getD 0)
      match FvdepIO.Parse.convert input.fileMap {} ⟨p.line, p.column⟩ c cmd with
      | (.ok t, c') =>
        out := out.push t
        c := c'
      | (.error _, _) =>
        return .error s!"the frontend's tree caps at {p.line}:{p.column}"
  return .ok (out.toList, env)

unsafe def runImpl (args : List String) : IO UInt32 := do
  let mut rows : List LibModule := []
  let mut paths : List System.FilePath := []
  let mut files : List String := []
  for a in args do
    if a.startsWith "--lib=" then
      match (String.ofList (a.toList.drop 6)).splitOn "=" with
      | [m, is] =>
        rows := rows ++ [⟨m, if is.isEmpty then [] else is.splitOn ","⟩]
      | _ =>
        IO.eprintln "usage: --lib=<M>=<I>,…"
        return 2
    else
      if a.startsWith "--path=" then
        paths := paths ++ [⟨String.ofList (a.toList.drop 7)⟩]
      else
        files := files ++ [a]
  let mut rc : UInt32 := 0
  for f in files do
    let text ← IO.FS.readFile f
    let input := Parser.mkInputContext text f
    let (item, _, _) ← FvdepIO.Parse.headItem {} ⟨0, 0⟩ input
    let own :=
      match item with
      | .tree h _ => importsOf h
      | .stop _ => []
    let imports := fun (x : String) =>
      if x == f then own else ((rows.find? (·.module == x)).map (·.imports)).getD []
    let g :=
      grammar imports (2 * (own.length + (rows.map (·.imports.length)).sum) + rows.length + 4) f
    let envChild ← FvdepDev.Parse.grammar (g.map FvdepIO.Parse.nameOf)
    match ← childTrees envChild f text, ← frontendTrees paths f text with
    | .error e, _ =>
      IO.println s!"differ {f} {e}"
      rc := 1
    | _, .error e =>
      IO.println s!"differ {f} {e}"
      rc := 1
    | .ok ct, .ok (ft, envFront) =>
      let gc := toolchainModules envChild
      let gf := toolchainModules envFront
      if gc != gf then
        IO.println s!"differ {f} grammar child {gc.length} {gc} frontend {gf.length} {gf}"
        rc := 1
      else
        if ct.length != ft.length then
          IO.println s!"differ {f} commands child {ct.length} frontend {ft.length}"
          rc := 1
        else
          match (ct.zip ft).zipIdx.find? fun x => reprStr x.1.1 != reprStr x.1.2 with
          | some (_, i) =>
            IO.println s!"differ {f} command {i + 1}"
            rc := 1
          | none =>
            IO.println s!"same {f} {ct.length} commands, grammar {gc.length} toolchain modules"
  return rc

/-- `runImpl` (it enables initializer execution: `unsafe`). -/
@[implemented_by runImpl]
opaque run : List String → IO UInt32

end FvdepDev.Differential
