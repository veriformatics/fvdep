import FvdepDev.ProfileTree
import Lean.Elab.Import
import Lean.Parser.Module

/-! U6's parse (contract `docs/contracts/U6-profile.md` P; residue `lean-parser`): one module's
header + every command parsed by Lean's own parser in a fixed trusted environment (never the
frontend, never the module's own imports' artifacts), then read as data. A parse error — a recovered
tree included — or an end before the input's end refuses the module. -/

namespace FvdepDev.Parse

open Lean FvdepDev.ProfileTree

/-- A name's components in order (a numeric one printed). -/
def parts : Name → List String
  | .anonymous => []
  | .str p s => parts p ++ [s]
  | .num p n => parts p ++ [toString n]

def posOf (fm : FileMap) (info : SourceInfo) : Option Pos :=
  info.getPos?.map fun p =>
    let q := fm.toPosition p
    ⟨q.line, q.column⟩

/-- `stx` as data. -/
partial def toTree (fm : FileMap) : Syntax → Tree
  | .missing => .missing
  | .atom info v => .atom v (posOf fm info)
  | .ident info _ n _ => .ident (parts n) (posOf fm info)
  | .node info kind args => .node (parts kind) (posOf fm info) (args.toList.map (toTree fm))

/-- The first error of `log`, one line. -/
def firstError (log : MessageLog) : IO String := do
  match log.toList.find? (·.severity == .error) with
  | some m =>
    let t ← m.toString
    return (t.splitOn "\n").headD t
  | none =>
    return "a parse error"

/-- The module `text` (`path` names it): its header, then each command parsed in `env` under `opts`;
a parse error, a recovered command or an end before the input's end → the refusal; `#exit` + a body
`import` end the list (their trees kept). -/
def parseModule (env : Environment) (opts : Options) (path text : String) :
    IO (Except String (List Tree)) := do
  let input := Parser.mkInputContext text path
  let (header, st0, log0) ← Parser.parseHeader input
  if log0.hasErrors then
    return .error s!"{path}: {← firstError log0}"
  let pmctx : Parser.ParserModuleContext := { env, options := opts }
  let mut st := st0
  let mut out := #[toTree input.fileMap header.raw]
  repeat
    let (cmd, st', log) := Parser.parseCommand input pmctx st {}
    if log.hasErrors then
      return .error s!"{path}: {← firstError log}"
    if cmd.isOfKind ``Parser.Command.eoi then
      if input.atEnd st'.pos then
        break
      return .error s!"{path}: the parse ended before the end of the input"
    out := out.push (toTree input.fileMap cmd)
    -- Lean's frontend stops at these (U6 D4 keeps the node + its keyword position).
    if cmd.isOfKind ``Parser.Command.exit || cmd.isOfKind ``Parser.Command.import then
      break
    st := st'
  return .ok out.toList

/-- `grammar`'s body: initializers enabled first (`importModules (loadExts := true)` refuses
otherwise; the modules it runs them for = the toolchain's own). -/
unsafe def grammarImpl (mods : List Name) : IO Environment := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  importModules (mods.map fun m => { module := m }).toArray {} (loadExts := true)

/-- The trusted grammar: `mods` from the toolchain on Lean's search path, their parser extensions
loaded (the toolchain's own compiled parsers). -/
@[implemented_by grammarImpl]
opaque grammar (mods : List Name) : IO Environment

end FvdepDev.Parse
