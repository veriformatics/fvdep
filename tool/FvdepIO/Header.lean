import FvdepCore.Manifest
import Lean.Elab.Import

/-! K2's header observation (contract `docs/contracts/U5-sandbox.md` K2; residue `lean-toolchain`:
Lean's own header parser): a module's `module` keyword (P2's family) + its imports in header order
with their flags — a non-`prelude` header's implicit `Init` + `meta Init` included — over the bytes
read once. A header with a parse error is refused, never read as "no imports". -/

namespace FvdepIO.Header

/-- One import as the header states it (K1's import vector before its keys). -/
structure Imported where
  module : String
  isPublic : Bool
  isMeta : Bool
  all : Bool
  deriving DecidableEq, Repr

structure Observed where
  isModule : Bool
  imports : List Imported
  deriving DecidableEq, Repr

/-- A module name's components when each is plain (U3 T3: `[A-Za-z_][A-Za-z0-9_']*`), else `none`
(an escaped or numeric component names no `A/B.lean` path). -/
def plainParts : Lean.Name → Option (List String)
  | .anonymous => some []
  | .str p s => do
    unless FvdepCore.Manifest.isComponent s.toList do
      none
    pure ((← plainParts p) ++ [s])
  | .num _ _ => none

/-- A plain module name's dotted spelling. -/
def plain (n : Lean.Name) : Option String :=
  match plainParts n with
  | some (c :: cs) => some (".".intercalate (c :: cs))
  | _ => none

/-- K2: the header of the source `src` (`path` names it in a refusal). -/
def observe (path : String) (src : ByteArray) : IO (Except String Observed) := do
  let some text := String.fromUTF8? src
    | return .error s!"{path} is not UTF-8"
  let input := Lean.Parser.mkInputContext text path
  let (header, _, messages) ← Lean.Parser.parseHeader input
  -- `headerToImports`' fall-through arms are `unreachable!`: a malformed header is refused here,
  -- before it is read.
  if messages.hasErrors then
    let first := messages.toList.find? (·.severity == .error)
    let why ←
      match first with
      | some m =>
        m.toString
      | none =>
        pure "a parse error"
    return .error s!"the header of {path} does not parse: {(why.splitOn "\n").headD why}"
  let mut imports := #[]
  for i in Lean.Elab.headerToImports header do
    match plain i.module with
    | some m =>
      imports :=
        imports.push
          { module := m, isPublic := i.isExported, isMeta := i.isMeta, all := i.importAll }
    | none =>
      return .error s!"{path} imports {i.module}, a module name without an `A/B.lean` path"
  return .ok { isModule := Lean.Elab.HeaderSyntax.isModule header, imports := imports.toList }

end FvdepIO.Header
