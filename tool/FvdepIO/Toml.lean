import FvdepCore.Manifest
import Lake.Toml.Load

/-! `fvdep.toml` through Lake's TOML parser (contract `docs/contracts/U3-codecs.md` T1):
`Lake.Toml.loadToml` = residue `toml-parse`; `ofLake` turns its table into a `Tree`. -/

namespace FvdepIO.Toml

open Lean FvdepCore.Manifest FvdepCore.Doc

/-- T1: Lake's first error message (line 1-based, column 0-based as Lake reports it, its text) or
`ofLake`'s key of another shape. -/
inductive ParseError where
  | syntax (line col : Nat) (message : String)
  | key (name : Name)
  deriving Repr, BEq

mutual
/-- T1 + T5: Lake's value as a `Tree`; `.error` = the first key (pre-order) of another shape than
one string component. -/
def ofValue : Lake.Toml.Value → Except Name Tree
  | .string _ s => .ok (.str s)
  | .integer _ n => .ok (.int n)
  | .float .. => .ok (.other .float)
  | .boolean _ b => .ok (.bool b)
  | .dateTime .. => .ok (.other .dateTime)
  | .array _ xs => .arr <$> ofValues xs.toList
  | .table' _ d => .tbl <$> ofMembers d.items.toList
/-- The elements, in order. -/
def ofValues : List Lake.Toml.Value → Except Name (List Tree)
  | [] => .ok []
  | x :: xs => do
    let t ← ofValue x
    let ts ← ofValues xs
    return t :: ts
/-- The members, in Lake's order; a key = its `Name`'s single string component. -/
def ofMembers : List (Name × Lake.Toml.Value) → Except Name (List (String × Tree))
  | [] => .ok []
  | (n, x) :: xs =>
    match n with
    | .str .anonymous s => do
      let t ← ofValue x
      let ms ← ofMembers xs
      return (s, t) :: ms
    | _ => .error n
end

/-- T1 + T5: Lake's table as a `Tree`. -/
def ofLake (t : Lake.Toml.Table) : Except Name Tree := .tbl <$> ofMembers t.items.toList

/-- T1: Lake's parse of `fvdep.toml`'s text, then `ofLake` (the read path's one IO step). -/
def parseTree (text : String) : IO (Except ParseError Tree) := do
  match ← (Lake.Toml.loadToml (Parser.mkInputContext text "fvdep.toml")).toBaseIO with
  | .ok t =>
    return (ofLake t).mapError .key
  | .error log =>
    match log.toList.find? (·.severity == .error) with
    | some msg =>
      return .error (.syntax msg.pos.line msg.pos.column (← msg.data.toString))
    | none =>
      return .error (.syntax 0 0 "")

/-- T1: why `fvdep.toml` is refused. -/
inductive ReadError where
  | text (e : TextError)
  | parse (e : ParseError)
  | schema (e : ManifestError)
  deriving Repr

/-- The public code: `internal` for `ofLake`'s key, `schema` for every other refusal. -/
def ReadError.code : ReadError → PublicCode
  | .parse (.key _) => .internal
  | _ => .schema

/-- The refusal text (presentation): Lake's position as `line:column` (both 1-based). -/
def ReadError.detail : ReadError → String
  | .text e => e.detail
  | .parse (.syntax line col message) =>
    "syntax at " ++ toString line ++ ":" ++ toString (col + 1) ++ ": " ++ escapeControls message
  | .parse (.key n) => "TOML key of an unexpected shape: " ++ escapeControls (toString n)
  | .schema e => e.detail

/-- T1: bytes → `textStage` → `parseTree` → `validate`. -/
def readManifest (b : ByteArray) : IO (Except ReadError ManifestFile) := do
  match textStage b with
  | .error e =>
    return .error (.text e)
  | .ok s =>
    match ← parseTree s with
    | .error e =>
      return .error (.parse e)
    | .ok t =>
      return (validate t).mapError .schema

end FvdepIO.Toml
