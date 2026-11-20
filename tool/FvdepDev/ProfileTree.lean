/-! U6's input (contract `docs/contracts/U6-profile.md` T): one parsed module as data — every syntax
node with its kind, every atom + identifier leaf, each with its source position. -/

namespace FvdepDev.ProfileTree

/-- A source position: one-based line, zero-based column (codepoints), as Lean's `FileMap`
reports. -/
structure Pos where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr

/-- One node of a parsed module (a name = its components in order). -/
inductive Tree where
  | node (kind : List String) (pos : Option Pos) (kids : List Tree)
  | atom (text : String) (pos : Option Pos)
  | ident (name : List String) (pos : Option Pos)
  | missing
  deriving Repr, Inhabited

end FvdepDev.ProfileTree
