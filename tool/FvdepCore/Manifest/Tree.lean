/-! `fvdep.toml`'s TOML tree + Lake's parse failure (contract `docs/contracts/U3-codecs.md` T1): a
leaf module, so the effect vocabulary (`FvdepCore.Plan`) names the `parse` effect's answer. -/

namespace FvdepCore.Manifest

/-- T1: a TOML value kind no manifest field takes. -/
inductive Other where
  | float
  | dateTime
  deriving DecidableEq, Repr, Inhabited

/-- T1: a TOML value, keys as strings (`FvdepIO.Toml.ofLake` builds it from Lake's table; a table's
members in Lake's order, which T3 never relies on). -/
inductive Tree where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  | arr (xs : List Tree)
  | tbl (ms : List (String × Tree))
  | other (k : Other)
  deriving Repr, Inhabited, BEq

/-- T1: Lake's first error message (line 1-based, column 0-based as Lake reports it, its text) or
`ofLake`'s key of another shape. -/
inductive ParseError where
  | syntax (line col : Nat) (message : String)
  | key (name : Lean.Name)
  deriving Repr, BEq

end FvdepCore.Manifest
