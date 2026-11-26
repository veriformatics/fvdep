import FvdepCore.Judge.Compare
import Std.Data.HashMap

/-! U7 X6 + X8 (contract `docs/contracts/U7-judge.md`): one export as the judge reads it — the
reader's tables + its constants by denoted name (X8: one declaration per name, so the index finds
the one). Pure. -/

namespace FvdepCore.Judge

open FvdepCore.Export

/-- A constant's name (an index). -/
def Entry.name : Entry → Nat
  | .axiom _ _ n _ => n
  | .defn _ _ _ n _ _ _ => n
  | .thm _ _ n _ _ => n
  | .opaque _ _ _ n _ _ => n
  | .quot _ _ n _ => n
  | .induct x => x.name
  | .ctor c => c.name
  | .recursor r => r.name

/-- One export as the judge reads it. -/
structure View where
  t : Tables
  byName : Std.HashMap Lean.Name Entry

/-- One constant into the index (an unbound name index: left out). -/
def indexStep (t : Tables) (m : Std.HashMap Lean.Name Entry) (e : Entry) :
    Std.HashMap Lean.Name Entry := match t.names[e.name]? with
  | some n => m.insert n e
  | none => m

/-- The constants of `es` by denoted name. -/
def nameIndex (t : Tables) (es : List Entry) : Std.HashMap Lean.Name Entry :=
  es.foldl (indexStep t) {}

def viewOf (t : Tables) : View := { t, byName := nameIndex t (t.rawDecls.toList.flatMap entries) }

end FvdepCore.Judge
