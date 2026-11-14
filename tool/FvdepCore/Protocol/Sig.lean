import FvdepCore.Protocol
import Lean.Expr

/-! A spec constant's type → its protocol signature (contract U4 B1; C's encodability rule V3): the
table matches `Expr` shapes without reduction (a type synonym, `optParam` or another wrapper = not
encodable); metadata (`mdata d e`, which the kernel reads as `e`) is transparent at every position
the table reads. -/

namespace FvdepCore.Protocol

/-- `e` without its outer metadata layers. -/
def bare : Lean.Expr → Lean.Expr
  | .mdata _ e => bare e
  | e => e

/-- The §8 type of a spec argument or result. -/
def tyOf (e : Lean.Expr) : Option Ty :=
  match bare e with
  | .app f x =>
    match bare f, bare x with
    | .const ``List [_], .const ``UInt8 [] => some .bytes
    | .const ``List [_], .const ``Char [] => some .text
    | .const ``List [_], .const ``UInt16 [] => some .utf16
    | _, _ => none
  | .const ``ByteArray [] => some .bytes
  | .const ``Nat [] => some .nat
  | .const ``Int [] => some .int
  | .const ``Ordering [] => some .ordering
  | .const ``Fvdep.Semver.Version.V1_0_0.Version [] => some .version
  | _ => none

/-- A result type: `Option X` → `option`, else a plain value type. -/
def rtyOf (e : Lean.Expr) : Option RTy :=
  match bare e with
  | .app f x =>
    match bare f with
    | .const ``Option [_] => (tyOf x).map .option
    | _ => (tyOf e).map .plain
  | _ => (tyOf e).map .plain

/-- Argument types + result type of a spec type (non-dependent arrows over the §8 types; a result
`Option X` → `option`); `none` = not encodable (no argument, a dependent arrow, another type). -/
def sigOf : Lean.Expr → Option (List Ty × RTy)
  | .mdata _ e => sigOf e
  | .forallE _ a b _ =>
    if b.hasLooseBVars then none
    else
      match tyOf a, sigOf b with
      | some t, some p => some (t :: p.1, p.2)
      | some t, none => (rtyOf b).map fun r => ([t], r)
      | none, _ => none
  | _ => none

end FvdepCore.Protocol
