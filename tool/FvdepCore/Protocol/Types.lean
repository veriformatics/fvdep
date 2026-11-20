import Fvdep.Semver.Version.V1_0_0

/-! Adapter protocol v1's value types (`docs/interface.md` §8; contract U5b W0): shared by the
protocol codec (`FvdepCore.Protocol`) + the internal wire codec (`FvdepCore.Oracle.Wire`), whose
source the evaluation step compiles too ⇒ this module imports the version type alone. -/

namespace FvdepCore.Protocol

open Fvdep.Semver.Version.V1_0_0

/-- §8's value types. -/
inductive Ty where
  | bytes
  | text
  | utf16
  | nat
  | int
  | ordering
  | version
  deriving DecidableEq, Repr

/-- A result type: a value, or an optional value (`none` = the reply `err`). -/
inductive RTy where
  | plain (t : Ty)
  | option (t : Ty)
  deriving DecidableEq, Repr

/-- A typed value. -/
inductive Val where
  | bytes (b : List UInt8)
  | text (s : List Char)
  | utf16 (u : List UInt16)
  | nat (n : Nat)
  | int (i : Int)
  | ordering (o : Ordering)
  | version (v : Version)
  deriving DecidableEq, Repr

/-- A value's type (`HasTy x t` ⟺ `x.ty = t`). -/
def Val.ty : Val → Ty
  | .bytes _ => .bytes
  | .text _ => .text
  | .utf16 _ => .utf16
  | .nat _ => .nat
  | .int _ => .int
  | .ordering _ => .ordering
  | .version _ => .version

/-- A reply: a result, an optional result's `none` (wire `{"err":"none"}`), or a refused request. -/
inductive Reply where
  | ok (v : Val)
  | err
  | invalid (reason : String)
  deriving DecidableEq, Repr

end FvdepCore.Protocol
