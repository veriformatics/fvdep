-- expect phase1: No deriving handlers have been implemented for class
/-! Q1's shadow control: a consumer class named like an admitted deriving class in the current
namespace takes the `deriving` name; Lean finds no handler for it + the build fails (no other
handler runs). -/

namespace Witness.ShadowRepr

class Repr (α : Type) where
  tag : Nat

structure Point where
  x : Nat
  deriving Repr

end Witness.ShadowRepr
