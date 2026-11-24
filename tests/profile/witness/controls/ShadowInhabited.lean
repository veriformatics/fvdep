-- expect phase1: No deriving handlers have been implemented for class
/-! Q1's shadow control for `Inhabited`: a consumer class of that name in scope takes the `deriving`
name; Lean finds no handler + the build fails (no other handler runs). -/

namespace Witness.ShadowInhabited

class Inhabited (α : Type) where
  tag : Nat

structure Point where
  x : Nat
  deriving Inhabited

end Witness.ShadowInhabited
