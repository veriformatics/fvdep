-- expect phase1: No deriving handlers have been implemented for class
/-! Q1's shadow control for `Ord`: a consumer class of that name in scope takes the `deriving`
name; Lean finds no handler + the build fails (no other handler runs). -/

namespace Witness.ShadowOrd

class Ord (α : Type) where
  tag : Nat

structure Point where
  x : Nat
  deriving Ord

end Witness.ShadowOrd
