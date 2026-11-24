namespace Witness.Binders

universe u v

def explicitLevels.{p, q} (α : Type p) (β : Type q) : Type (max p q) := α × β
def levelPlus (α : Type (u + 1)) : Type (u + 1) := α
def levelMax (_ : Sort u) (_ : Sort v) (α : Sort (max u v)) : Sort (max u v) := α
def levelIMax (_ : Sort u) (_ : Sort v) (α : Sort (imax u v)) : Sort (imax u v) := α
def levelInferred (α : Type _) := α

def dependentUnicode : (x : Nat) → Fin (x + 1) := fun x => ⟨x, Nat.lt_succ_self x⟩
def dependentAscii : (x : Nat) -> Fin (x + 1) := λ x ↦ ⟨x, Nat.lt_succ_self x⟩
def ordinary {α : Type u} (a : α) : α := a
def strict ⦃α : Type u⦄ (a : α) : α := a
def synthesize {α : Type u} [Inhabited α] : α := default

end Witness.Binders

namespace Witness.BinderSpellings

def named [h : Inhabited Nat] : Nat := h.default

def strict {{α : Type}} (x : α) : α := x

end Witness.BinderSpellings
