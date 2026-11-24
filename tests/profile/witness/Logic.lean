namespace Witness.Logic

def compare (a b : Nat) : Prop :=
  ((a < b ∨ a > b) ∧ (a ≤ b /\ a <= b)) ∧
    ((a ≥ b \/ a >= b) ∧ ((a = b) ↔ ¬ (a ≠ b)))

def iffAscii (a b : Prop) : Prop := a <-> b

def universal : Prop := ∀ (a : Nat), a = a
def universalAscii : Prop := forall (a : Nat), a = a
def existsUnicode : Prop := ∃ (a : Nat), a = a
def existsAscii : Prop := exists a : Nat, a = a

def ordered : Prop :=
  (∀ a < (1 : Nat), a = a) ∧ (∀ a > (1 : Nat), a = a) ∧
    (∀ a ≤ (1 : Nat), a = a) ∧ (∀ a ≥ (1 : Nat), a = a) ∧
      (∀ a ≠ (1 : Nat), a = a) ∧ (∃ a < (2 : Nat), a = a)

def membership (xs : List Nat) : Prop := (∀ a ∈ xs, a ∈ xs) ∧ (∀ a ∉ xs, a ∉ xs)

structure Collection where
  values : List Nat

instance : HasSubset Collection where
  Subset l r := List.Subset l.values r.values

instance : HasSSubset Collection where
  SSubset l r := List.Subset l.values r.values ∧ l.values ≠ r.values

def subsets (xs : Collection) : Prop :=
  (∀ ys ⊆ xs, (ys : Collection) = ys) ∧ (∀ ys ⊂ xs, (ys : Collection) = ys) ∧
    (∀ ys ⊇ xs, (ys : Collection) = ys) ∧ (∀ ys ⊃ xs, (ys : Collection) = ys)

end Witness.Logic
