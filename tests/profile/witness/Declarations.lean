namespace Witness.Declarations

open Nat
open Array (push)

structure First where
  first : Nat
  deriving DecidableEq, Repr, BEq, Hashable, Ord, Inhabited

-- Legacy `:=` still parses for both kinds; Lean warns but compiles.
structure Second :=
  (second : Nat)

structure Combined extends toFirst : First, Second where
  newCombined ::
  (value : Nat)
  {hidden : Nat}
  [defaultable : Inhabited Nat]

structure Defaults where
  first : Nat
  second : Bool := false

class Mapper (α : Type) where
  sample : α

instance : Mapper Nat where
  sample := 0

inductive Legacy :=
  | empty
  | full : Nat → Legacy

mutual
  inductive Tree where
    | node : Grove → Tree
  inductive Grove where
    | empty
    | cons : Tree → Grove → Grove
end

def combined (a : First) (b : Second) : Combined :=
  {a, b with value := 3, hidden := 4, defaultable := inferInstance}
def updated (p : Nat × (Nat × Bool)) : Nat × (Nat × Bool) := {p with snd.1 := 2}
def typed (n : Nat) := {first := n : First}
def semicolons : Defaults where
  first := private 1; second := true
def partialFields : Defaults := {first := 1, ..}

def withWorkers (n : Nat) : Nat := tweak n
where tweak x := inc x; inc x := x + 1

end Witness.Declarations
