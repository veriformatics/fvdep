/-! Basic terms, control flow and names. -/

namespace Witness.Terms

/-- Application with a defaulted binder. -/
private def apply (f : Nat -> Nat) (x : Nat := 1) : Nat := f (x : Nat)

protected def named : Nat := apply Nat.succ (x := 2)

def tupled : Nat × Bool := (1, true)
def indexProjection (p : Nat × Bool) : Nat := p.1
def fieldProjection (p : Nat × Bool) : Nat := (p).fst
def pipeProjection (xs : List Nat) : Nat := xs |>.length
def inferred (x : Nat) : Nat := @id _ x
def someDot (x : Nat) : Option Nat := .some x

def dotUnicode : Nat → Nat := (· + 1)
def dotAscii : Nat → Nat := (. + 2)

def localBindings (n : Nat) : Nat :=
  let bump (x : Nat) := x + 1; let (a, b) := (bump n, n)
  have c := a + b; c + 1

def ordinaryIf (x : Nat) : Nat := if x > 0 then x else 1
def proofIf (x : Nat) : Nat := if h : x < 3 then (Fin.mk x h).val else 0
def patternIf (x : Option Nat) : Nat := if let some a := x then a else 0
def boolIf (b : Bool) : Nat := bif b then 1 else 0

def equations : Nat → Nat
  | 0 => 0
  | Nat.succ n => n

def matching (x y : Nat) : Nat :=
  match h : x, y with
  | 0, n => Eq.mp (congrArg (fun _ : Nat => Nat) h) n
  | Nat.succ n, m => n + m

def plainName : Lean.Name := `entry
def checkedName : Lean.Name := ``Nat.succ

end Witness.Terms
