namespace Witness.Termination

def structuralCount : Nat → Nat
  | 0 => 0
  | Nat.succ n => 1 + structuralCount n
termination_by structural n => n

def wellFounded (n : Nat) : Nat :=
  if h : 1 < n then wellFounded (n - 1) + (Fin.mk 1 h).val else 0
termination_by n
decreasing_by
  all_goals (omega);

def twoCalls (n : Nat) : Nat :=
  if 2 < n then twoCalls (n - 1) + twoCalls (n - 2) else 1
termination_by n
decreasing_by
  · omega
  . omega

def closedDecrease : Nat → Nat
  | 0 => 0
  | 1 => closedDecrease 0
  | Nat.succ (Nat.succ n) => n
termination_by n => n
decreasing_by decide

end Witness.Termination
