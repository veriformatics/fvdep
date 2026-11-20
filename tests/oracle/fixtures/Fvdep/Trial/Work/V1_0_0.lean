namespace Fvdep.Trial.Work.V1_0_0

def walk : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => walk n ((67 * x + 1) % 97)

def crank (n : Nat) : Nat := walk n 3

end Fvdep.Trial.Work.V1_0_0
