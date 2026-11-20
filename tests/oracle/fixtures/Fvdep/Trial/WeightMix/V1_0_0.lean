namespace Fvdep.Trial.WeightMix.V1_0_0

def foldPulse {a : Int} (b c : Int) : Option Int :=
  if b == c then none else some (a + 2 * b - 3 * c)

end Fvdep.Trial.WeightMix.V1_0_0
