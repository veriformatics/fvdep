namespace Fvdep.Trial.WeightMix.V2_0_0

def foldPulse {a : Int} (b c : Int) : Option Int :=
  if b == c then none else some (5 * a - 7 * b + 11 * c)

end Fvdep.Trial.WeightMix.V2_0_0
