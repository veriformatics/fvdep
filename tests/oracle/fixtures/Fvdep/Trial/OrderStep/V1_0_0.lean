namespace Fvdep.Trial.OrderStep.V1_0_0

def spin : Ordering → Ordering
  | .lt => .eq
  | .eq => .gt
  | .gt => .lt

end Fvdep.Trial.OrderStep.V1_0_0
