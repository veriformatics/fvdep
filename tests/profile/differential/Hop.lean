import Fvdep.Trial

/-! P3's library hop: the grammar reaches `Std.Data.HashSet` through the library module only. -/

namespace Witness.Hop

def hop : Nat := Fvdep.Trial.sample + 1

end Witness.Hop
