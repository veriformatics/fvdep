import Std.Data.HashSet
import Std.Data.HashMap

/-! P3 + P4's import boundary: two toolchain imports in source order (the frontend's post-order). -/

namespace Witness.Imports

def sizes (s : Std.HashSet Nat) (m : Std.HashMap Nat Nat) : Nat := s.size + m.size

end Witness.Imports
