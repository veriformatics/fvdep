/-! P4's scope boundaries: `namespace`, `section`, `open` of a namespace outside S, `end`; every
command parses in the initial context (no admitted command changes the grammar). -/

namespace Witness.Scopes

section
open Nat

def twice (n : Nat) : Nat := n + n

end

namespace Inner

def thrice (n : Nat) : Nat := twice n + n

end Inner

end Witness.Scopes
