/-! Registry types v1 (`docs/library.md` Registry): what entry modules, proof registries, notices
and removed-entry records declare. Every operation entry's identity covers this module ⇒ it never
changes once an entry importing it is indexed; a change = `V2` beside it. -/

namespace Fvdep.Registry.Types.V1

/-- An operation entry: `spec` names the spec constant, `obligations` its named propositions (phase
1, in the identity); `abi` the C ABI shape (`Fvdep.Abi.V<x>_<y>_<z>.<shape>`) where one applies;
`compat` an older version of the same id this spec equals (fvdep builds `new spec = old spec`). -/
structure Module where
  id : String
  version : String
  spec : Lean.Name
  obligations : List Lean.Name
  abi : Option Lean.Name
  compat : Option String

/-- A proof registry (phase 2, `FvdepProofs`; never in an identity): each obligation → the theorem
proving it; `compat` → the theorem proving the entry's `compat` statement. -/
structure Proofs where
  obligations : List (Lean.Name × Lean.Name)
  compat : Option Lean.Name

/-- An appended notice (retraction): `replacement` = the version that replaces this one, if any. -/
structure Notice where
  id : String
  version : String
  reason : String
  replacement : Option String

inductive Kind where
  | operation
  | profile

/-- An entry that left the tree (a toolchain bump it failed): its last identity + where it lives. -/
structure Removed where
  id : String
  version : String
  kind : Kind
  digest : String
  toolchain : String
  lastCommit : String

end Fvdep.Registry.Types.V1
