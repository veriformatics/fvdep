/-! Shared type of `semver.parse` + `semver.compare` 1.0.0 (`docs/library.md`): a SemVer 2.0.0
version. Any value, valid or not: `semver.compare` is total over the whole type. -/

namespace Fvdep.Semver.Version.V1_0_0

/-- A pre-release identifier (§9): numeric or alphanumeric. -/
inductive Ident where
  | num (n : Nat)
  | alnum (s : List Char)
  deriving DecidableEq, Repr

/-- `major.minor.patch` (§2), pre-release identifiers (§9), build identifiers (§10). -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List Ident
  build : List (List Char)
  deriving DecidableEq, Repr

end Fvdep.Semver.Version.V1_0_0
