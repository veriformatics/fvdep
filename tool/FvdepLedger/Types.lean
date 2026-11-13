/-! Coverage ledger data (contract `docs/contracts/U2-core.md` L1). Values stay literal (structure
instances, list + string literals, double-backtick names, references to other such values): the
checker decodes them from their elaborated definitions, so each name is checked twice — by the
elaborator (a dangling double-backtick name fails the build) + by the checker against the loaded
environment. -/

namespace FvdepLedger

/-- Something fvdep trusts without a proof (Decisions `Self-verification scope`): `ruling` = text
that must occur verbatim in `.agent/spec.md`; `boundary` = the declarations allowed to be opaque,
`extern` or `implemented_by` inside a proved closure that cites this entry. -/
structure Residue where
  id : String
  what : String
  reason : String
  ruling : String
  boundary : List Lean.Name

/-- One claim about fvdep's own code. `claims` = (statement, theorem) pairs: the statement is a
`Prop` definition in the ledger modules (the claim's exact proposition), the theorem's type must be
it. `path` = `main` → … → `subject` (the executed function), or `[]` while `noCaller` names the open
unit that wires the subject in, or is `support` (a helper inside the closure of a row with a path).
`residue` + `unproven` cite `Residue` ids: what the claims still assume, and what of the component
has no theorem. -/
structure Row where
  component : Lean.Name
  contract : String
  claim : String
  claims : List (Lean.Name × Lean.Name)
  subject : Lean.Name
  path : List Lean.Name
  noCaller : String
  residue : List String
  unproven : List String

/-- The whole ledger: the executable's root (`main` = `interpreter` applied to `plan args`, checked
by shape), the shipped lean_lib roots, the rows, the residue. -/
structure Ledger where
  main : Lean.Name
  interpreter : Lean.Name
  plan : Lean.Name
  libs : List Lean.Name
  rows : List Row
  residue : List Residue

end FvdepLedger
