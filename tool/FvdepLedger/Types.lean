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
it. `path` = a root's `main` → … → `subject` (the executed function), or `[]` while `noCaller`
names the open unit that wires the subject in, is `support` (a helper inside the closure of a row
with a path) or `step` (inside a `StepSource`'s reach: run only in a sandbox step, from shipped
source). `residue` + `unproven` cite `Residue` ids: what the claims still assume, and what of the
component has no theorem. -/
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

/-- A shipped executable's entry: `main` = `interpreter` applied to `plan args` (shape checked). -/
structure Root where
  main : Lean.Name
  interpreter : Lean.Name
  plan : Lean.Name

/-- A sandbox step whose program fvdep ships as source: `driver` = the shipped definition that
writes the program (a root reaches it); `embedded` = the shipped `List (Lean.Name × String)` the
driver writes the program's module texts from (`lake test` holds each text = its module's file);
`call` = the shipped definition naming (a name literal) the function the program's generated code
calls, which the driver renders; `classes` = the type classes whose instances the program's
elaboration picks among. The driver reaches `embedded` + `call`; the call + each class = a
declaration of an embedded module. -/
structure StepSource where
  driver : Lean.Name
  embedded : Lean.Name
  call : Lean.Name
  classes : List Lean.Name

/-- The whole ledger: `fvdep`'s root (`main` = `interpreter` applied to `plan args`, checked by
shape), the shipped lean_lib roots, the rows, the residue, one `Root` per further shipped
executable (an owned entry its root module's `main` calls whole: a second top-level `main` cannot
share this environment with `fvdep`'s) + one `StepSource` per sandbox step running shipped
source. -/
structure Ledger where
  main : Lean.Name
  interpreter : Lean.Name
  plan : Lean.Name
  libs : List Lean.Name
  rows : List Row
  residue : List Residue
  extraRoots : List Root := []
  steps : List StepSource := []

end FvdepLedger
