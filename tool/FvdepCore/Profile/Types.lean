/-! The implementation profile's data (contract `docs/contracts/U6-profile.md` P5a–c, P6, T, C1):
the owned tree the checker walks, its typed causes, a batch's request + record. Pure. -/

namespace FvdepCore.Profile

/-- A source position: Lean's `Position` (line 1-based, column 0-based in codepoints). -/
structure Pos where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr

/-- One occurrence of a parsed module (C1): a node of `kind`, an atom (its text) or an identifier
(its parsed `Name`'s components), each leaf at its original position; `missing` = a parser gap.
Names = their components in order. -/
inductive Tree where
  | node (kind : List String) (kids : List Tree)
  | atom (text : String) (pos : Option Pos)
  | ident (name : List String) (pos : Option Pos)
  | missing
  deriving Repr, Inhabited

/-- The profile this child implements (P5a's + P5b's `profile`; Q2's version id). -/
def profileId : String := "fvdep/profile/1"

/-- T's cap on one detail string, in UTF-8 bytes. -/
def detailMax : Nat := 1024

/-- P6's limits the child applies (`seconds` = the supervisor's step deadline). -/
structure Limits where
  depth : Nat := 4096
  nodes : Nat := 4194304
  batchNodes : Nat := 16777216
  deriving DecidableEq, Repr

/-- The role a batch is checked under (I1, I2). -/
inductive Role where
  | consumer
  | library
  deriving DecidableEq, Repr

def Role.text : Role → String
  | .consumer => "consumer"
  | .library => "library"

/-- P5a: a batch module — its name, its path relative to the snapshot root (`A/B.lean`) + S1's
SHA-256 of its bytes (lowercase hex). -/
structure ReqModule where
  module : String
  path : String
  sha256 : String
  deriving DecidableEq, Repr

/-- P5a: a module of the pinned library snapshot + its explicit header imports in source order. -/
structure LibModule where
  module : String
  imports : List String
  deriving DecidableEq, Repr

/-- P5a: every input the child's verdict depends on beside the frozen sources + the sysroot. -/
structure Request where
  library : List LibModule
  limits : Limits
  modules : List ReqModule
  profile : String
  recipe : String
  role : Role
  toolchain : String
  deriving DecidableEq, Repr

/-- P5b: a batch module as the record reports it. -/
structure ModuleRec where
  module : String
  sha256 : String
  grammar : List String
  deriving DecidableEq, Repr

/-- P5b: a refusal's location + its cause at T's rendering level (`rule` + `detail`). -/
structure Refusal where
  module : String
  line : Nat
  column : Nat
  rule : String
  detail : List String
  deriving DecidableEq, Repr

/-- P5b: a batch's outcome; `over` = P6's `batchNodes` passed (infrastructure). -/
inductive Outcome where
  | accepted
  | refused (r : Refusal)
  | over
  deriving DecidableEq, Repr

/-- P5b: the record the child writes for one batch. -/
structure Record where
  modules : List ModuleRec
  outcome : Outcome
  profile : String
  recipe : String
  request : String
  deriving DecidableEq, Repr

end FvdepCore.Profile
