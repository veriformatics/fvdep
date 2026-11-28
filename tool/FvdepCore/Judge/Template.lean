import FvdepCore.Evidence
import FvdepCore.Json.Print

/-! U7 S0 (contract `docs/contracts/U7-judge.md`): the challenge key's `statement` digest = the hash
of the statement template's canonical J text over the request's names as written — fixed before
e1 exists (T, read from e1, is bound by the key's library commit + spec-closure digest). Pure: `h`
= the hash (SHA-256 hex in IO). -/

namespace FvdepCore.Judge

open FvdepCore.Json FvdepCore.Evidence

/-- S's statement kinds (contract U7 S4 + Part B B7): `eq` = part A's equation (fn
`@Eq.{u} T impl spec`, abi `@Eq.{u} T impl (shape spec)`, T = the spec's type or the shape's
codomain); `prop` = an obligation (the theorem's type = the proposition constant `spec` itself:
U4 C5); `compat` = `@Eq.{u} T impl spec` with T = the type of `impl` (the new spec), `spec` = the
old (U4 C5). -/
inductive Kind where
  | eq
  | prop
  | compat
  deriving DecidableEq, Repr

/-- S0's inputs: the manifest's + the registry's names (U3 T3 + D2) + the statement's kind; a
compat's `target` = its target entry's `<id>@<version>` (Part B B7). -/
structure Template where
  shape : Shape
  impl : String
  spec : String
  proof : String
  abi : Option String
  kind : Kind := .eq
  target : Option String := none
  deriving DecidableEq, Repr

/-- S0's form tag per kind (part A's `eq` keeps its bytes: `fvdep/statement/1`). -/
def formText : Kind → String
  | .eq => "fvdep/statement/1"
  | .prop => "fvdep/statement/prop/1"
  | .compat => "fvdep/statement/compat/1"

def shapeText : Shape → String
  | .fn => "fn"
  | .abi => "abi"

/-- The template as a J value (members in key order; `target` present only when given). -/
def templateValue (x : Template) : Value :=
  .obj
    ([("abi",
          match x.abi with
          | some a => .str a
          | none => .null),
        ("form", .str (formText x.kind)), ("impl", .str x.impl), ("proof", .str x.proof),
        ("shape", .str (shapeText x.shape)), ("spec", .str x.spec)] ++
      x.target.toList.map fun t => ("target", .str t))

def templateBytes (x : Template) : ByteArray := print (templateValue x)

/-- S0: the challenge key's `statement`. -/
def statementDigest (h : ByteArray → String) (x : Template) : Digest := h (templateBytes x)

end FvdepCore.Judge
