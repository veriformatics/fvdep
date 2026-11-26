import FvdepCore.Evidence
import FvdepCore.Json.Print

/-! U7 S0 (contract `docs/contracts/U7-judge.md`): the challenge key's `statement` digest = the hash
of the statement template's canonical J text over the request's names as written — fixed before
e1 exists (T, read from e1, is bound by the key's library commit + spec-closure digest). Pure: `h`
= the hash (SHA-256 hex in IO). -/

namespace FvdepCore.Judge

open FvdepCore.Json FvdepCore.Evidence

/-- S0's inputs: the manifest's + the registry's names (U3 T3 + D2). -/
structure Template where
  shape : Shape
  impl : String
  spec : String
  proof : String
  abi : Option String
  deriving DecidableEq, Repr

def shapeText : Shape → String
  | .fn => "fn"
  | .abi => "abi"

/-- The template as a J value (members in key order). -/
def templateValue (x : Template) : Value :=
  .obj
    [("abi",
        match x.abi with
        | some a => .str a
        | none => .null),
      ("form", .str "fvdep/statement/1"), ("impl", .str x.impl), ("proof", .str x.proof),
      ("shape", .str (shapeText x.shape)), ("spec", .str x.spec)]

def templateBytes (x : Template) : ByteArray := print (templateValue x)

/-- S0: the challenge key's `statement`. -/
def statementDigest (h : ByteArray → String) (x : Template) : Digest := h (templateBytes x)

end FvdepCore.Judge
