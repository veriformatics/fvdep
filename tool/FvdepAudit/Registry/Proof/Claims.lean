import FvdepAudit.Registry.Proof.Read

/-! The registry-reading claims (contract U4 C8 `RegistryDecodeExact`, `ReencodeExact` + the
certificate's lists), headers = the ledger statements. -/

namespace FvdepAudit.Registry.Proof

open Lean FvdepCore.Index.Registry FvdepAudit.Registry.Spec

theorem registry_decode (F : Facts) (f : Form) (e : Expr) (env : List Expr) (p : List Name)
    (v : Val) : decode F f e env p = .ok v ↔ Denotes F f e env p v := decode_exact F f e env p v

theorem registry_read (F : Facts) (r : Lists) :
    (readRaw F).map Lists.ofRaw = .ok r ↔ RegistryDenotes F r := readRecords_exact F r

theorem registry_proofs (F : Facts) (c : Name) (pr : Proofs) :
    readProofs F c = .ok pr ↔ ProofsAt F c pr := readProofs_exact F c pr

theorem registry_forms :
    moduleForm = moduleFormSpec ∧
      noticeForm = noticeFormSpec ∧
      removedForm = removedFormSpec ∧ proofsForm = proofsFormSpec := forms_eq

theorem registry_reencode (F : Facts) (f : Form) (vs : List Val) (env : List Expr) (p : List Name)
    (hp : Plain f) (hv : ∀ v ∈ vs, Fits f v) :
    decode F (.list f) (listLiteral f vs) env p = .ok (listVal vs) :=
  listLiteral_exact F f vs env p hp hv

theorem registry_certificate (F : Facts) (r : RawLists) (env : List Expr) (p : List Name)
    (h : readRaw F = .ok r) (c : Name) (f : Form) (vs : List Val)
    (hc : (c, f, vs) ∈ certificate r) :
    decode F (.list f) (listLiteral f vs) env p = .ok (listVal vs) :=
  certificate_exact F r env p h c f vs hc

end FvdepAudit.Registry.Proof
