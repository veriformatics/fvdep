import FvdepAudit.Json.Proof.Corollaries
import FvdepCore.Judge.Template

/-! Proofs: S0's template digest input (contract `docs/contracts/U7-judge.md` S0) — on names within
J's string bound, the template's canonical bytes determine the request (J's `print_decode`). -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Json FvdepCore.Judge FvdepAudit.Json.Proof

theorem templateValue_valid (x : Template)
    (h : ∀ s ∈ x.abi.toList ++ [x.impl, x.spec, x.proof], s.utf8ByteSize ≤ 65536) :
    FvdepAudit.Json.Spec.Valid (templateValue x) := by
  rcases x with ⟨sh, i, sp, pr, ab⟩
  have hi : i.utf8ByteSize ≤ 65536 := h _ (by simp)
  have hs : sp.utf8ByteSize ≤ 65536 := h _ (by simp)
  have hp : pr.utf8ByteSize ≤ 65536 := h _ (by simp)
  cases ab with
  | none =>
    cases sh <;>
      simp [templateValue, shapeText, FvdepAudit.Json.Spec.Valid, FvdepAudit.Json.Spec.intsFit,
        FvdepAudit.Json.Spec.intsFitMembers, FvdepAudit.Json.Spec.stringsFit,
        FvdepAudit.Json.Spec.stringsFitMembers, FvdepAudit.Json.Spec.depth,
        FvdepAudit.Json.Spec.depthMembers, FvdepAudit.Json.Spec.keysAscend,
        FvdepAudit.Json.Spec.keysAscendMembers, FvdepAudit.Json.Spec.maxStringBytes,
        FvdepAudit.Json.Spec.maxDepth, hi, hs, hp] <;>
      decide
  | some a =>
    have ha : a.utf8ByteSize ≤ 65536 := h _ (by simp)
    cases sh <;>
      simp [templateValue, shapeText, FvdepAudit.Json.Spec.Valid, FvdepAudit.Json.Spec.intsFit,
        FvdepAudit.Json.Spec.intsFitMembers, FvdepAudit.Json.Spec.stringsFit,
        FvdepAudit.Json.Spec.stringsFitMembers, FvdepAudit.Json.Spec.depth,
        FvdepAudit.Json.Spec.depthMembers, FvdepAudit.Json.Spec.keysAscend,
        FvdepAudit.Json.Spec.keysAscendMembers, FvdepAudit.Json.Spec.maxStringBytes,
        FvdepAudit.Json.Spec.maxDepth, hi, hs, hp, ha] <;>
      decide

/-- U7 S0 `templateInjective`. -/
theorem template_injective (x y : Template) :
    (∀ s ∈ x.abi.toList ++ [x.impl, x.spec, x.proof], s.utf8ByteSize ≤ 65536) →
      (∀ s ∈ y.abi.toList ++ [y.impl, y.spec, y.proof], s.utf8ByteSize ≤ 65536) →
      templateBytes x = templateBytes y → x = y := by
  intro hx hy he
  have h1 := print_decode _ (templateValue_valid x hx)
  have h2 := print_decode _ (templateValue_valid y hy)
  unfold templateBytes at he
  rw [he, h2] at h1
  have hv : templateValue y = templateValue x := Except.ok.inj h1
  rcases x with ⟨sx, ix, px, prx, ax⟩
  rcases y with ⟨sy, iy, py, pry, ay⟩
  cases sx <;> cases sy <;> cases ax <;> cases ay <;> simp_all [templateValue, shapeText]

/-- U7 S0 `templateLayout`: the template's bytes = the canonical J text of S0's six members. -/
theorem template_layout (x : Template) :
    templateBytes x =
      print
        (.obj
          [("abi", x.abi.elim .null .str), ("form", .str "fvdep/statement/1"),
            ("impl", .str x.impl), ("proof", .str x.proof),
            ("shape", .str (if x.shape = .fn then "fn" else "abi")), ("spec", .str x.spec)]) := by
  rcases x with ⟨_ | _, _, _, _, _ | _⟩ <;> rfl

/-- U7 S0 `statementDigestExact`: the digest hashes exactly the template's bytes. -/
theorem statementDigest_exact (h : ByteArray → String) (x : Template) :
    statementDigest h x = h (templateBytes x) := rfl

end FvdepAudit.Judge.Proof
