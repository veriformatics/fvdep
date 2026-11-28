import FvdepAudit.Json.Proof.Corollaries
import FvdepCore.Judge.Template

/-! Proofs: S0's template digest input (contract `docs/contracts/U7-judge.md` S0) — on names within
J's string bound, the template's canonical bytes determine the request (J's `print_decode`). -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Json FvdepCore.Judge FvdepAudit.Json.Proof

theorem templateValue_valid (x : Template)
    (h :
      ∀ s ∈ x.abi.toList ++ [x.impl, x.spec, x.proof] ++ x.target.toList, s.utf8ByteSize ≤ 65536) :
    FvdepAudit.Json.Spec.Valid (templateValue x) := by
  rcases x with ⟨sh, i, sp, pr, ab, k, tg⟩
  have hi : i.utf8ByteSize ≤ 65536 := h _ (by simp)
  have hs : sp.utf8ByteSize ≤ 65536 := h _ (by simp)
  have hp : pr.utf8ByteSize ≤ 65536 := h _ (by simp)
  have htg : ∀ x ∈ tg.toList, x.utf8ByteSize ≤ 65536 := fun x hx => h _ (by simp_all)
  cases tg with
  | none => ?_
  | some tgt =>
    have ht : tgt.utf8ByteSize ≤ 65536 := htg _ (by simp)
    cases ab with
    | none =>
      cases sh <;> cases k <;>
        simp [templateValue, shapeText, formText, FvdepAudit.Json.Spec.Valid,
          FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
          FvdepAudit.Json.Spec.stringsFit, FvdepAudit.Json.Spec.stringsFitMembers,
          FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
          FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers,
          FvdepAudit.Json.Spec.maxStringBytes, FvdepAudit.Json.Spec.maxDepth, hi, hs, hp, ht] <;>
        decide
    | some a =>
      have ha : a.utf8ByteSize ≤ 65536 := h _ (by simp)
      cases sh <;> cases k <;>
        simp [templateValue, shapeText, formText, FvdepAudit.Json.Spec.Valid,
          FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
          FvdepAudit.Json.Spec.stringsFit, FvdepAudit.Json.Spec.stringsFitMembers,
          FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
          FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers,
          FvdepAudit.Json.Spec.maxStringBytes, FvdepAudit.Json.Spec.maxDepth, hi, hs, hp, ha,
          ht] <;>
        decide
  cases ab with
  | none =>
    cases sh <;> cases k <;>
      simp [templateValue, shapeText, formText, FvdepAudit.Json.Spec.Valid,
        FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
        FvdepAudit.Json.Spec.stringsFit, FvdepAudit.Json.Spec.stringsFitMembers,
        FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
        FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers,
        FvdepAudit.Json.Spec.maxStringBytes, FvdepAudit.Json.Spec.maxDepth, hi, hs, hp] <;>
      decide
  | some a =>
    have ha : a.utf8ByteSize ≤ 65536 := h _ (by simp)
    cases sh <;> cases k <;>
      simp [templateValue, shapeText, formText, FvdepAudit.Json.Spec.Valid,
        FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
        FvdepAudit.Json.Spec.stringsFit, FvdepAudit.Json.Spec.stringsFitMembers,
        FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
        FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers,
        FvdepAudit.Json.Spec.maxStringBytes, FvdepAudit.Json.Spec.maxDepth, hi, hs, hp, ha] <;>
      decide

theorem formText_inj {k k' : Kind} (h : formText k = formText k') : k = k' := by
  cases k <;> cases k' <;> simp_all [formText]

theorem shapeText_inj {s s' : FvdepCore.Evidence.Shape} (h : shapeText s = shapeText s') :
    s = s' := by cases s <;> cases s' <;> simp_all [shapeText]

/-- The template's J value determines the template (each member's encoding injective). -/
theorem templateValue_inj {x y : Template} (h : templateValue x = templateValue y) : x = y := by
  rcases x with ⟨sx, ix, px, prx, ax, kx, tx⟩
  rcases y with ⟨sy, iy, py, pry, ay, ky, ty⟩
  simp only [templateValue, Value.obj.injEq] at h
  obtain ⟨h6, ht⟩ := List.append_inj h (by simp)
  simp only [List.cons.injEq, Prod.mk.injEq, Value.str.injEq, true_and, and_true] at h6
  obtain ⟨ha, hk, hi, hp, hs, hsp⟩ := h6
  have hk' := formText_inj hk
  have hs' := shapeText_inj hs
  subst hk' hs' hi hp hsp
  have hab : ax = ay := by cases ax <;> cases ay <;> simp_all
  have htt : tx = ty := by cases tx <;> cases ty <;> simp_all
  subst hab htt
  rfl

/-- U7 S0 `templateInjective`. -/
theorem template_injective (x y : Template) :
    (∀ s ∈ x.abi.toList ++ [x.impl, x.spec, x.proof] ++ x.target.toList, s.utf8ByteSize ≤ 65536) →
      (∀ s ∈ y.abi.toList ++ [y.impl, y.spec, y.proof] ++ y.target.toList, s.utf8ByteSize ≤ 65536) →
      templateBytes x = templateBytes y → x = y := by
  intro hx hy he
  have h1 := print_decode _ (templateValue_valid x hx)
  have h2 := print_decode _ (templateValue_valid y hy)
  unfold templateBytes at he
  rw [he, h2] at h1
  have hv : templateValue y = templateValue x := Except.ok.inj h1
  exact (templateValue_inj hv).symm

/-- U7 S0 `templateLayout`: the template's bytes = the canonical J text of S0's six members, the
form tagging the kind, + a compat's `target`. -/
theorem template_layout (x : Template) :
    templateBytes x =
      print
        (.obj
          ([("abi", x.abi.elim .null .str),
              ("form",
                .str
                  (if x.kind = .eq then "fvdep/statement/1"
                  else
                    if x.kind = .prop then "fvdep/statement/prop/1"
                    else "fvdep/statement/compat/1")),
              ("impl", .str x.impl), ("proof", .str x.proof),
              ("shape", .str (if x.shape = .fn then "fn" else "abi")), ("spec", .str x.spec)] ++
            x.target.toList.map fun t => ("target", .str t))) := by
  rcases x with ⟨_ | _, _, _, _, _ | _, _ | _ | _, _ | _⟩ <;> rfl

/-- U7 S0 `statementDigestExact`: the digest hashes exactly the template's bytes. -/
theorem statementDigest_exact (h : ByteArray → String) (x : Template) :
    statementDigest h x = h (templateBytes x) := rfl

end FvdepAudit.Judge.Proof
