import FvdepAudit.Index.Rules.Proof.Reach
import FvdepAudit.Index.Statuses.Spec

/-! C4's framed input against the closure written apart: `closureFiles` holds exactly the closure
modules' (canonical path, observed bytes); its paths are distinct when every closure module is plain
(`PlainModule`: `modulePath` is injective there), the frame's `FrameDomain` path premise. -/

namespace FvdepAudit.Index.Statuses.Proof

open Lean FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses
open FvdepAudit.Index.Rules.Spec FvdepAudit.Index.Rules.Proof FvdepAudit.Index.Statuses.Spec

theorem plain_parts {m : Name} (h : PlainModule m) :
    pathParts m ≠ [] ∧ ∀ s ∈ pathParts m, '/' ∉ s.toList := by
  induction m with
  | anonymous => simp [PlainModule] at h
  | num p n _ => simp [PlainModule] at h
  | str p s ih =>
    simp only [PlainModule] at h
    obtain ⟨hp, hs⟩ := h
    refine ⟨by simp [pathParts], fun x hx => ?_⟩
    simp only [pathParts, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · rcases hp with rfl | hp
      · simp [pathParts] at hx
      · exact (ih hp).2 x hx
    · exact hs

theorem pathParts_inj {m : Name} (h : PlainModule m) :
    ∀ {m' : Name}, PlainModule m' → pathParts m = pathParts m' → m = m' := by
  induction m with
  | anonymous => simp [PlainModule] at h
  | num p n _ => simp [PlainModule] at h
  | str p s ih =>
    intro m' h' he
    cases m' with
    | anonymous => simp [PlainModule] at h'
    | num p' n' => simp [PlainModule] at h'
    | str p' s' =>
      simp only [pathParts] at he
      obtain ⟨hp, hs⟩ := List.append_inj' he rfl
      simp only [List.cons.injEq, and_true] at hs
      subst hs
      simp only [PlainModule] at h h'
      rcases h.1 with rfl | hq <;> rcases h'.1 with rfl | hq'
      · rfl
      · exact absurd (by simpa [pathParts] using hp.symm) (plain_parts hq').1
      · exact absurd (by simpa [pathParts] using hp) (plain_parts hq).1
      · rw [ih hq hq' hp]

theorem modulePath_inj {m m' : Name} (h : PlainModule m) (h' : PlainModule m')
    (he : modulePath m = modulePath m') : m = m' := by
  unfold modulePath at he
  have e₁ := congrArg String.toList ((String.append_left_inj ".lean").mp he)
  have hsl : "/".toList = ['/'] := by simp
  simp only [String.toList_intercalate, hsl] at e₁
  have e₂ := congrArg (List.splitOn '/') e₁
  have hm := plain_parts h
  have hm' := plain_parts h'
  rw [List.splitOn_intercalate (ls := (pathParts m).map String.toList) '/' (by simpa using hm.2)
      (by simpa using hm.1),
    List.splitOn_intercalate (ls := (pathParts m').map String.toList) '/' (by simpa using hm'.2)
      (by simpa using hm'.1)] at e₂
  exact pathParts_inj h h' ((List.map_inj_right fun _ _ => String.toList_inj.mp).mp e₂)

theorem file_path {F : Facts} {m : Name} {a : String × ByteArray}
    (h : ((modFacts? F m).bind fun x => x.file.map (modulePath m, ·)) = some a) :
    a.1 = modulePath m := by
  cases hx : modFacts? F m with
  | none => simp [hx] at h
  | some x =>
    cases hf : x.file with
    | none => simp [hx, hf] at h
    | some b =>
      simp only [hx, hf, Option.bind, Option.map, Option.some.injEq] at h
      rw [← h]

/-- C4: `closureFiles` holds exactly the closure modules' (path, observed bytes). -/
theorem closureFiles_exact (F : Facts) (M : Name) (p : String) (b : ByteArray) :
    (p, b) ∈ closureFiles F M ↔
      ∃ m,
        ImportReach F M m ∧ modulePath m = p ∧ ∃ x, modFacts? F m = some x ∧ x.file = some b := by
  have hc : ∀ m, m ∈ closure F M ↔ ImportReach F M m := fun m => (closure_exact F M m).1
  unfold closureFiles
  simp only [List.mem_filterMap, hc]
  constructor
  · rintro ⟨m, hm, h⟩
    cases hx : modFacts? F m with
    | none => simp [hx] at h
    | some x =>
      cases hf : x.file with
      | none => simp [hx, hf] at h
      | some
        b' =>
        simp only [hx, hf, Option.bind, Option.map, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨m, hm, rfl, x, hx, hf⟩
  · rintro ⟨m, hm, rfl, x, hx, hf⟩
    exact ⟨m, hm, by simp [hx, hf]⟩

/-- C4: the frame's paths are distinct when every closure module is plain. -/
theorem closureFiles_distinct (F : Facts) (M : Name) (h : ∀ m, ImportReach F M m → PlainModule m) :
    ((closureFiles F M).map fun x => x.1).Nodup := by
  have hc : ∀ m, m ∈ closure F M ↔ ImportReach F M m := fun m => (closure_exact F M m).1
  unfold closureFiles
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map, List.pairwise_filterMap]
  refine
    List.Pairwise.imp_of_mem (fun {m m'} hm hm' hne => ?_)
      (List.nodup_iff_pairwise_ne.mp (closure_exact F M M).2)
  intro a ha a' ha' heq
  exact
    hne
      (modulePath_inj (h m ((hc m).mp hm)) (h m' ((hc m').mp hm'))
        ((file_path ha).symm.trans (heq.trans (file_path ha'))))

end FvdepAudit.Index.Statuses.Proof
