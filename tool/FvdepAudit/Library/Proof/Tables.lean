import FvdepAudit.Doc.Proof.Rules
import FvdepAudit.Doc.Proof.Valid
import FvdepAudit.Hash.Proof.Frame
import FvdepAudit.Index.Proof.Claims
import FvdepAudit.Library.Spec
import FvdepAudit.Manifest.Proof.Rules

/-! Proofs: project selection (P3), the selection tables (L6), the source key (L1), the head record
(L5) — contract `docs/contracts/U5b-oracle.md` L10. -/

namespace FvdepAudit.Library.Proof

open FvdepCore.Json FvdepCore.Library FvdepCore.Project FvdepAudit.Library.Spec

/-! ## P3 -/

/-- Two splits at the first entry that is not absent agree. -/
theorem first_unique {pre pre' rest rest' : List (String × Found)} {x x' : String × Found}
    (hp : ∀ y ∈ pre, y.2 = .absent) (hp' : ∀ y ∈ pre', y.2 = .absent) (hx : x.2 ≠ .absent)
    (hx' : x'.2 ≠ .absent) (h : pre ++ x :: rest = pre' ++ x' :: rest') : x = x' := by
  induction pre generalizing pre' with
  | nil =>
    cases pre' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact h.1
    | cons y ys =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hp' y (by simp)) hx
  | cons y ys ih =>
    cases pre' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hp y (by simp)) hx'
    | cons z zs =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih (fun w hw => hp w (by simp [hw])) (fun w hw => hp' w (by simp [hw])) h.2

theorem selectProject_exact (s : Seen) (p : Pick) :
    pick (selectProject s) = p ↔ ProjectSpec s p := by
  cases s with
  | explicit d f =>
    cases f with
    | file =>
      simp only [selectProject, pick]
      constructor
      · rintro rfl
        exact .explicit d
      · intro h
        cases h with
        | explicit => rfl
        | explicitNot _ _ hf => exact absurd rfl hf
    | absent
    | link
    | special =>
      simp only [selectProject, pick]
      constructor
      · rintro rfl
        exact .explicitNot d _ (by decide)
      · intro h
        cases h
        rfl
  | ancestors ds =>
    cases hf : ds.find? (·.2 != .absent) with
    | none =>
      have hall : ∀ x ∈ ds, x.2 = .absent := by
        intro x hx
        have := List.find?_eq_none.1 hf x hx
        simpa using this
      simp only [selectProject, hf, pick]
      constructor
      · rintro rfl
        exact .none ds hall
      · intro h
        cases h with
        | nearest pre d rest _ => exact absurd (hall (d, .file) (by simp)) (by simp)
        | nearestIrregular pre d f rest _
          hfl =>
          have := hall (d, f) (by simp)
          rcases hfl with rfl | rfl <;> simp at this
        | none => rfl
    | some x =>
      obtain ⟨hx, pre, rest, hds, hpre⟩ := List.find?_eq_some_iff_append.1 hf
      have hpre' : ∀ y ∈ pre, y.2 = .absent := fun y hy => by simpa using hpre y hy
      have hx' : x.2 ≠ .absent := by simpa using hx
      rcases x with ⟨d, f⟩
      cases f with
      | absent => exact absurd rfl hx'
      | file =>
        simp only [selectProject, hf, pick]
        constructor
        · rintro rfl
          rw [hds]
          exact .nearest pre d rest hpre'
        · intro h
          cases h with
          | nearest pre2 d2 rest2
            hp2 =>
            have := first_unique hpre' hp2 (by simp) (by simp) hds.symm
            simp only [Prod.mk.injEq] at this
            rw [this.1]
          | nearestIrregular pre2 d2 f2 rest2 hp2
            hf2 =>
            have :=
              first_unique hpre' hp2 (by simp) (by rcases hf2 with rfl | rfl <;> simp) hds.symm
            simp only [Prod.mk.injEq] at this
            rcases hf2 with rfl | rfl <;> simp at this
          | none _ hall => exact absurd (hall (d, .file) (by simp [hds])) (by simp)
      | link
      | special =>
        simp only [selectProject, hf, pick]
        constructor
        · rintro rfl
          rw [hds]
          exact .nearestIrregular pre d _ rest hpre' (by simp)
        · intro h
          cases h with
          | nearest pre2 d2 rest2
            hp2 =>
            have := first_unique hpre' hp2 (by simp) (by simp) hds.symm
            simp at this
          | nearestIrregular => rfl
          | none _ hall =>
            exact
              absurd
                (hall _
                  (by
                    rw [hds]; exact List.mem_append_right _ (List.mem_cons_self ..)))
                hx'

/-! ## L6 -/

theorem start_exact (pin : Option String) (published : Bool) (s : Start) :
    start pin published = s ↔ StartSpec pin published s := by
  cases pin with
  | none =>
    simp only [start]
    constructor
    · rintro rfl
      exact .head published
    · intro h
      cases h
      rfl
  | some p =>
    cases published with
    | true =>
      simp only [start]
      constructor
      · rintro rfl
        exact .published p
      · intro h
        cases h
        rfl
    | false =>
      simp only [start]
      constructor
      · rintro rfl
        exact .pin p
      · intro h
        cases h
        rfl

theorem afterPin_exact (pin : String) (f : Fetch) (v : Verdict) :
    verdict (afterPin pin f) = v ↔ PinSpec pin f v := by
  cases f with
  | ok c =>
    simp only [afterPin, verdict, Option.isSome_none]
    constructor
    · rintro rfl
      exact .ok c
    · intro h
      cases h with
      | ok => rfl
      | failed _ hf => exact absurd rfl (hf c)
  | transport r
  | received r
  | localFault r
  | unclassified r =>
    simp only [afterPin, verdict]
    constructor
    · rintro rfl
      exact .failed _ fun c => by simp
    · intro h
      cases h
      rfl

theorem afterHead_exact (s : HeadState) (f : Fetch) (v : Verdict) :
    verdict (afterHead s f) = v ↔ HeadSpec s f v := by
  cases f with
  | ok c =>
    simp only [afterHead, verdict, Option.isSome_none]
    constructor
    · rintro rfl
      exact .ok s c
    · intro h
      cases h with
      | ok => rfl
      | other _ _ hok _ => exact absurd rfl (hok c)
  | transport r =>
    cases s with
    | valid h =>
      simp only [afterHead, verdict, Option.isSome_some]
      constructor
      · rintro rfl
        exact .fallback h r
      · intro hs
        cases hs with
        | fallback => rfl
        | other _ _ _ htr => exact absurd rfl (htr r)
    | absent =>
      simp only [afterHead, verdict]
      constructor
      · rintro rfl
        exact .never r
      · intro hs
        cases hs with
        | never => rfl
        | other _ _ _ htr => exact absurd rfl (htr r)
    | damaged why =>
      simp only [afterHead, verdict]
      constructor
      · rintro rfl
        exact .damaged why r
      · intro hs
        cases hs with
        | damaged => rfl
        | other _ _ _ htr => exact absurd rfl (htr r)
  | received r
  | localFault r
  | unclassified r =>
    simp only [afterHead, verdict]
    constructor
    · rintro rfl
      exact .other s _ (fun c => by simp) fun r => by simp
    · intro h
      cases h
      rfl

/-! ## L1 + L7 -/

theorem sourceKey_exact (h : ByteArray → String) (s t : String) :
    sourceKey h s = h s.toUTF8 ∧ (s ≠ t → s.toUTF8 ≠ t.toUTF8) := by
  refine ⟨rfl, fun hne he => hne ?_⟩
  have hu : FvdepAudit.Hash.Spec.utf8 s = FvdepAudit.Hash.Spec.utf8 t := by
    unfold FvdepAudit.Hash.Spec.utf8
    rw [he]
  have hs := FvdepAudit.Hash.Proof.text_utf8 s
  rw [hu, FvdepAudit.Hash.Proof.text_utf8 t] at hs
  exact (Option.some.inj hs).symm

theorem toolchain_exact (commit theirs ours : String) :
    toolchainRefusal commit theirs ours = none ↔
      FvdepCore.Index.Assemble.trimText theirs = ours := by
  unfold toolchainRefusal
  by_cases h : FvdepCore.Index.Assemble.trimText theirs = ours <;> simp [h]

/-! ## L5 -/

theorem headWF_iff (h : Head) : h.wf = true ↔ HeadWF h := by
  simp [Head.wf, HeadWF, FvdepAudit.Manifest.Proof.isCommit_iff, FvdepAudit.Doc.Proof.isUtc_iff,
    FvdepAudit.Doc.Proof.isDigest_iff, and_assoc]

theorem utc_length {s : String} (h : FvdepAudit.Doc.Spec.UtcText s) : s.length = 20 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, -⟩ := h
  rw [← String.length_toList, hs]
  rfl

theorem head_valid (h : Head) (hw : HeadWF h) : FvdepAudit.Json.Spec.Valid (headLayout h) := by
  obtain ⟨⟨c, hc⟩, hu, hd⟩ := hw
  have h1 : h.commit.length = 40 := by
    rw [hc, ← String.length_toList]
    simp [toString, FvdepCore.Ids.Commit.chars, c.length_eq]
  have h2 := utc_length hu
  have h3 : h.source.length = 64 := by
    rw [← String.length_toList]
    exact hd.1
  have s1 := FvdepAudit.Doc.Proof.size_le_length h.commit
  have s2 := FvdepAudit.Doc.Proof.size_le_length h.fetched
  have s3 := FvdepAudit.Doc.Proof.size_le_length h.source
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [headLayout, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
      FvdepAudit.Json.Spec.maxInt]
  · have f1 : h.commit.utf8ByteSize ≤ 65536 := by omega
    have f2 : h.fetched.utf8ByteSize ≤ 65536 := by omega
    have f3 : h.source.utf8ByteSize ≤ 65536 := by omega
    simp +decide [headLayout, FvdepAudit.Json.Spec.stringsFit,
      FvdepAudit.Json.Spec.stringsFitMembers, FvdepAudit.Json.Spec.maxStringBytes, f1, f2, f3]
  · simp [headLayout, FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
      FvdepAudit.Json.Spec.maxDepth]
  · simp [headLayout, FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers]

/-- L5: `headOf` reads back exactly the well-formed records' `head.json` bytes. -/
theorem head_exact (b : ByteArray) (h : Head) : headOf b = some h ↔ HeadWF h ∧ b = headBytes h := by
  constructor
  · intro hb
    unfold headOf at hb
    split at hb
    · rename_i c f s _
      simp only at hb
      split at hb
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at hb
        subst hb
        refine ⟨(headWF_iff _).1 hc.1, ?_⟩
        exact ByteArray.ext hc.2.symm
      · cases hb
    · cases hb
  · rintro ⟨hw, rfl⟩
    rcases h with ⟨c, f, s⟩
    have hv := head_valid _ hw
    unfold headOf
    rw [show headBytes ⟨c, f, s⟩ = (print (headLayout ⟨c, f, s⟩)).push 0x0A from rfl,
      FvdepAudit.Index.Proof.dropFinalLF_push, FvdepAudit.Json.Proof.print_decode _ hv]
    have hw' := (headWF_iff _).2 hw
    simp [hw', headText, Head.toJson, headLayout]

end FvdepAudit.Library.Proof
