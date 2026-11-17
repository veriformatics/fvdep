import FvdepAudit.Hash.Proof.Frame
import FvdepAudit.Json.Proof.Corollaries
import FvdepAudit.Step.Spec

/-! U5 R8: the step frame read back (contract `docs/contracts/U5-sandbox.md` R8). -/

namespace FvdepAudit.Step.Proof

open FvdepCore.Step FvdepCore.Phase FvdepCore.Hash FvdepCore.Json FvdepAudit.Step.Spec
  FvdepAudit.Hash.Spec FvdepAudit.Hash.Proof

theorem ofJson_toJson (s : Status) : Status.ofJson s.toJson = some s := by
  obtain ⟨c, w, t⟩ := s
  cases c <;> simp [Status.toJson, Status.ofJson]

theorem toJson_of_ofJson {v : Value} {s : Status} (h : Status.ofJson v = some s) :
    v = s.toJson := by
  unfold Status.ofJson at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp [Status.toJson, Int.toNat_of_nonneg hc]
    · simp at h
  · split at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      simp [Status.toJson, Int.toNat_of_nonneg hn]
    · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [Status.toJson]
  · simp at h

theorem toJson_valid (s : Status) (h : StatusFits s) : FvdepAudit.Json.Spec.Valid s.toJson := by
  obtain ⟨c, w, t⟩ := s
  cases c <;>
    simp_all +decide [StatusFits, Status.toJson, FvdepAudit.Json.Spec.Valid,
      FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
      FvdepAudit.Json.Spec.stringsFit, FvdepAudit.Json.Spec.stringsFitMembers,
      FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
      FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers,
      FvdepAudit.Json.Spec.maxDepth]

theorem empty_le (p : String) : "" ≤ p :=
  String.not_lt.mp
    (by
      rw [String.lt_iff]; simp [List.not_lt_nil])

theorem sortByPath_eq (fs : List (String × ByteArray)) : sortByPath fs = byPath fs := rfl

/-- The status entry ahead of path-sorted files is already path-sorted. -/
theorem entries_sorted (sb : ByteArray) (files : List (String × ByteArray)) :
    byPath (("", sb) :: byPath files) = ("", sb) :: byPath files := by
  apply List.mergeSort_of_pairwise
  rw [List.pairwise_cons]
  exact
    ⟨fun g _ => decide_eq_true (empty_le g.1), List.pairwise_mergeSort path_trans path_total files⟩

theorem domain_perm {t : String} {fs gs : List (String × ByteArray)} (h : FrameDomain t fs)
    (p : fs.Perm gs) : FrameDomain t gs := by
  obtain ⟨hd, ht, hn, hf⟩ := h
  exact ⟨(p.map _).nodup_iff.mp hd, ht, p.length_eq ▸ hn, fun g hg => hf g (p.mem_iff.mpr hg)⟩

/-- R8 `FrameRead`. -/
theorem frame_read (s : Status) (files : List (String × ByteArray)) (hs : StatusFits s)
    (hdom : FrameDomain Tag.step.spelling (("", print s.toJson) :: files))
    (hsafe : ∀ f ∈ files, safePath f.1 = true) :
    read (frameOf s files) = some ⟨s, byPath files⟩ := by
  have hdom' := domain_perm hdom (((byPath_perm files).symm).cons ("", print s.toJson))
  have hdec : decode (print s.toJson) = .ok s.toJson :=
    FvdepAudit.Json.Proof.print_decode _ (toJson_valid s hs)
  have hall : (byPath files).all (safePath ·.1) = true := by
    rw [List.all_eq_true]
    exact fun f hf => hsafe f ((byPath_perm files).mem_iff.mp hf)
  simp [FvdepCore.Step.read, frameOf, sortByPath_eq, frame_decode _ _ hdom', entries_sorted, hdec,
    ofJson_toJson, hall, Except.toOption]

theorem fits_of_valid (s : Status) (h : FvdepAudit.Json.Spec.Valid s.toJson) : StatusFits s := by
  obtain ⟨c, w, t⟩ := s
  cases c <;>
    simp_all [StatusFits, Status.toJson, FvdepAudit.Json.Spec.Valid, FvdepAudit.Json.Spec.intsFit,
      FvdepAudit.Json.Spec.intsFitMembers, FvdepAudit.Json.Spec.stringsFit,
      FvdepAudit.Json.Spec.stringsFitMembers]

/-- R8 `FrameExact`. -/
theorem frame_exact (b : ByteArray) (o : Output) (h : read b = some o) :
    StatusFits o.status ∧
      FrameDomain Tag.step.spelling (("", print o.status.toJson) :: o.files) ∧
      (∀ f ∈ o.files, safePath f.1 = true) ∧ frameOf o.status o.files = b := by
  simp only [FvdepCore.Step.read, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨tag, entries⟩, hu, h⟩ := h
  split at h
  · rename_i sb files he
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, s, hs, h⟩ := h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      obtain ⟨⟨rfl, hsb⟩, hall⟩ := hc
      have hsb' : sb = print s.toJson := ByteArray.ext hsb
      subst hsb'
      obtain ⟨hdom, hpw, hframe⟩ := unframe_exact b _ _ hu
      simp only at he
      subst he
      have hdec : decode (print s.toJson) = .ok v := by
        cases hd : decode (print s.toJson) <;> simp_all [Except.toOption]
      have hvalid := FvdepAudit.Json.Proof.decode_valid _ _ hdec
      rw [toJson_of_ofJson hs] at hvalid
      have hle : files.Pairwise fun a b => decide (a.1 ≤ b.1) = true :=
        (List.pairwise_map.mp (List.pairwise_cons.mp hpw).2).imp fun hlt =>
          decide_eq_true (String.not_lt.mp (String.lt_asymm hlt))
      have hsorted : sortByPath files = files := List.mergeSort_of_pairwise hle
      refine ⟨fits_of_valid s hvalid, hdom, hall, ?_⟩
      simp only [frameOf, hsorted]
      exact hframe
    · simp at h
  · simp at h

end FvdepAudit.Step.Proof
