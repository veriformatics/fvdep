import FvdepAudit.Json.Proof.Decode.Complete
import FvdepAudit.Json.Proof.Decode.GrammarDepth
import FvdepAudit.Json.Proof.Decode.Normalize
import FvdepAudit.Json.Proof.Decode.Post
import FvdepAudit.Json.Proof.Decode.Site

namespace FvdepAudit.Json.Proof

open FvdepCore.Json

theorem maxDepth_eq : maxDepth = FvdepAudit.Json.Spec.maxDepth := rfl

theorem text_iff_parse (b : ByteArray) (v : Value) :
    FvdepAudit.Json.Spec.Text b.data.toList v ↔
      ∃ j, parseValue b (2 * b.size + 2) (skipWs b 0) = some (v, j) ∧ skipWs b j = b.size := by
  constructor
  · rintro ⟨r₁, r₂, hw₁, hv, hw₂⟩
    have hw₁ : FvdepAudit.Json.Spec.Ws (bytesAt b 0) r₁ := hw₁
    have hstart := skipWs_complete hw₁
    rw [← hstart] at hv
    rcases parseValue_complete hv (by omega : 2 * (b.size - skipWs b 0) + 1 ≤ 2 * b.size + 2) with
      ⟨j, hp, hr⟩
    rw [← hr] at hw₂
    have hend := skipWs_complete hw₂
    have hj := (parseValue_sound hp).2.2
    exact ⟨j, hp, (bytesAt_nil_iff (skipWs_le hj)).mp hend⟩
  · rintro ⟨j, hp, hj⟩
    have hw := skipWs_sound b j
    rw [hj, bytesAt_nil (by omega : b.size ≤ b.size)] at hw
    exact ⟨bytesAt b (skipWs b 0), bytesAt b j, skipWs_sound b 0, (parseValue_sound hp).1, hw⟩

theorem text_unique :
    ∀ (bs : FvdepAudit.Json.Spec.Bytes) (v w : Value),
      FvdepAudit.Json.Spec.Text bs v → FvdepAudit.Json.Spec.Text bs w → v = w := by
  intro bs v w hv hw
  let b := bs.toByteArray
  have hbytes : b.data.toList = bs := List.toList_data_toByteArray
  rw [← hbytes] at hv hw
  rcases (text_iff_parse b v).mp hv with ⟨j, hp, _⟩
  rcases (text_iff_parse b w).mp hw with ⟨k, hq, _⟩
  exact congrArg Prod.fst (Option.some.inj (hp.symm.trans hq))

theorem decode_outcome (b : ByteArray) : FvdepAudit.Json.Spec.Outcome b.data.toList (decode b) := by
  unfold decode
  rw [maxDepth_eq, scanDepth_eq]
  split
  · rename_i hd
    exact .deep hd
  · rename_i hd
    have hdepth :
      FvdepAudit.Json.Spec.lexicalDepth b.data.toList ≤ FvdepAudit.Json.Spec.maxDepth := by omega
    cases hp : parseValue b (2 * b.size + 2) (skipWs b 0) with
    | none =>
      apply FvdepAudit.Json.Spec.Outcome.malformed hdepth
      intro v ht
      rcases (text_iff_parse b v).mp ht with ⟨j, hq, _⟩
      simp [hp] at hq
    | some p =>
      rcases p with ⟨v, j⟩
      by_cases hend : skipWs b j = b.size
      · have ht := (text_iff_parse b v).mpr ⟨j, hp, hend⟩
        by_cases hs : stringsFit v = true
        · by_cases hdup : hasDupKey v = true
          · simpa [hend, hs, hdup, dupSite_site] using
              FvdepAudit.Json.Spec.Outcome.duplicate hdepth ht
                (by simpa only [stringsFit_eq] using hs) (by simpa only [hasDupKey_eq] using hdup)
          · have hdup' : FvdepAudit.Json.Spec.hasDupKey v = false := by
              rw [← hasDupKey_eq]
              exact Bool.eq_false_iff.mpr hdup
            simpa [hend, hs, hdup, canon_eq] using
              FvdepAudit.Json.Spec.Outcome.ok hdepth ht (by simpa only [stringsFit_eq] using hs)
                hdup'
        · have hs' : FvdepAudit.Json.Spec.stringsFit v = false := by
            rw [← stringsFit_eq]
            exact Bool.eq_false_iff.mpr hs
          simpa [hend, hs] using FvdepAudit.Json.Spec.Outcome.long hdepth ht hs'
      · have hn : ∀ w, ¬FvdepAudit.Json.Spec.Text b.data.toList w := by
          intro w ht
          rcases (text_iff_parse b w).mp ht with ⟨k, hq, hk⟩
          have he := Option.some.inj (hp.symm.trans hq)
          have hjk : j = k := congrArg Prod.snd he
          exact hend ((congrArg (skipWs b) hjk).trans hk)
        simpa [hend] using FvdepAudit.Json.Spec.Outcome.malformed hdepth hn

theorem outcome_decode {b : ByteArray} {r : Except DecodeError Value}
    (h : FvdepAudit.Json.Spec.Outcome b.data.toList r) : decode b = r := by
  cases h with
  | deep hd => simp [decode, scanDepth_eq, maxDepth_eq, hd]
  | malformed hd
    hn =>
    have hdeep : ¬maxDepth < scanDepth b := by
      rw [maxDepth_eq, scanDepth_eq]; omega
    unfold decode
    simp only [hdeep, ite_false]
    cases hp : parseValue b (2 * b.size + 2) (skipWs b 0) with
    | none => rfl
    | some p =>
      rcases p with ⟨v, j⟩
      by_cases hend : skipWs b j = b.size
      · exact False.elim (hn v ((text_iff_parse b v).mpr ⟨j, hp, hend⟩))
      · simp [hend]
  | long hd ht
    hs =>
    have hdeep : ¬maxDepth < scanDepth b := by
      rw [maxDepth_eq, scanDepth_eq]; omega
    rcases (text_iff_parse b _).mp ht with ⟨j, hp, hj⟩
    simp [decode, hdeep, hp, hj, stringsFit_eq, hs]
  | duplicate hd ht hs
    hdup =>
    have hdeep : ¬maxDepth < scanDepth b := by
      rw [maxDepth_eq, scanDepth_eq]; omega
    rcases (text_iff_parse b _).mp ht with ⟨j, hp, hj⟩
    simp [decode, hdeep, hp, hj, stringsFit_eq, hs, hasDupKey_eq, hdup, dupSite_site]
  | ok hd ht hs
    hdup =>
    have hdeep : ¬maxDepth < scanDepth b := by
      rw [maxDepth_eq, scanDepth_eq]; omega
    rcases (text_iff_parse b _).mp ht with ⟨j, hp, hj⟩
    simp [decode, hdeep, hp, hj, stringsFit_eq, hs, hasDupKey_eq, hdup, canon_eq]

theorem decode_exact :
    ∀ (b : ByteArray) (r : Except DecodeError Value),
      decode b = r ↔ FvdepAudit.Json.Spec.Outcome b.data.toList r := by
  intro b r
  constructor
  · intro h
    rw [← h]
    exact decode_outcome b
  · exact outcome_decode

theorem decode_valid :
    ∀ (b : ByteArray) (v : Value), decode b = .ok v → FvdepAudit.Json.Spec.Valid v := by
  intro b v h
  have ho := (decode_exact b (.ok v)).mp h
  cases ho with
  | @ok w hd ht hs hdup =>
    rcases canon_invariants w with ⟨hi, hs', hd'⟩
    refine ⟨hi.trans (text_intsFit ht), hs'.trans hs, ?_, canon_keysAscend w hdup⟩
    rw [hd', ← lexicalDepth_text ht]
    exact hd

end FvdepAudit.Json.Proof
