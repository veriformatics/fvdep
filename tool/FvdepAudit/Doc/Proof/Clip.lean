import FvdepAudit.Doc.Proof.Valid

/-! D1: `clip` = `clipSpec` (`ClipExact`), and its result fits 65,536 bytes (`ClipBound`). -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Doc FvdepAudit.Doc.Spec

theorem bytes_cons (c : Char) (p : List Char) : bytes (c :: p) = c.utf8Size + bytes p := by
  simp [bytes]

theorem bytes_nil : bytes [] = 0 := rfl

theorem prefixes_ne_nil {α : Type} : ∀ xs : List α, [] ∈ prefixes xs
  | [] => by simp [prefixes]
  | _ :: _ => by simp [prefixes]

theorem longestPrefix_nil (n : Nat) : longestPrefix n [] = [] := by
  simp [longestPrefix, prefixes, bytes_nil]

theorem longestPrefix_cons (n : Nat) (c : Char) (cs : List Char) :
    longestPrefix n (c :: cs) =
      if c.utf8Size ≤ n then c :: longestPrefix (n - c.utf8Size) cs else [] := by
  unfold longestPrefix
  simp only [prefixes, List.filter_cons, bytes_nil, Nat.zero_le, decide_true, ite_true,
    List.filter_map, Function.comp_def, bytes_cons]
  by_cases hc : c.utf8Size ≤ n
  · simp only [hc, ite_true]
    have hf :
      (prefixes cs).filter (fun p => decide (c.utf8Size + bytes p ≤ n)) =
        (prefixes cs).filter (fun p => decide (bytes p ≤ n - c.utf8Size)) := by
      apply List.filter_congr
      intro p _
      simp only [decide_eq_decide]
      omega
    rw [hf]
    have hne : (prefixes cs).filter (fun p => decide (bytes p ≤ n - c.utf8Size)) ≠ [] := by
      intro h
      have := List.filter_eq_nil_iff.mp h [] (prefixes_ne_nil cs)
      simp [bytes_nil] at this
    obtain ⟨x, hx⟩ :
      ∃ x, ((prefixes cs).filter fun p => decide (bytes p ≤ n - c.utf8Size)).getLast? = some x := by
      cases h : ((prefixes cs).filter fun p => decide (bytes p ≤ n - c.utf8Size)).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
      | some x => exact ⟨x, rfl⟩
    simp [List.getLast?_cons, List.getLast?_map, hx]
  · have hf : (prefixes cs).filter (fun p => decide (c.utf8Size + bytes p ≤ n)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro p _
      simp only [decide_eq_true_eq]
      omega
    simp [hc, hf]

theorem fitPrefix_eq : ∀ (n : Nat) (cs : List Char), fitPrefix n cs = longestPrefix n cs
  | n, [] => by simp [fitPrefix, longestPrefix_nil]
  | n, c :: cs => by
    rw [longestPrefix_cons]
    by_cases hc : c.utf8Size ≤ n
    · simp [fitPrefix, hc, fitPrefix_eq (n - c.utf8Size) cs]
    · simp [fitPrefix, hc]

theorem fitPrefix_take :
    ∀ (m k : Nat) (cs : List Char), m ≤ k → fitPrefix m (cs.take k) = fitPrefix m cs
  | _, _, [], _ => by simp
  | m, 0, c :: cs, h => by
    have hm : m = 0 := by omega
    subst hm
    have := Char.utf8Size_pos c
    have hc : ¬c.utf8Size ≤ 0 := by omega
    simp [fitPrefix, hc]
  | m, k + 1, c :: cs, h => by
    by_cases hc : c.utf8Size ≤ m
    · have := Char.utf8Size_pos c
      simp [fitPrefix, hc, fitPrefix_take (m - c.utf8Size) k cs (by omega)]
    · simp [fitPrefix, hc]

theorem fitPrefix_bytes : ∀ (n : Nat) (cs : List Char), bytes (fitPrefix n cs) ≤ n
  | n, [] => by simp [fitPrefix, bytes_nil]
  | n, c :: cs => by
    by_cases hc : c.utf8Size ≤ n
    · have := fitPrefix_bytes (n - c.utf8Size) cs
      simp only [fitPrefix, hc, ite_true, bytes_cons]
      omega
    · simp [fitPrefix, hc, bytes_nil]

/-- D7 `ClipExact`. -/
theorem clip_exact (s : String) : clip s = clipSpec s := by
  unfold clip clipSpec
  split
  · rfl
  · rw [String.toList_copy_take, fitPrefix_take 65520 65520 _ (Nat.le_refl _), fitPrefix_eq]

/-- D7 `ClipBound`. -/
theorem clip_bound (s : String) : (clip s).utf8ByteSize ≤ 65536 := by
  unfold clip
  split
  · assumption
  · rw [String.utf8ByteSize_append, bytes_ofList]
    have := fitPrefix_bytes 65520 (s.take 65520).copy.toList
    have h12 : (" [truncated]" : String).utf8ByteSize = 12 := by decide
    rw [h12]
    unfold bytes at this
    omega

end FvdepAudit.Doc.Proof
