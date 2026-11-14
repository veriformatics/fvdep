import FvdepAudit.Protocol.Spec

/-! Proof: line framing (contract U4 B3). -/

namespace FvdepAudit.Protocol.Proof

open FvdepCore.Protocol FvdepAudit.Protocol.Spec

theorem segments_ne_nil : ∀ l : List UInt8, segments l ≠ []
  | [] => by simp [segments]
  | b :: rest => by
    simp only [segments]
    split
    · split <;> simp
    · simp

theorem segments_of_no_lf : ∀ {x : List UInt8}, 0x0A ∉ x → segments x = [x]
  | [], _ => rfl
  | b :: rest, h => by
    have hb : b ≠ 0x0A := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : 0x0A ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    simp [segments, segments_of_no_lf hr, hb]

theorem segments_append_lf {rest : List UInt8} :
    ∀ {x : List UInt8}, 0x0A ∉ x → segments (x ++ 0x0A :: rest) = x :: segments rest
  | [], _ => by
    simp only [List.nil_append, segments]
    cases h : segments rest with
    | nil => exact absurd h (segments_ne_nil rest)
    | cons s ss => rfl
  | b :: x, h => by
    have hb : b ≠ 0x0A := fun e => h (e ▸ List.mem_cons_self ..)
    have hx : 0x0A ∉ x := fun m => h (List.mem_cons_of_mem _ m)
    simp [segments, segments_append_lf hx, hb]

/-- `splitLines rest acc` = the lines of `acc.reverse ++ rest` (`acc` holds no LF). -/
theorem splitLines_eq :
    ∀ (rest acc : List UInt8), 0x0A ∉ acc → splitLines rest acc = linesSpec (acc.reverse ++ rest)
  | [], acc, h => by
    have hr : 0x0A ∉ acc.reverse := by simpa using h
    simp only [splitLines, List.append_nil, linesSpec, segments_of_no_lf hr]
    cases acc with
    | nil => simp
    | cons a as => simp
  | b :: rest, acc, h => by
    simp only [splitLines]
    split
    · rename_i hb
      have e : b = 0x0A := by simpa using hb
      subst e
      have hr : 0x0A ∉ acc.reverse := by simpa using h
      rw [splitLines_eq rest [] (by simp), List.reverse_nil, List.nil_append]
      simp only [linesSpec, segments_append_lf hr]
      have hne := segments_ne_nil rest
      cases hs : segments rest with
      | nil => exact absurd hs hne
      | cons s ss =>
        simp only [List.getLast?_cons_cons, List.dropLast_cons_cons]
        by_cases hc : (s :: ss).getLast? = some [] <;> simp [hc]
    · rename_i hb
      have hb' : b ≠ 0x0A := by simpa using hb
      rw [splitLines_eq rest (b :: acc)
          (by
            simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hb', h⟩)]
      simp

theorem lines_exact (b : ByteArray) : (lines b).map (·.data.toList) = linesSpec b.data.toList := by
  simp only [lines, List.map_map]
  rw [show
      ((fun l : ByteArray => l.data.toList) ∘ fun l : List UInt8 => (⟨l.toArray⟩ : ByteArray)) = id
      from rfl,
    List.map_id, splitLines_eq _ [] (by simp)]
  rfl

end FvdepAudit.Protocol.Proof
