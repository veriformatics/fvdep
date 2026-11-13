import FvdepAudit.Doc.Spec

/-! J1 validity facts for document layouts: string sizes per D2 field kind, string arrays. -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Json (Value)
open FvdepCore.Ids FvdepCore.Doc FvdepAudit.Doc.Spec
open FvdepAudit.Json.Spec

theorem bytes_ofList (l : List Char) :
    (String.ofList l).utf8ByteSize = (l.map Char.utf8Size).sum := by
  induction l with
  | nil => rfl
  | cons c l
    ih =>
    rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih]
    simp

theorem size_eq_sum (s : String) : s.utf8ByteSize = (s.toList.map Char.utf8Size).sum := by
  have := bytes_ofList s.toList
  rwa [String.ofList_toList] at this

theorem sum_utf8Size_le (l : List Char) : (l.map Char.utf8Size).sum ≤ 4 * l.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have := Char.utf8Size_le_four c
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem size_le_length (s : String) : s.utf8ByteSize ≤ 4 * s.length := by
  rw [size_eq_sum, ← String.length_toList]
  exact sum_utf8Size_le _

theorem utc_size {s : String} (h : UtcText s) : s.utf8ByteSize ≤ maxStringBytes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, -⟩ := h
  have hl : s.length = 20 := by
    rw [← String.length_toList, hs]; rfl
  have := size_le_length s
  simp only [maxStringBytes]
  omega

theorem digest_size {s : String} (h : DigestText s) : s.utf8ByteSize ≤ maxStringBytes := by
  have hl : s.length = 64 := by
    rw [← String.length_toList]; exact h.1
  have := size_le_length s
  simp only [maxStringBytes]
  omega

theorem commit_size (c : Commit) : (toString c).utf8ByteSize ≤ maxStringBytes := by
  have hl : (toString c).length = 40 := by
    rw [← String.length_toList]
    simp [toString, Commit.chars, c.length_eq]
  have := size_le_length (toString c)
  simp only [maxStringBytes]
  omega

theorem profile_size {s : String} (h : ProfileText s) : s.utf8ByteSize ≤ maxStringBytes := by
  have := h.2.1
  simp only [maxStringBytes]
  omega

theorem constant_size {s : String} (h : ConstantText s) : s.utf8ByteSize ≤ maxStringBytes := by
  have := h.2.1
  simp only [maxStringBytes]
  omega

theorem spelling_size {s : String} (h : SpellingFits s) : s.utf8ByteSize ≤ maxStringBytes := h

theorem arg_size {b : Bool} {s : String} (h : ArgText b s) : s.utf8ByteSize ≤ maxStringBytes :=
  h.2.1

theorem strs_ints (xs : List String) : intsFitList (xs.map .str) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [intsFitList, intsFit] using ih

theorem strs_depth (xs : List String) : depthList (xs.map .str) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [depthList, depth] using ih

theorem strs_keys (xs : List String) : keysAscendList (xs.map .str) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [keysAscendList, keysAscend] using ih

theorem strs_fit (xs : List String) (h : ∀ x ∈ xs, x.utf8ByteSize ≤ maxStringBytes) :
    stringsFitList (xs.map .str) = true := by
  induction xs with
  | nil => rfl
  | cons x xs
    ih =>
    simp only [List.map_cons, stringsFitList, stringsFit, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h x (by simp), ih fun y hy => h y (by simp [hy])⟩

end FvdepAudit.Doc.Proof
