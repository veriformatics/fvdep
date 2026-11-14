import FvdepAudit.Doc.Proof.Valid
import FvdepAudit.Index.Spec

/-! A well-formed index's layout is a J1-valid value (contract U4 C6 `IndexValid`). -/

namespace FvdepAudit.Index.Proof

open FvdepCore.Json (Value)
open FvdepCore.Ids FvdepCore.Doc FvdepCore.Index FvdepAudit.Doc.Spec FvdepAudit.Index.Spec
open FvdepAudit.Json.Spec
open FvdepAudit.Doc.Proof (strs_ints strs_keys strs_depth strs_fit digest_size commit_size
  spelling_size)

/-! ## J1 validity of a well-formed index's layout -/

theorem ints_map {α : Type} (f : α → Value) (h : ∀ x, intsFit (f x) = true) :
    ∀ xs : List α, intsFitList (xs.map f) = true
  | [] => rfl
  | x :: xs => by simp [intsFitList, h x, ints_map f h xs]

theorem keys_map {α : Type} (f : α → Value) (h : ∀ x, keysAscend (f x) = true) :
    ∀ xs : List α, keysAscendList (xs.map f) = true
  | [] => rfl
  | x :: xs => by simp [keysAscendList, h x, keys_map f h xs]

theorem depth_map {α : Type} (f : α → Value) (n : Nat) (h : ∀ x, depth (f x) ≤ n) :
    ∀ xs : List α, depthList (xs.map f) ≤ n
  | [] => Nat.zero_le _
  | x :: xs => by
    simp only [List.map_cons, depthList]
    exact Nat.max_le.mpr ⟨h x, depth_map f n h xs⟩

theorem strings_map {α : Type} (f : α → Value) (P : α → Prop)
    (h : ∀ x, P x → stringsFit (f x) = true) :
    ∀ xs : List α, (∀ x ∈ xs, P x) → stringsFitList (xs.map f) = true
  | [], _ => rfl
  | x :: xs, hx => by
    simp only [List.map_cons, stringsFitList, Bool.and_eq_true]
    exact ⟨h x (hx x (by simp)), strings_map f P h xs fun y hy => hx y (by simp [hy])⟩

theorem text_size {cap : Nat} {s : String} (h : TextFits cap s) (hc : cap ≤ maxStringBytes) :
    s.utf8ByteSize ≤ maxStringBytes := Nat.le_trans h.2.1 hc

theorem status_size (s : Status) : (statusText s).utf8ByteSize ≤ maxStringBytes := by
  cases s <;> decide

theorem names_fit {xs : List String} (h : ∀ a ∈ xs, TextFits 1024 a) :
    stringsFitList (xs.map .str) = true := strs_fit xs fun x hx => text_size (h x hx) (by decide)

theorem obligation_ints (o : Obligation) : intsFit (obligationLayout o) = true := by
  simp [obligationLayout, intsFit, intsFitMembers, namesLayout, strs_ints]

theorem obligation_keys (o : Obligation) : keysAscend (obligationLayout o) = true := by
  simp [obligationLayout, keysAscend, keysAscendMembers, namesLayout, strs_keys]

theorem obligation_depth (o : Obligation) : depth (obligationLayout o) ≤ 2 := by
  simp [obligationLayout, depth, depthMembers, namesLayout, strs_depth]

theorem obligation_fit (o : Obligation) (h : ObligationWF o) :
    stringsFit (obligationLayout o) = true := by
  obtain ⟨hn, hax, -, -⟩ := h
  simp +decide [obligationLayout, stringsFit, stringsFitMembers, namesLayout, names_fit hax,
    text_size hn (by decide), status_size]

theorem compat_ints (c : Option Compat) : intsFit (compatLayout c) = true := by
  cases c <;> simp [compatLayout, intsFit, intsFitMembers, namesLayout, strs_ints]

theorem compat_keys (c : Option Compat) : keysAscend (compatLayout c) = true := by
  cases c <;> simp [compatLayout, keysAscend, keysAscendMembers, namesLayout, strs_keys]

theorem compat_depth (c : Option Compat) : depth (compatLayout c) ≤ 2 := by
  cases c <;> simp [compatLayout, depth, depthMembers, namesLayout, strs_depth]

theorem compat_fit (c : Option Compat) (h : ∀ x, c = some x → CompatWF x) :
    stringsFit (compatLayout c) = true := by
  cases c with
  | none => rfl
  | some x =>
    obtain ⟨⟨hax, -, -⟩, hv⟩ := h x rfl
    simp +decide [compatLayout, stringsFit, stringsFitMembers, namesLayout, names_fit hax,
      status_size, spelling_size hv]

theorem operation_ints (o : Operation) : intsFit (operationLayout o) = true := by
  simp [operationLayout, intsFit, intsFitMembers, compat_ints,
    ints_map obligationLayout obligation_ints]

theorem operation_keys (o : Operation) : keysAscend (operationLayout o) = true := by
  simp [operationLayout, keysAscend, keysAscendMembers, compat_keys,
    keys_map obligationLayout obligation_keys]

theorem operation_depth (o : Operation) : depth (operationLayout o) ≤ 4 := by
  have h1 := compat_depth o.compat
  have h2 := depth_map obligationLayout 2 obligation_depth o.obligations
  simp only [operationLayout, depth, depthMembers]
  omega

theorem operation_fit (o : Operation) (h : OperationWF o) :
    stringsFit (operationLayout o) = true := by
  obtain ⟨hm, hv, hd, hobs, -, hc⟩ := h
  simp +decide [operationLayout, stringsFit, stringsFitMembers, compat_fit o.compat hc,
    strings_map obligationLayout ObligationWF obligation_fit o.obligations hobs, digest_size hd,
    spelling_size hm, spelling_size hv]

theorem notice_ints (n : Notice) : intsFit (noticeLayout n) = true := by
  rcases n with ⟨m, x, r, rep⟩
  cases rep <;> simp [noticeLayout, replacementLayout, intsFit, intsFitMembers]

theorem notice_keys (n : Notice) : keysAscend (noticeLayout n) = true := by
  rcases n with ⟨m, x, r, rep⟩
  cases rep <;> simp [noticeLayout, replacementLayout, keysAscend, keysAscendMembers]

theorem notice_depth (n : Notice) : depth (noticeLayout n) ≤ 1 := by
  rcases n with ⟨m, x, r, rep⟩
  cases rep <;> simp [noticeLayout, replacementLayout, depth, depthMembers]

theorem notice_fit (n : Notice) (h : NoticeNodeWF n) : stringsFit (noticeLayout n) = true := by
  rcases n with ⟨m, x, r, rep⟩
  obtain ⟨hm, hx, hr, hrep⟩ := h
  cases rep with
  | none =>
    simp +decide [noticeLayout, replacementLayout, stringsFit, stringsFitMembers, spelling_size hm,
      spelling_size hx, text_size hr (by decide)]
  | some y =>
    simp +decide [noticeLayout, replacementLayout, stringsFit, stringsFitMembers, spelling_size hm,
      spelling_size hx, text_size hr (by decide), spelling_size (hrep y rfl)]

theorem removed_ints (r : Removed) : intsFit (removedLayout r) = true := by
  simp [removedLayout, intsFit, intsFitMembers]

theorem removed_keys (r : Removed) : keysAscend (removedLayout r) = true := by
  simp [removedLayout, keysAscend, keysAscendMembers]

theorem removed_depth (r : Removed) : depth (removedLayout r) ≤ 1 := by
  simp [removedLayout, depth, depthMembers]

theorem removed_fit (r : Removed) (h : RemovedNodeWF r) : stringsFit (removedLayout r) = true := by
  obtain ⟨hm, hx, hd, ht⟩ := h
  simp +decide [removedLayout, stringsFit, stringsFitMembers, spelling_size hm, spelling_size hx,
    digest_size hd, text_size ht (by decide), commit_size]

theorem index_keys (i : IndexFile) : keysAscend (indexLayout i) = true := by
  simp [indexLayout, keysAscend, keysAscendMembers, keys_map noticeLayout notice_keys,
    keys_map operationLayout operation_keys, keys_map removedLayout removed_keys]

theorem index_valid_layout (i : IndexFile) (h : IndexNodeWF i) :
    FvdepAudit.Json.Spec.Valid (indexLayout i) := by
  obtain ⟨ht, hops, -, hns, hrs⟩ := h
  refine ⟨?_, ?_, ?_, index_keys i⟩
  · simp [indexLayout, intsFit, intsFitMembers, ints_map noticeLayout notice_ints,
      ints_map operationLayout operation_ints, ints_map removedLayout removed_ints,
      FvdepAudit.Json.Spec.maxInt]
  · simp +decide [indexLayout, stringsFit, stringsFitMembers,
      strings_map noticeLayout NoticeNodeWF notice_fit i.notices hns,
      strings_map operationLayout OperationWF operation_fit i.operations hops,
      strings_map removedLayout RemovedNodeWF removed_fit i.removed hrs, text_size ht (by decide)]
  · have h1 := depth_map noticeLayout 1 notice_depth i.notices
    have h2 := depth_map operationLayout 4 operation_depth i.operations
    have h3 := depth_map removedLayout 1 removed_depth i.removed
    simp only [indexLayout, depth, depthMembers, maxDepth]
    omega

end FvdepAudit.Index.Proof
