import FvdepAudit.Export.Proof
import FvdepAudit.Oracle.Command.Spec
import FvdepAudit.Protocol.Proof.Lines

/-! V1–V2 + V4's budget against the run written apart: the staging over byte offsets = V2's
outcome over `Protocol.lines` (the first line passing a budget names it), the replies' incremental
encoding = their whole bytes against the batch budget. -/

namespace FvdepAudit.Oracle.Command.Proof

open Lean FvdepCore FvdepCore.Protocol FvdepCore.Oracle FvdepCore.Oracle.Command
open FvdepAudit.Oracle.Command.Spec

/-! ## V4: the batch budget over the whole encoding -/

theorem foldl_append_size (xs : List ByteArray) (acc : ByteArray) :
    (xs.foldl (· ++ ·) acc).size = acc.size + (xs.map ByteArray.size).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs
    ih =>
    simp only [List.foldl_cons, ih, ByteArray.size_append, List.map_cons, List.sum_cons]
    omega

/-- The incremental encoding = the whole encoding against the budget (from a start within it, or
with at least one reply). -/
theorem encodeAll_eq (cap : Nat) (rs : List Reply) (acc : ByteArray)
    (h : rs ≠ [] ∨ acc.size ≤ cap) :
    encodeAll cap rs acc =
      if cap < ((rs.map encodeReply).foldl (· ++ ·) acc).size then none
      else some ((rs.map encodeReply).foldl (· ++ ·) acc) := by
  induction rs generalizing acc with
  | nil =>
    simp only [ne_eq, not_true_eq_false, false_or] at h
    simp only [encodeAll, List.map_nil, List.foldl_nil]
    rw [ite_eq_right (by omega)]
  | cons r rest ih =>
    simp only [encodeAll, List.map_cons, List.foldl_cons]
    have hge := foldl_append_size (rest.map encodeReply) (acc ++ encodeReply r)
    by_cases hc : cap < (acc ++ encodeReply r).size
    · rw [ite_eq_left hc, ite_eq_left (by omega)]
    · rw [ite_eq_right hc]
      exact ih (acc ++ encodeReply r) (.inr (by omega))

/-- The plan's call: from the empty start. -/
theorem encodeAll_empty (cap : Nat) (rs : List Reply) :
    encodeAll cap rs .empty =
      if cap < ((rs.map encodeReply).foldl (· ++ ·) ByteArray.empty).size then none
      else some ((rs.map encodeReply).foldl (· ++ ·) ByteArray.empty) :=
  encodeAll_eq cap rs ByteArray.empty (.inr (Nat.zero_le _))

/-! ## V1–V2: the staging over offsets = V2's outcome over the lines -/

/-- The plan's staging, line by line over a list. -/
def stageList (lim : Command.Limits) (sig : Sig) : List ByteArray → Staging → Except Over Staging
  | [], st => .ok st
  | l :: ls, st =>
    match decodeRequest sig l with
    | .error r =>
      let c := st.charged + (encodeReply (.invalid r)).size
      if lim.batchBytes < c then .error .batch
      else
        stageList lim sig ls
          { st with
            reqs := .invalid r :: st.reqs, charged := c }
    | .ok xs =>
      let w := Wire.encodeArgs xs ++ "\n"
      let n := st.stagedBytes + w.utf8ByteSize
      if lim.stagingBytes < n then .error .staging
      else
        stageList lim sig ls
          { st with
            reqs := .valid :: st.reqs
            staged := st.staged ++ w
            stagedBytes := n }

/-- The lines from offset `i` (U4 B3's segments, as byte arrays). -/
def linesAt (b : ByteArray) (i : Nat) : List ByteArray :=
  (FvdepAudit.Protocol.Spec.linesSpec (b.data.toList.drop i)).map fun l => ⟨l.toArray⟩

theorem bytes_eta (x : ByteArray) : (⟨x.data.toList.toArray⟩ : ByteArray) = x := rfl

/-- The offset walk from `i` = the list walk over the lines from `i`. -/
theorem stageFrom_list (lim : Command.Limits) (sig : Sig) (b : ByteArray) (i : Nat) (st : Staging) :
    stageFrom lim sig b i st = stageList lim sig (linesAt b i) st := by
  rw [stageFrom.eq_def]
  by_cases h : i < b.size
  · simp only [h, ↓reduceDIte]
    have := Export.le_lineEnd b i (Nat.le_of_lt h)
    rw [linesAt, FvdepAudit.Export.Proof.lines_drop b i h, List.map_cons, bytes_eta, stageList]
    cases decodeRequest sig (b.extract i (Export.lineEnd b i)) with
    | error r =>
      dsimp only
      split
      · rfl
      · rw [stageFrom_list]
        rfl
    | ok xs =>
      dsimp only
      split
      · rfl
      · rw [stageFrom_list]
        rfl
  · simp only [h, ↓reduceDIte]
    rw [linesAt, FvdepAudit.Export.Proof.lines_end b i h]
    rfl
termination_by b.size - i
decreasing_by all_goals omega

/-- The lines from offset 0 = `Protocol.lines`. -/
theorem linesAt_zero (b : ByteArray) : linesAt b 0 = Protocol.lines b := by
  have h := FvdepAudit.Protocol.Proof.lines_exact b
  rw [linesAt, List.drop_zero, ← h, List.map_map]
  conv =>
    rhs; rw [← List.map_id (Protocol.lines b)]
  rfl

/-- The state after the lines `pre` within both budgets. -/
def stateOf (sig : Sig) (pre : List ByteArray) : Staging :=
  { reqs := (pre.map (reqOf sig)).reverse
    staged := String.join (pre.map (stagedOf sig))
    stagedBytes := (String.join (pre.map (stagedOf sig))).utf8ByteSize
    charged := (pre.map (chargeOf sig)).sum }

theorem within_prefix {lim : Command.Limits} {sig : Sig} {xs ys : List ByteArray}
    (h : Within lim sig (xs ++ ys)) : Within lim sig xs := by
  obtain ⟨h1, h2⟩ := h
  simp only [List.map_append, String.join_append, String.utf8ByteSize_append,
    List.sum_append] at h1 h2
  exact ⟨by omega, by omega⟩

/-- One refused line: the state after it + its budget. -/
theorem state_invalid (sig : Sig) (pre : List ByteArray) (l : ByteArray) (r : String)
    (hd : decodeRequest sig l = .error r) :
    stateOf sig (pre ++ [l]) =
      { stateOf sig pre with
        reqs := .invalid r :: (stateOf sig pre).reqs
        charged := (stateOf sig pre).charged + (encodeReply (.invalid r)).size } := by
  simp [stateOf, reqOf, stagedOf, chargeOf, hd]

theorem state_valid (sig : Sig) (pre : List ByteArray) (l : ByteArray) (xs : List Val)
    (hd : decodeRequest sig l = .ok xs) :
    stateOf sig (pre ++ [l]) =
      { stateOf sig pre with
        reqs := .valid :: (stateOf sig pre).reqs
        staged := (stateOf sig pre).staged ++ (Wire.encodeArgs xs ++ "\n")
        stagedBytes :=
          (stateOf sig pre).stagedBytes + (Wire.encodeArgs xs ++ "\n").utf8ByteSize } := by
  simp [stateOf, reqOf, stagedOf, chargeOf, hd, String.utf8ByteSize_append]

theorem within_invalid (lim : Command.Limits) (sig : Sig) (pre : List ByteArray) (l : ByteArray)
    (r : String) (hd : decodeRequest sig l = .error r) (hw : Within lim sig pre) :
    Within lim sig (pre ++ [l]) ↔
      (stateOf sig pre).charged + (encodeReply (.invalid r)).size ≤ lim.batchBytes := by
  obtain ⟨h1, h2⟩ := hw
  simp only [Within, stateOf, List.map_append, List.map_cons, List.map_nil, String.join_append,
    String.utf8ByteSize_append, List.sum_append, List.sum_cons, List.sum_nil, stagedOf, chargeOf,
    hd]
  simp
  omega

theorem within_valid (lim : Command.Limits) (sig : Sig) (pre : List ByteArray) (l : ByteArray)
    (xs : List Val) (hd : decodeRequest sig l = .ok xs) (hw : Within lim sig pre) :
    Within lim sig (pre ++ [l]) ↔
      (stateOf sig pre).stagedBytes + (Wire.encodeArgs xs ++ "\n").utf8ByteSize ≤
        lim.stagingBytes := by
  obtain ⟨h1, h2⟩ := hw
  simp only [Within, stateOf, List.map_append, List.map_cons, List.map_nil, String.join_append,
    String.utf8ByteSize_append, List.sum_append, List.sum_cons, List.sum_nil, stagedOf, chargeOf,
    hd]
  simp
  omega

/-- The list walk from the state after `pre` (within both budgets) ends `ok` exactly when every
line stays within both budgets, with the state after all of them. -/
theorem stageList_ok (lim : Command.Limits) (sig : Sig) (ls : List ByteArray) :
    ∀ (pre : List ByteArray) (st : Staging),
      Within lim sig pre →
        (stageList lim sig ls (stateOf sig pre) = .ok st ↔
          Within lim sig (pre ++ ls) ∧ st = stateOf sig (pre ++ ls)) := by
  induction ls with
  | nil =>
    intro pre st hw
    simp only [stageList, Except.ok.injEq, List.append_nil]
    constructor
    · rintro rfl
      exact ⟨hw, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  | cons l rest ih =>
    intro pre st hw
    simp only [stageList]
    cases hd : decodeRequest sig l with
    | error r =>
      dsimp only
      by_cases hc : lim.batchBytes < (stateOf sig pre).charged + (encodeReply (.invalid r)).size
      · rw [ite_eq_left hc]
        simp only [reduceCtorEq, false_iff, not_and]
        intro hall
        have hpre : Within lim sig (pre ++ [l]) := within_prefix (ys := rest) (by simpa using hall)
        have := (within_invalid lim sig pre l r hd hw).mp hpre
        omega
      · rw [ite_eq_right hc]
        have hw' : Within lim sig (pre ++ [l]) :=
          (within_invalid lim sig pre l r hd hw).mpr (by omega)
        rw [← state_invalid sig pre l r hd, ih (pre ++ [l]) st hw']
        simp
    | ok xs =>
      dsimp only
      by_cases hc :
        lim.stagingBytes < (stateOf sig pre).stagedBytes + (Wire.encodeArgs xs ++ "\n").utf8ByteSize
      · rw [ite_eq_left hc]
        simp only [reduceCtorEq, false_iff, not_and]
        intro hall
        have hpre : Within lim sig (pre ++ [l]) := within_prefix (ys := rest) (by simpa using hall)
        have := (within_valid lim sig pre l xs hd hw).mp hpre
        omega
      · rw [ite_eq_right hc]
        have hw' : Within lim sig (pre ++ [l]) :=
          (within_valid lim sig pre l xs hd hw).mpr (by omega)
        rw [← state_valid sig pre l xs hd, ih (pre ++ [l]) st hw']
        simp

/-- A line's budget class (V2). -/
def classOf (sig : Sig) (l : ByteArray) : Over := if reqOf sig l = .valid then .staging else .batch

/-- The list walk from the state after `pre` ends refused exactly at the first line whose addition
passes a budget, naming that line's budget. -/
theorem stageList_error (lim : Command.Limits) (sig : Sig) (ls : List ByteArray) :
    ∀ (pre : List ByteArray) (o : Over),
      Within lim sig pre →
        (stageList lim sig ls (stateOf sig pre) = .error o ↔
          ∃ mid l post,
            ls = mid ++ l :: post ∧
              Within lim sig (pre ++ mid) ∧
              ¬Within lim sig (pre ++ mid ++ [l]) ∧ o = classOf sig l) := by
  induction ls with
  | nil =>
    intro pre o hw
    simp only [stageList, reduceCtorEq, false_iff, not_exists, not_and]
    intro mid l post h
    simp at h
  | cons l rest ih =>
    intro pre o hw
    simp only [stageList]
    cases hd : decodeRequest sig l with
    | error r =>
      dsimp only
      have hcl : classOf sig l = .batch := by simp [classOf, reqOf, hd]
      by_cases hc : lim.batchBytes < (stateOf sig pre).charged + (encodeReply (.invalid r)).size
      · rw [ite_eq_left hc]
        have hn : ¬Within lim sig (pre ++ [l]) := fun h =>
          absurd ((within_invalid lim sig pre l r hd hw).mp h) (by omega)
        simp only [Except.error.injEq]
        constructor
        · rintro rfl
          exact ⟨[], l, rest, rfl, by simpa using hw, by simpa using hn, hcl.symm⟩
        · rintro ⟨mid, l', post, hs, hwm, hnw, rfl⟩
          cases mid with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact hcl.symm
          | cons x mid =>
            simp only [List.cons_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact absurd (within_prefix (ys := mid) (by simpa using hwm)) hn
      · rw [ite_eq_right hc]
        have hw' : Within lim sig (pre ++ [l]) :=
          (within_invalid lim sig pre l r hd hw).mpr (by omega)
        rw [← state_invalid sig pre l r hd, ih (pre ++ [l]) o hw']
        constructor
        · rintro ⟨mid, l', post, rfl, hwm, hnw, ho⟩
          exact ⟨l :: mid, l', post, rfl, by simpa using hwm, by simpa using hnw, ho⟩
        · rintro ⟨mid, l', post, hs, hwm, hnw, ho⟩
          cases mid with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact absurd (by simpa using hw') hnw
          | cons x mid =>
            simp only [List.cons_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact ⟨mid, l', post, rfl, by simpa using hwm, by simpa using hnw, ho⟩
    | ok xs =>
      dsimp only
      have hcl : classOf sig l = .staging := by simp [classOf, reqOf, hd]
      by_cases hc :
        lim.stagingBytes < (stateOf sig pre).stagedBytes + (Wire.encodeArgs xs ++ "\n").utf8ByteSize
      · rw [ite_eq_left hc]
        have hn : ¬Within lim sig (pre ++ [l]) := fun h =>
          absurd ((within_valid lim sig pre l xs hd hw).mp h) (by omega)
        simp only [Except.error.injEq]
        constructor
        · rintro rfl
          exact ⟨[], l, rest, rfl, by simpa using hw, by simpa using hn, hcl.symm⟩
        · rintro ⟨mid, l', post, hs, hwm, hnw, rfl⟩
          cases mid with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact hcl.symm
          | cons x mid =>
            simp only [List.cons_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact absurd (within_prefix (ys := mid) (by simpa using hwm)) hn
      · rw [ite_eq_right hc]
        have hw' : Within lim sig (pre ++ [l]) :=
          (within_valid lim sig pre l xs hd hw).mpr (by omega)
        rw [← state_valid sig pre l xs hd, ih (pre ++ [l]) o hw']
        constructor
        · rintro ⟨mid, l', post, rfl, hwm, hnw, ho⟩
          exact ⟨l :: mid, l', post, rfl, by simpa using hwm, by simpa using hnw, ho⟩
        · rintro ⟨mid, l', post, hs, hwm, hnw, ho⟩
          cases mid with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact absurd (by simpa using hw') hnw
          | cons x mid =>
            simp only [List.cons_append, List.cons.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            exact ⟨mid, l', post, rfl, by simpa using hwm, by simpa using hnw, ho⟩

theorem stateOf_nil (sig : Sig) : stateOf sig [] = {} := rfl

theorem within_nil (lim : Command.Limits) (sig : Sig) : Within lim sig [] := by simp [Within]

/-- Two first-failing decompositions of one list name the same line. -/
theorem first_unique {lim : Command.Limits} {sig : Sig} {pre1 pre2 post1 post2 : List ByteArray}
    {l1 l2 : ByteArray} (hs : pre1 ++ l1 :: post1 = pre2 ++ l2 :: post2) (hw1 : Within lim sig pre1)
    (hn1 : ¬Within lim sig (pre1 ++ [l1])) (hw2 : Within lim sig pre2)
    (hn2 : ¬Within lim sig (pre2 ++ [l2])) : l1 = l2 := by
  rcases List.append_eq_append_iff.mp hs with ⟨a, rfl, ha⟩ | ⟨c, rfl, hc⟩
  · cases a with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at ha
      exact ha.1
    | cons x a =>
      simp only [List.cons_append, List.cons.injEq] at ha
      obtain ⟨rfl, _⟩ := ha
      exact absurd (within_prefix (ys := a) (by simpa using hw2)) hn1
  · cases c with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hc
      exact hc.1.symm
    | cons x c =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd (within_prefix (ys := c) (by simpa using hw1)) hn2

/-- V2's outcome over a list of lines is unique. -/
theorem staged_unique {lim : Command.Limits} {sig : Sig} {ls : List ByteArray}
    {r1 r2 : Except Over (List Req × String)} (h1 : Staged lim sig ls r1)
    (h2 : Staged lim sig ls r2) : r1 = r2 := by
  rcases h1 with ⟨hw, rfl⟩ | ⟨pre1, l1, post1, rfl, hw1, hn1, rfl⟩ <;>
    rcases h2 with ⟨hw', rfl⟩ | ⟨pre2, l2, post2, hs, hw2, hn2, rfl⟩
  · rfl
  · subst hs
    exact absurd (within_prefix (ys := post2) (by simpa using hw)) hn2
  · exact absurd (within_prefix (ys := post1) (by simpa using hw')) hn1
  · rw [first_unique hs hw1 hn1 hw2 hn2]

/-- The plan's staging (from offset 0, the empty state) meets V2's outcome over the lines. -/
theorem staged_plan (lim : Command.Limits) (sig : Sig) (b : ByteArray) :
    Staged lim sig (Protocol.lines b)
      ((stageFrom lim sig b 0 {}).map fun st => (st.reqs.reverse, st.staged)) := by
  rw [stageFrom_list, linesAt_zero, ← stateOf_nil sig]
  cases hs : stageList lim sig (Protocol.lines b) (stateOf sig []) with
  | ok st =>
    obtain ⟨hw, rfl⟩ := (stageList_ok lim sig _ [] st (within_nil lim sig)).mp hs
    refine .inl ⟨by simpa using hw, ?_⟩
    simp [Except.map, stateOf]
  | error
    o =>
    obtain ⟨mid, l, post, hl, hwm, hnw, rfl⟩ :=
      (stageList_error lim sig _ [] o (within_nil lim sig)).mp hs
    exact .inr ⟨mid, l, post, hl, by simpa using hwm, by simpa using hnw, rfl⟩

/-- A statement about V2's outcome = that statement about the plan's staging. -/
theorem staged_iff (lim : Command.Limits) (sig : Sig) (b : ByteArray)
    (P : Except Over (List Req × String) → Prop) :
    (∃ r, Staged lim sig (Protocol.lines b) r ∧ P r) ↔
      P ((stageFrom lim sig b 0 {}).map fun st => (st.reqs.reverse, st.staged)) := by
  constructor
  · rintro ⟨r, hr, hp⟩
    rw [staged_unique hr (staged_plan lim sig b)] at hp
    exact hp
  · intro hp
    exact ⟨_, staged_plan lim sig b, hp⟩

end FvdepAudit.Oracle.Command.Proof
