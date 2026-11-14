import FvdepAudit.Sys.Proof.OldOrNew

/-! F4 `ReplaceSingleTouch`. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

/-- F4 `ReplaceSingleTouch`: one rename step is the only call naming the target (none when the
run stops before it); every write, the data fsync + the temp's close between its create and the
rename use the descriptor that create returned; nothing after the rename writes. -/
theorem replace_single_touch (dir : Path) (name : Name) (pid size : Nat) (script : Script)
    (hc : Consistent ((replace scripted dir name pid size).run script).events) :
    (∀ e ∈ ((replace scripted dir name pid size).run script).events,
        ¬Names (targetText dir name) e.request) ∨
      ∃ (walk data renames rest : Trace) (temp target : Path) (mode : Mode) (fd : Nat) (renamed :
        Except Cause Nat),
        ((replace scripted dir name pid size).run script).events =
            walk ++ ⟨.create temp mode, .ok fd⟩ :: data ++ renames ++ rest ∧
          target.toString = targetText dir name ∧
          Retry (.rename temp target) 64 renames renamed ∧
          writerOnly fd data ∧
          (∀ e ∈ rest, ∀ g o c, e.request ≠ .write g o c) ∧
          ∀ e ∈ walk ++ ⟨.create temp mode, .ok fd⟩ :: data ++ rest,
            ¬Names (targetText dir name) e.request := by
  have hR :
    Replace dir name pid size ((replace scripted dir name pid size).run script).events
      ((replace scripted dir name pid size).run script).result :=
    replace_sound dir name pid size script hc
  generalize ((replace scripted dir name pid size).run script).result = R at hR
  generalize ((replace scripted dir name pid size).run script).events = ev at hR ⊢
  cases hR with
  | noTemp walk => exact .inl fun e he => (walk_inert walk e he).1
  | @opened created rest temp fd result walk
    body =>
    obtain ⟨pre, mode, k, hcr, named⟩ := walk_ok walk
    have walkN : ∀ e ∈ created, ¬Names (targetText dir name) e.request := fun e he =>
      (walk_inert walk e he).1
    have writesN :
      ∀ {w r}, Writes fd 0 size w r → ∀ e ∈ w, ¬Names (targetText dir name) e.request :=
      fun data e he => by
      obtain ⟨o, c, hq⟩ := writes_requests data e he
      rw [hq]
      simp [Names]
    have syncN :
      ∀ {w r}, Retry (.fsync fd) 64 w r → ∀ e ∈ w, ¬Names (targetText dir name) e.request :=
      fun sync e he => by
      rw [retry_requests sync e he]
      simp [Names]
    have cleanN :
      ∀ {e₀ w e'}, Abandoned temp fd e₀ w e' → ∀ e ∈ w, ¬Names (targetText dir name) e.request :=
      fun clean e he => by
      rcases abandoned_requests clean e he with h | h <;> rw [h]
      · simp [Names]
      · exact (unlink_inert named).1
    have unlinkN :
      ∀ {e₀ w e'}, Unlinked temp e₀ w e' → ∀ e ∈ w, ¬Names (targetText dir name) e.request :=
      fun clean e he => by
      rw [unlinked_requests clean e he]
      exact (unlink_inert named).1
    cases body with
    | writeFailed data clean =>
      refine .inl fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact walkN e he
      rcases List.mem_append.mp he with he | he
      · exact writesN data e he
      · exact cleanN clean e he
    | syncFailed data sync clean =>
      refine .inl fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact walkN e he
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · exact writesN data e he
        · exact syncN sync e he
      · exact cleanN clean e he
    | closeFailed data sync clean =>
      refine .inl fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact walkN e he
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · exact writesN data e he
        · exact syncN sync e he
      rcases List.mem_cons.mp he with rfl | he
      · simp [Names]
      · exact unlinkN clean e he
    | @closed written synced crest n m result data sync
      commit =>
      have dataOnly : writerOnly fd (written ++ synced ++ [⟨.close fd, .ok n⟩]) := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · rcases List.mem_append.mp he with he | he
          · exact writes_owned data e he
          · rw [retry_requests sync e he]
        · rw [List.mem_singleton.mp he]
      have dataN :
        ∀ e ∈ written ++ synced ++ [⟨.close fd, .ok n⟩],
          ¬Names (targetText dir name) e.request := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · rcases List.mem_append.mp he with he | he
          · exact writesN data e he
          · exact syncN sync e he
        · rw [List.mem_singleton.mp he]
          simp [Names]
      have createN : ¬Names (targetText dir name) (.create temp mode) := by
        simp only [Names, named]
        exact tempText_ne dir name pid k
      have preN : ∀ e ∈ pre, ¬Names (targetText dir name) e.request := fun e he =>
        walkN e
          (by
            rw [hcr]; exact List.mem_append_left _ he)
      have front :
        ∀ (rest' : Trace),
          (∀ e ∈ rest', ¬Names (targetText dir name) e.request) →
            ∀
              e ∈
                pre ++ ⟨.create temp mode, .ok fd⟩ :: (written ++ synced ++ [⟨.close fd, .ok n⟩]) ++
                  rest',
              ¬Names (targetText dir name) e.request := by
        intro rest' hr e he
        rcases List.mem_append.mp he with he | he
        · rcases List.mem_append.mp he with he | he
          · exact preN e he
          · rcases List.mem_cons.mp he with rfl | he
            · exact createN
            · exact dataN e he
        · exact hr e he
      refine .inr ?_
      cases commit with
      | renameFailed namedT attempt clean =>
        exact
          ⟨pre, _, _, _, temp, _, mode, fd, _, by
            rw [hcr]; simp, namedT, attempt, dataOnly, fun e he g o c => by
            rw [unlinked_requests clean e he]; simp, front _ (unlinkN clean)⟩
      | unsynced namedT attempt flush =>
        exact
          ⟨pre, _, _, _, temp, _, mode, fd, _, by
            rw [hcr]; simp, namedT, attempt, dataOnly, fun e he => (dir_inert name flush e he).2,
            front _ fun e he => (dir_inert name flush e he).1⟩
      | replaced namedT attempt flush =>
        exact
          ⟨pre, _, _, _, temp, _, mode, fd, _, by
            rw [hcr]; simp, namedT, attempt, dataOnly, fun e he => (dir_inert name flush e he).2,
            front _ fun e he => (dir_inert name flush e he).1⟩

end FvdepAudit.Sys.Proof
