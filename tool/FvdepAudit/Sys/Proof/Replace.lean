import FvdepAudit.Sys.Proof.Exact

/-! F4 `ReplaceExact`, soundness: every scripted run of `replace` follows the protocol relation. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

theorem retry_error_cause {request budget events cause}
    (h : Retry request budget events (.error cause)) :
    (∃ n, cause = .errno n) ∨ cause = .retryExhausted := by
  generalize hr : Except.error cause = result at h
  induction h with
  | success => cases hr
  | failure _ n _ =>
    cases hr; exact .inl ⟨n, rfl⟩
  | exhausted =>
    cases hr; exact .inr rfl
  | interrupted _ ih => exact ih hr

theorem tempPath_text (dir : Path) (name : Name) (pid n : Nat) :
    (tempPath dir name pid n).toString = tempText dir name pid n := by
  apply String.ext
  simp [tempPath, Path.child, tempText]

theorem at_text (dir : Path) (name : Name) : (dir.at name).toString = targetText dir name := rfl

theorem createTemp_sound (dir : Path) (name : Name) (pid : Nat) :
    ∀ (k n : Nat) (script : Script),
      n + k = 64 →
        TempWalk dir name pid n ((createTemp scripted dir name pid n).run script).events
          ((createTemp scripted dir name pid n).run script).result := by
  intro k
  induction k with
  | zero =>
    intro n script hn
    have h64 : n = 64 := by omega
    subst h64
    rw [createTemp]
    simp only [tempTries, Nat.lt_irrefl]
    exact TempWalk.allTaken (tempPath_text dir name pid 63)
  | succ k ih =>
    intro n script hn
    have hlt : n < tempTries := by
      simp only [tempTries]; omega
    have hs := retry_sound (.create (tempPath dir name pid n) Mode.default) retryBudget script
    rw [createTemp]
    simp only [hlt, dite_true, run_bind]
    generalize
      (retry scripted (.create (tempPath dir name pid n) Mode.default) retryBudget).run script =
      first at *
    cases h : first.result with
    | ok fd =>
      simp only [run_pure, List.append_nil]
      exact
        TempWalk.created (by omega) (tempPath_text dir name pid n) rfl
          (by simpa [h, retryBudget] using hs)
    | error cause =>
      by_cases he : cause = .errno eexist
      · subst he
        simp only [ite_true]
        exact
          TempWalk.taken (by omega) (tempPath_text dir name pid n) rfl
            (by simpa [h, retryBudget, eexist] using hs) (ih (n + 1) _ (by omega))
      · simp only [he, ite_false, run_pure, List.append_nil]
        exact
          TempWalk.failed (by omega) (tempPath_text dir name pid n) rfl
            (by simpa [h, retryBudget] using hs) (by simpa [eexist] using he)

theorem dropTemp_sound (temp : Path) (e : SysError) (script : Script) :
    Unlinked temp e ((dropTemp scripted temp e).run script).events
      ((dropTemp scripted temp e).run script).result := by
  have hs := retry_sound (.unlink temp) retryBudget script
  simp only [dropTemp, run_bind]
  generalize (retry scripted (.unlink temp) retryBudget).run script = first at *
  cases h : first.result with
  | ok n =>
    simp only [run_pure, List.append_nil]
    exact Unlinked.removed (by simpa [h, retryBudget] using hs)
  | error
    cause =>
    have hr : Retry (.unlink temp) 64 first.events (.error cause) := by
      simpa [h, retryBudget] using hs
    simp only [run_pure, List.append_nil]
    rcases retry_error_cause hr with ⟨n, rfl⟩ | rfl
    · exact Unlinked.failed hr
    · exact Unlinked.interrupted hr

theorem abandon_sound (temp : Path) (fd : Nat) (e : SysError) (script : Script) :
    Abandoned temp fd e ((abandon scripted temp fd e).run script).events
      ((abandon scripted temp fd e).run script).result := by
  simp only [abandon, run_bind, run_call]
  cases h : script 0 with
  | ok n =>
    simpa [h] using
      Abandoned.closed (temp := temp) (fd := fd) (e := e) (n := n)
        (dropTemp_sound temp e fun i => script (i + 1))
  | error n =>
    simpa [h] using
      Abandoned.closeFailed (temp := temp) (fd := fd) (e := e) (n := n)
        (dropTemp_sound temp { e with secondary := e.secondary ++ [(.close, n)] } fun i =>
          script (i + 1))

theorem commit_sound (dir : Path) (name : Name) (temp : Path) (script : Script) :
    Commit dir name temp ((commit scripted dir name temp).run script).events
      ((commit scripted dir name temp).run script).result := by
  have hs := retry_sound (.rename temp (dir.at name)) retryBudget script
  simp only [commit, run_bind]
  generalize (retry scripted (.rename temp (dir.at name)) retryBudget).run script = renamed at *
  cases h : renamed.result with
  | error cause =>
    simp only [run_bind, run_pure, List.append_nil, Nat.add_zero]
    exact
      Commit.renameFailed (at_text dir name) (by simpa [h, retryBudget] using hs)
        (dropTemp_sound temp _ _)
  | ok n =>
    simp only [run_bind]
    have hd := directory_sound dir fun i => script (i + renamed.consumed)
    simp only [scriptDirectory, asExecution] at hd
    generalize (directory scripted dir).run (fun i => script (i + renamed.consumed)) = flushed at *
    cases hf : flushed.result with
    | error e =>
      simp only [run_pure, List.append_nil]
      exact
        Commit.unsynced (at_text dir name) (by simpa [h, retryBudget] using hs)
          (by simpa [hf] using hd)
    | ok m =>
      simp only [run_pure, List.append_nil]
      exact
        Commit.replaced (at_text dir name) (by simpa [h, retryBudget] using hs)
          (by simpa [hf] using hd)

theorem body_sound (dir : Path) (name : Name) (size : Nat) (temp : Path) (fd : Nat)
    (script : Script) (hc : Consistent ((body scripted dir name size temp fd).run script).events) :
    Body dir name size temp fd ((body scripted dir name size temp fd).run script).events
      ((body scripted dir name size temp fd).run script).result := by
  simp only [body, run_bind] at hc ⊢
  have hw := writes_sound fd 0 size script ((consistent_append _ _).mp hc).1
  generalize (writes scripted fd 0 size).run script = written at *
  cases h : written.result with
  | error cause =>
    simp only [run_bind, run_pure, List.append_nil, Nat.add_zero]
    exact Body.writeFailed (by simpa [h] using hw) (abandon_sound temp fd _ _)
  | ok u =>
    cases u
    simp only [h, run_bind] at hc ⊢
    have hs := retry_sound (.fsync fd) retryBudget fun i => script (i + written.consumed)
    generalize
      (retry scripted (.fsync fd) retryBudget).run (fun i => script (i + written.consumed)) =
      synced at *
    cases hy : synced.result with
    | error cause =>
      simp only [run_bind, run_pure, List.append_nil, Nat.add_zero]
      simpa only [List.append_assoc, Policy.error] using
        Body.syncFailed (dir := dir) (name := name) (by simpa [h] using hw)
          (by simpa [hy, retryBudget] using hs) (abandon_sound temp fd _ _)
    | ok m =>
      simp only [run_bind, run_call]
      cases hz : script (0 + synced.consumed + written.consumed) with
      | error n =>
        simp only [run_bind, run_pure, List.append_nil, Nat.add_zero]
        simpa only [List.append_assoc, List.cons_append, List.nil_append, Policy.error] using
          Body.closeFailed (dir := dir) (name := name) (by simpa [h] using hw)
            (by simpa [hy, retryBudget] using hs) (dropTemp_sound temp _ _)
      | ok n =>
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          Body.closed (by simpa [h] using hw) (by simpa [hy, retryBudget] using hs)
            (commit_sound dir name temp _)

theorem replace_sound (dir : Path) (name : Name) (pid size : Nat) (script : Script)
    (hc : Consistent (scriptReplace dir name pid size script).events) :
    Replace dir name pid size (scriptReplace dir name pid size script).events
      (scriptReplace dir name pid size script).result := by
  simp only [scriptReplace, replace, run_bind] at hc ⊢
  have hw := createTemp_sound dir name pid 64 0 script (by omega)
  generalize (createTemp scripted dir name pid 0).run script = created at *
  cases h : created.result with
  | error e =>
    simp only [run_pure, List.append_nil]
    exact Replace.noTemp (by simpa [h] using hw)
  | ok p =>
    obtain ⟨temp, fd⟩ := p
    simp only [h] at hc ⊢
    exact
      Replace.opened (by simpa [h] using hw)
        (body_sound dir name size temp fd _ ((consistent_append _ _).mp hc).2)

end FvdepAudit.Sys.Proof
