import FvdepAudit.Sys.Proof.ReplaceExact

/-! F4 `LockExact`: every scripted run of `withLock` follows the lock relation, which fixes the
result from the calls. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

theorem retry_consumed (request : Request) (budget : Nat) (script : Script) :
    ((retry scripted request budget).run script).consumed =
      ((retry scripted request budget).run script).events.length := by
  induction budget generalizing script with
  | zero =>
    cases h : script 0 with
    | ok n => simp [retry, h]
    | error n => simp [retry, h]
  | succ budget ih =>
    cases h : script 0 with
    | ok n => simp [retry, h]
    | error n =>
      by_cases hn : n = eintr
      · simp [retry, h, hn, ih]
        omega
      · simp [retry, h, hn]

theorem lockPath_text (dir : Path) : (lockPath dir).toString = lockText dir := by
  apply String.ext
  simp [lockPath, Path.child, lockText, lockName]

theorem lock_refusal_eq (path : Path) (cause : Cause) (closed : Response) :
    lockRefusal path cause closed = refusal path cause closed := by cases closed <;> rfl

theorem lock_sound {α : Type} (dir : Path) (act : ScriptIO α) (script : Script) :
    Lock dir act script (scriptLock dir act script).events (scriptLock dir act script).result := by
  have hs := retry_sound (.openLock (lockPath dir)) retryBudget script
  have hn := retry_consumed (.openLock (lockPath dir)) retryBudget script
  simp only [scriptLock, withLock, run_bind]
  generalize (retry scripted (.openLock (lockPath dir)) retryBudget).run script = opened at *
  cases h : opened.result with
  | error cause =>
    simp only [run_pure, List.append_nil]
    exact Lock.openFailed (lockPath_text dir) (by simpa [h, retryBudget] using hs)
  | ok fd =>
    simp only [run_bind]
    have hs' := retry_sound (.lock fd) retryBudget fun i => script (i + opened.consumed)
    have hn' := retry_consumed (.lock fd) retryBudget fun i => script (i + opened.consumed)
    generalize (retry scripted (.lock fd) retryBudget).run (fun i => script (i + opened.consumed)) =
      locked at *
    cases hl : locked.result with
    | error cause =>
      simp only [run_bind, run_call, run_pure, List.append_nil]
      rw [lock_refusal_eq]
      simpa only [List.append_assoc, List.singleton_append] using
        Lock.refused (act := act) (script := script) (lockPath_text dir)
          (by simpa [h, retryBudget] using hs) (by simpa [hl, retryBudget] using hs')
    | ok n =>
      simp only [run_bind, run_call, run_pure, List.append_nil]
      have hshift :
        (fun i => script (i + locked.consumed + opened.consumed)) = fun i =>
          script (i + (opened.events.length + locked.events.length)) := by
        funext i
        rw [hn, hn']
        congr 1
        omega
      rw [hshift]
      simpa only [List.append_assoc, List.singleton_append] using
        Lock.ran (act := act) (script := script) (lockPath_text dir)
          (by simpa [h, retryBudget] using hs) (by simpa [hl, retryBudget] using hs')

theorem lock_unique_eq {α : Type} {dir : Path} {act : ScriptIO α} {script : Script} {e₁ r₁}
    (h₁ : Lock dir act script e₁ r₁) {e₂ r₂} (h₂ : Lock dir act script e₂ r₂) (same : e₁ = e₂) :
    r₁ = r₂ := by
  cases h₁ with
  | openFailed named attempt =>
    cases h₂ with
    | openFailed named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases (retry_prefix_unique attempt attempt₂ [] [] (by simpa using same)).2.1
      rfl
    | refused named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      simp only [List.append_assoc] at same
      cases (retry_prefix_unique attempt attempt₂ [] _ (by simpa using same)).2.1
    | ran named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      simp only [List.append_assoc] at same
      cases (retry_prefix_unique attempt attempt₂ [] _ (by simpa using same)).2.1
  | refused named attempt lockAttempt =>
    simp only [List.append_assoc] at same
    cases h₂ with
    | openFailed named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases (retry_prefix_unique attempt attempt₂ _ [] (by simpa using same)).2.1
    | refused named₂ attempt₂
      lockAttempt₂ =>
      cases path_eq (named.trans named₂.symm)
      simp only [List.append_assoc] at same
      obtain ⟨_, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      obtain ⟨_, hl, hc⟩ := retry_prefix_unique lockAttempt lockAttempt₂ _ _ ht
      cases hl
      cases hc
      rfl
    | ran named₂ attempt₂ lockAttempt₂ =>
      cases path_eq (named.trans named₂.symm)
      simp only [List.append_assoc] at same
      obtain ⟨_, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      cases (retry_prefix_unique lockAttempt lockAttempt₂ _ _ ht).2.1
  | ran named attempt lockAttempt =>
    simp only [List.append_assoc] at same
    cases h₂ with
    | openFailed named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases (retry_prefix_unique attempt attempt₂ _ [] (by simpa using same)).2.1
    | refused named₂ attempt₂
      lockAttempt₂ =>
      cases path_eq (named.trans named₂.symm)
      simp only [List.append_assoc] at same
      obtain ⟨_, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      cases (retry_prefix_unique lockAttempt lockAttempt₂ _ _ ht).2.1
    | ran named₂ attempt₂ lockAttempt₂ =>
      cases path_eq (named.trans named₂.symm)
      simp only [List.append_assoc] at same
      obtain ⟨ho, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      obtain ⟨hl, _, _⟩ := retry_prefix_unique lockAttempt lockAttempt₂ _ _ ht
      subst ho
      subst hl
      rfl

/-- F4 `LockExact`. -/
theorem lock_exact_script {α : Type} (dir : Path) (act : ScriptIO α) (script : Script)
    (r : Except SysError α) :
    (scriptLock dir act script).result = r ↔
      Lock dir act script (scriptLock dir act script).events r := by
  constructor
  · intro h
    rw [← h]
    exact lock_sound dir act script
  · exact (lock_unique_eq (lock_sound dir act script) · rfl)

end FvdepAudit.Sys.Proof
