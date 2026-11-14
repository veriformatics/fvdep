import FvdepAudit.Sys.Proof.ReplaceExact

/-! `ReadExact`: every scripted run of `readFile` follows the protocol relation, which fixes the
result from the calls. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

theorem retry_read_bound {fd count budget events n}
    (h : Retry (.read fd count) budget events (.ok n)) (hc : Consistent events) : n ≤ count :=
  hc _ (retry_success_event h)

theorem reads_sound (fd : Nat) :
    ∀ (cap total : Nat) (script : Script),
      Consistent ((reads scripted fd total cap).run script).events →
        Reads fd total cap ((reads scripted fd total cap).run script).events
          ((reads scripted fd total cap).run script).result := by
  intro cap
  induction cap using Nat.strongRecOn with
  | ind cap ih =>
    intro total script hc
    have hs := retry_sound (.read fd (min (cap + 1) readChunk)) retryBudget script
    rw [reads] at hc ⊢
    simp only [run_bind] at hc ⊢
    generalize (retry scripted (.read fd (min (cap + 1) readChunk)) retryBudget).run script =
      first at *
    cases h : first.result with
    | error cause =>
      simp only [run_pure, List.append_nil]
      exact Reads.failed (by simpa [h, retryBudget, readChunk] using hs)
    | ok n =>
      cases n with
      | zero =>
        simp only [run_pure, List.append_nil]
        exact Reads.done (by simpa [h, retryBudget, readChunk] using hs)
      | succ
        n =>
        have hb := retry_read_bound (by simpa [h] using hs) ((consistent_append _ _).mp hc).1
        by_cases hcap : n + 1 ≤ cap
        · simp only [h, hb, hcap, ite_true, dite_true] at hc ⊢
          exact
            Reads.progress (by simpa [h, retryBudget, readChunk] using hs) (by omega) hcap
              (ih (cap - (n + 1)) (by omega) _ _ ((consistent_append _ _).mp hc).2)
        · simp only [hb, hcap, ite_true, dite_false, run_pure, List.append_nil]
          exact Reads.tooLarge (by simpa [h, retryBudget, readChunk] using hs) (by omega)

theorem read_outcome_eq (path : Path) (r : Except Cause Nat) (c : Response) :
    readOutcome path r c = readResult path r c := by cases r <;> cases c <;> rfl

theorem readFile_sound (path : Path) (cap : Nat) (script : Script)
    (hc : Consistent (scriptReadFile path cap script).events) :
    ReadFile path cap (scriptReadFile path cap script).events
      (scriptReadFile path cap script).result := by
  have hs := retry_sound (.openRead path) retryBudget script
  simp only [scriptReadFile, readFile, run_bind] at hc ⊢
  generalize (retry scripted (.openRead path) retryBudget).run script = opened at *
  cases h : opened.result with
  | error cause =>
    by_cases he : cause = .errno enoent
    · subst he
      simp only [ite_true, run_pure, List.append_nil]
      exact ReadFile.absent (by simpa [h, retryBudget, enoent] using hs)
    · simp only [he, ite_false, run_pure, List.append_nil]
      exact ReadFile.openFailed (by simpa [h, retryBudget] using hs) (by simpa [enoent] using he)
  | ok fd =>
    simp only [h, run_bind, run_call, run_pure, List.append_nil] at hc ⊢
    have hr :=
      reads_sound fd cap 0 (fun i => script (i + opened.consumed))
        ((consistent_append _ _).mp ((consistent_append _ _).mp hc).2).1
    rw [read_outcome_eq]
    simpa only [List.append_assoc, List.singleton_append] using
      ReadFile.opened (by simpa [h, retryBudget] using hs) hr

theorem reads_prefix_unique {fd total cap w₁ r₁} (h₁ : Reads fd total cap w₁ r₁) {w₂ r₂}
    (h₂ : Reads fd total cap w₂ r₂) (t₁ t₂ : Trace) (same : w₁ ++ t₁ = w₂ ++ t₂) :
    w₁ = w₂ ∧ r₁ = r₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing w₂ r₂ t₁ t₂ with
  | done attempt =>
    cases h₂ with
    | done attempt₂ =>
      obtain ⟨hf, _, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      exact ⟨hf, rfl, ht⟩
    | progress attempt₂ positive =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | tooLarge attempt₂
      over =>
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | failed attempt₂ => cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
  | progress attempt positive within tail ih =>
    cases h₂ with
    | done attempt₂ =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | progress attempt₂ _ _
      tail₂ =>
      rw [List.append_assoc, List.append_assoc] at same
      obtain ⟨hf, hr, rest⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      obtain ⟨hw, hres, ht⟩ := ih tail₂ _ _ rest
      exact ⟨by rw [hf, hw], hres, ht⟩
    | tooLarge attempt₂ over =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | failed attempt₂ =>
      rw [List.append_assoc] at same
      cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
  | tooLarge attempt over =>
    cases h₂ with
    | done attempt₂ =>
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | progress attempt₂ _ within₂ =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | tooLarge
      attempt₂ =>
      obtain ⟨hf, _, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      exact ⟨hf, rfl, ht⟩
    | failed attempt₂ => cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
  | failed attempt =>
    cases h₂ with
    | done attempt₂ => cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
    | progress attempt₂ =>
      rw [List.append_assoc] at same
      cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
    | tooLarge attempt₂ => cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
    | failed attempt₂ =>
      obtain ⟨hf, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      exact ⟨hf, rfl, ht⟩

theorem readFile_unique_eq {path cap e₁ r₁} (h₁ : ReadFile path cap e₁ r₁) {e₂ r₂}
    (h₂ : ReadFile path cap e₂ r₂) (same : e₁ = e₂) : r₁ = r₂ := by
  cases h₁ with
  | absent attempt =>
    cases h₂ with
    | absent => rfl
    | openFailed attempt₂
      present =>
      cases (retry_prefix_unique attempt attempt₂ [] [] (by simpa using same)).2.1
      exact absurd rfl present
    | opened attempt₂ =>
      simp only [List.append_assoc] at same
      cases (retry_prefix_unique attempt attempt₂ [] _ (by simpa using same)).2.1
  | openFailed attempt present =>
    cases h₂ with
    | absent
      attempt₂ =>
      cases (retry_prefix_unique attempt attempt₂ [] [] (by simpa using same)).2.1
      exact absurd rfl present
    | openFailed
      attempt₂ =>
      cases (retry_prefix_unique attempt attempt₂ [] [] (by simpa using same)).2.1
      rfl
    | opened attempt₂ =>
      simp only [List.append_assoc] at same
      cases (retry_prefix_unique attempt attempt₂ [] _ (by simpa using same)).2.1
  | opened attempt body =>
    simp only [List.append_assoc] at same
    cases h₂ with
    | absent attempt₂ => cases (retry_prefix_unique attempt attempt₂ _ [] (by simpa using same)).2.1
    | openFailed attempt₂ =>
      cases (retry_prefix_unique attempt attempt₂ _ [] (by simpa using same)).2.1
    | opened attempt₂ body₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      obtain ⟨_, hres, hc⟩ := reads_prefix_unique body body₂ _ _ ht
      cases hc
      rw [hres]

/-- F2 `readFile` (beyond F4's list). -/
theorem read_exact_script (path : Path) (cap : Nat) (script : Script)
    (r : Except SysError (Option Nat)) (hc : Consistent (scriptReadFile path cap script).events) :
    (scriptReadFile path cap script).result = r ↔
      ReadFile path cap (scriptReadFile path cap script).events r := by
  constructor
  · intro h
    rw [← h]
    exact readFile_sound path cap script hc
  · exact (readFile_unique_eq (readFile_sound path cap script hc) · rfl)

end FvdepAudit.Sys.Proof
