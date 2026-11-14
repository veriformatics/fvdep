import FvdepAudit.Sys.Proof.Replace

/-! F4 `ReplaceExact`, uniqueness: the protocol relation fixes the result from the calls. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

theorem path_eq {p q : Path} (h : p.toString = q.toString) : p = q := by
  cases p
  cases q
  simp only at h
  subst h
  rfl

theorem mode_eq {a b : Mode} (h : a.toNat = b.toNat) : a = b := by
  cases a
  cases b
  simp only at h
  subst h
  rfl

theorem writes_prefix_unique {fd offset remaining w₁ r₁} (h₁ : Writes fd offset remaining w₁ r₁)
    {w₂ r₂} (h₂ : Writes fd offset remaining w₂ r₂) (t₁ t₂ : Trace) (same : w₁ ++ t₁ = w₂ ++ t₂) :
    w₁ = w₂ ∧ r₁ = r₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing w₂ r₂ t₁ t₂ with
  | empty =>
    cases h₂ with
    | empty => exact ⟨rfl, rfl, by simpa using same⟩
    | progress nonempty => omega
    | stalled nonempty => omega
    | failed nonempty => omega
  | progress nonempty attempt positive bounded tail ih =>
    cases h₂ with
    | empty => omega
    | progress _ attempt₂ _ _
      tail₂ =>
      rw [List.append_assoc, List.append_assoc] at same
      obtain ⟨hf, hr, rest⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      obtain ⟨hw, hres, ht⟩ := ih tail₂ _ _ rest
      exact ⟨by rw [hf, hw], hres, ht⟩
    | stalled _ attempt₂ =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | failed _ attempt₂ =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
  | stalled nonempty attempt =>
    cases h₂ with
    | empty => omega
    | progress _ attempt₂ positive₂ _
      _ =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      omega
    | stalled _
      attempt₂ =>
      obtain ⟨hf, _, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      exact ⟨hf, rfl, ht⟩
    | failed _ attempt₂ =>
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
  | failed nonempty attempt =>
    cases h₂ with
    | empty => omega
    | progress _ attempt₂ _ _ _ =>
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
    | stalled _ attempt₂ =>
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
    | failed _
      attempt₂ =>
      obtain ⟨hf, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      exact ⟨hf, rfl, ht⟩

theorem tempWalk_prefix_unique {dir name pid n w₁ r₁} (h₁ : TempWalk dir name pid n w₁ r₁) {w₂ r₂}
    (h₂ : TempWalk dir name pid n w₂ r₂) (t₁ t₂ : Trace) (same : w₁ ++ t₁ = w₂ ++ t₂) :
    w₁ = w₂ ∧ r₁ = r₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing w₂ r₂ t₁ t₂ with
  | created bound named perm attempt =>
    cases h₂ with
    | created _ named₂ perm₂
      attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      obtain ⟨hf, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      exact ⟨hf, rfl, ht⟩
    | taken _ named₂ perm₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
    | failed _ named₂ perm₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
    | allTaken => omega
  | taken bound named perm attempt next ih =>
    cases h₂ with
    | created _ named₂ perm₂
      attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
    | taken _ named₂ perm₂ attempt₂
      next₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      rw [List.append_assoc, List.append_assoc] at same
      obtain ⟨hf, _, rest⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      obtain ⟨hw, hr, ht⟩ := ih next₂ _ _ rest
      exact ⟨by rw [hf, hw], hr, ht⟩
    | failed _ named₂ perm₂ attempt₂
      other =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      exact absurd rfl other
    | allTaken => omega
  | failed bound named perm attempt other =>
    cases h₂ with
    | created _ named₂ perm₂
      attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
    | taken _ named₂ perm₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      rw [List.append_assoc] at same
      have hr := (retry_prefix_unique attempt attempt₂ _ _ same).2.1
      cases hr
      exact absurd rfl other
    | failed _ named₂ perm₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases mode_eq (perm.trans perm₂.symm)
      obtain ⟨hf, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      exact ⟨hf, rfl, ht⟩
    | allTaken => omega
  | allTaken named =>
    cases h₂ with
    | created bound => omega
    | taken bound => omega
    | failed bound => omega
    | allTaken named₂ =>
      cases path_eq (named.trans named₂.symm)
      exact ⟨rfl, rfl, by simpa using same⟩

theorem unlinked_unique {temp e events e₁ e₂} (h₁ : Unlinked temp e events e₁)
    (h₂ : Unlinked temp e events e₂) : e₁ = e₂ := by
  cases h₁ with
  | removed a =>
    cases h₂ with
    | removed => rfl
    | failed b => cases retry_unique a b
    | interrupted b => cases retry_unique a b
  | failed a =>
    cases h₂ with
    | removed b => cases retry_unique a b
    | failed b =>
      cases retry_unique a b; rfl
    | interrupted b => cases retry_unique a b
  | interrupted a =>
    cases h₂ with
    | removed b => cases retry_unique a b
    | failed b => cases retry_unique a b
    | interrupted => rfl

theorem abandoned_unique {temp fd e events e₁ e₂} (h₁ : Abandoned temp fd e events e₁)
    (h₂ : Abandoned temp fd e events e₂) : e₁ = e₂ := by
  cases h₁ with
  | closed a =>
    cases h₂ with
    | closed b => exact unlinked_unique a b
  | closeFailed a =>
    cases h₂ with
    | closeFailed b => exact unlinked_unique a b

theorem commit_unique_eq {dir name temp e₁ r₁} (h₁ : Commit dir name temp e₁ r₁) {e₂ r₂}
    (h₂ : Commit dir name temp e₂ r₂) (same : e₁ = e₂) : r₁ = r₂ := by
  cases h₁ with
  | renameFailed named attempt clean =>
    cases h₂ with
    | renameFailed named₂ attempt₂
      clean₂ =>
      cases path_eq (named.trans named₂.symm)
      obtain ⟨_, hr, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases hr
      subst ht
      rw [unlinked_unique clean clean₂]
    | unsynced named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
    | replaced named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
  | unsynced named attempt flush =>
    cases h₂ with
    | renameFailed named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
    | unsynced named₂ attempt₂
      flush₂ =>
      cases path_eq (named.trans named₂.symm)
      obtain ⟨_, _, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases directory_unique_eq flush flush₂ ht
      rfl
    | replaced named₂ attempt₂
      flush₂ =>
      cases path_eq (named.trans named₂.symm)
      obtain ⟨_, _, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases directory_unique_eq flush flush₂ ht
  | replaced named attempt flush =>
    cases h₂ with
    | renameFailed named₂ attempt₂ =>
      cases path_eq (named.trans named₂.symm)
      cases (retry_prefix_unique attempt attempt₂ _ _ same).2.1
    | unsynced named₂ attempt₂
      flush₂ =>
      cases path_eq (named.trans named₂.symm)
      obtain ⟨_, _, ht⟩ := retry_prefix_unique attempt attempt₂ _ _ same
      cases directory_unique_eq flush flush₂ ht
    | replaced => rfl

theorem body_unique_eq {dir name size temp fd e₁ r₁} (h₁ : Body dir name size temp fd e₁ r₁) {e₂ r₂}
    (h₂ : Body dir name size temp fd e₂ r₂) (same : e₁ = e₂) : r₁ = r₂ := by
  cases h₁ with
  | writeFailed data clean =>
    cases h₂ with
    | writeFailed data₂
      clean₂ =>
      obtain ⟨_, hr, ht⟩ := writes_prefix_unique data data₂ _ _ same
      cases hr
      subst ht
      rw [abandoned_unique clean clean₂]
    | syncFailed data₂ =>
      simp only [List.append_assoc] at same
      cases (writes_prefix_unique data data₂ _ _ same).2.1
    | closeFailed data₂ =>
      simp only [List.append_assoc] at same
      cases (writes_prefix_unique data data₂ _ _ same).2.1
    | closed data₂ =>
      simp only [List.append_assoc] at same
      cases (writes_prefix_unique data data₂ _ _ same).2.1
  | syncFailed data sync clean =>
    simp only [List.append_assoc] at same
    cases h₂ with
    | writeFailed data₂ => cases (writes_prefix_unique data data₂ _ _ same).2.1
    | syncFailed data₂ sync₂ clean₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      obtain ⟨_, hr, hc⟩ := retry_prefix_unique sync sync₂ _ _ ht
      cases hr
      subst hc
      rw [abandoned_unique clean clean₂]
    | closeFailed data₂ sync₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      cases (retry_prefix_unique sync sync₂ _ _ ht).2.1
    | closed data₂ sync₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      cases (retry_prefix_unique sync sync₂ _ _ ht).2.1
  | closeFailed data sync clean =>
    simp only [List.append_assoc] at same
    cases h₂ with
    | writeFailed data₂ => cases (writes_prefix_unique data data₂ _ _ same).2.1
    | syncFailed data₂ sync₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      cases (retry_prefix_unique sync sync₂ _ _ ht).2.1
    | closeFailed data₂ sync₂ clean₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      obtain ⟨_, _, hc⟩ := retry_prefix_unique sync sync₂ _ _ ht
      cases hc
      rw [unlinked_unique clean clean₂]
    | closed data₂ sync₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      obtain ⟨_, _, hc⟩ := retry_prefix_unique sync sync₂ _ _ ht
      cases hc
  | closed data sync commit =>
    simp only [List.append_assoc] at same
    cases h₂ with
    | writeFailed data₂ => cases (writes_prefix_unique data data₂ _ _ same).2.1
    | syncFailed data₂ sync₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      cases (retry_prefix_unique sync sync₂ _ _ ht).2.1
    | closeFailed data₂ sync₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      obtain ⟨_, _, hc⟩ := retry_prefix_unique sync sync₂ _ _ ht
      cases hc
    | closed data₂ sync₂ commit₂ =>
      simp only [List.append_assoc] at same
      obtain ⟨_, _, ht⟩ := writes_prefix_unique data data₂ _ _ same
      obtain ⟨_, _, hc⟩ := retry_prefix_unique sync sync₂ _ _ ht
      cases hc
      exact commit_unique_eq commit commit₂ rfl

theorem replace_unique_eq {dir name pid size e₁ r₁} (h₁ : Replace dir name pid size e₁ r₁) {e₂ r₂}
    (h₂ : Replace dir name pid size e₂ r₂) (same : e₁ = e₂) : r₁ = r₂ := by
  cases h₁ with
  | noTemp walk =>
    cases h₂ with
    | noTemp walk₂ =>
      cases (tempWalk_prefix_unique walk walk₂ [] [] (by simpa using same)).2.1
      rfl
    | opened walk₂ => cases (tempWalk_prefix_unique walk walk₂ [] _ (by simpa using same)).2.1
  | opened walk body =>
    cases h₂ with
    | noTemp walk₂ => cases (tempWalk_prefix_unique walk walk₂ _ [] (by simpa using same)).2.1
    | opened walk₂
      body₂ =>
      obtain ⟨_, hr, ht⟩ := tempWalk_prefix_unique walk walk₂ _ _ same
      cases hr
      exact body_unique_eq body body₂ ht

/-- F4 `ReplaceExact`. -/
theorem replace_exact_script (dir : Path) (name : Name) (pid size : Nat) (script : Script)
    (r : Except SysError Unit) (hc : Consistent (scriptReplace dir name pid size script).events) :
    (scriptReplace dir name pid size script).result = r ↔
      Replace dir name pid size (scriptReplace dir name pid size script).events r := by
  constructor
  · intro h
    rw [← h]
    exact replace_sound dir name pid size script hc
  · exact (replace_unique_eq (replace_sound dir name pid size script hc) · rfl)

end FvdepAudit.Sys.Proof
