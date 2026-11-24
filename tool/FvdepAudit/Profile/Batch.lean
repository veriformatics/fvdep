import FvdepCore.Profile.Barrier

/-! U6 C1 + P5 + P5c + B3 (contract `docs/contracts/U6-profile.md`): the batch's conclusion accepts
only a fully observed batch, ended clean; the supervisor's verdict accepts exactly through P5c's
record bytes + P5b's intake of an accepted record. -/

namespace FvdepAudit.Profile.Batch

open FvdepCore.Profile

theorem headStage_clean (role : Role) (lib batch : List String) :
    ∀ (obs : List Observed),
      headStage role lib batch obs = .clean →
        ∀ o ∈ obs, ∃ i, o.head = some i ∧ headEvent role lib batch o.module i = none
  | [], _ => by simp
  | o :: os, h => by
    unfold headStage at h
    split at h
    · cases h
    · rename_i i hi
      split at h
      · cases h
      · rename_i he
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨i, hi, he⟩
        · exact headStage_clean role lib batch os h x hx

theorem bodyStage_clean :
    ∀ (obs : List Observed),
      bodyStage obs = .clean → ∀ o ∈ obs, o.state.event = none ∧ o.ended = true
  | [], _ => by simp
  | o :: os, h => by
    unfold bodyStage at h
    split at h
    · cases h
    · rename_i he
      split at h
      · rename_i hend
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨he, hend⟩
        · exact bodyStage_clean os h x hx
      · cases h

theorem outcomeOf_ne (m : String) (e : Event) : outcomeOf m e ≠ .accepted := by
  cases e <;> simp [outcomeOf]

/-- C1 + P5 `ConcludeAccepts`: `accepted` names the request's modules in order, each header observed
with no event, each body ended at its input's end with no event. -/
theorem conclude_accepts (req : Request) (obs : List Observed) (gs : List (List String))
    (h : conclude req obs = some (.accepted, gs)) :
    obs.map (·.module) = req.modules.map (·.module) ∧
      ∀ o ∈ obs,
        (∃ i,
            o.head = some i ∧
              headEvent req.role (req.library.map (·.module)) (req.modules.map (·.module)) o.module
                  i =
                none) ∧
          o.state.event = none ∧ o.ended = true := by
  unfold conclude at h
  split at h
  · rename_i hm
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact absurd h.1 (outcomeOf_ne _ _)
    · rename_i hh
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact absurd h.1 (outcomeOf_ne _ _)
      · rename_i hb
        exact ⟨hm, fun o ho => ⟨headStage_clean _ _ _ obs hh o ho, bodyStage_clean obs hb o ho⟩⟩
  · cases h

/-- P5c + P5b + B3 `JudgeAccepts`: the verdict is `accepted r` exactly when P5c's disposition yields
record bytes whose intake under this profile binds `r` to the request + `r`'s outcome is
accepted. -/
theorem judge_accepts (req : Request) (digest : String) (seconds frameBytes : Nat) (run : Run)
    (r : Record) :
    judge req digest seconds frameBytes run = .accepted r ↔
      ∃ b,
        disposition seconds frameBytes run = .ok b ∧
          intake profileId req digest b = .ok r ∧ r.outcome = .accepted := by
  unfold judge verdictOf
  constructor
  · intro h
    cases hd : disposition seconds frameBytes run with
    | error e => simp [hd] at h
    | ok b =>
      simp only [hd] at h
      cases hi : intake profileId req digest b with
      | error e => simp [hi] at h
      | ok r' =>
        simp only [hi] at h
        cases ho : r'.outcome with
        | accepted =>
          simp only [ho, Verdict.accepted.injEq] at h
          subst h
          exact ⟨b, rfl, hi, ho⟩
        | refused f => simp [ho] at h
        | over => simp [ho] at h
  · rintro ⟨b, hd, hi, ho⟩
    simp [hd, hi, ho]

end FvdepAudit.Profile.Batch
