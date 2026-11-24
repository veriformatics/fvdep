import FvdepAudit.Profile.Barrier.Spec
import FvdepAudit.Profile.Stage.Proof

/-! U6 P5c + P5b + B3 + C1: the supervisor's verdict = the spec's (`judge_exact`, `judge_record`),
the batch's conclusion = the spec's over the header stage's findings (`conclude_first`). -/

namespace FvdepAudit.Profile.Barrier.Proof

open FvdepCore.Profile FvdepAudit.Profile.Barrier.Spec
open FvdepCore.Evidence (Infra)
open FvdepAudit.Profile.Stage.Spec FvdepAudit.Profile.Stage.Proof

theorem disposition_spec (seconds frameBytes : Nat) (run : Run) :
    disposition seconds frameBytes run =
      match (failures seconds frameBytes run).head?, recordBytes run with
      | some e, _ => .error e
      | none, some b => .ok b
      | none, none => .error (.io, "profile, the parse step wrote no result record") := by
  cases run with
  | setup d => rfl
  | timedOut => rfl
  | overflow => rfl
  | invalid => rfl
  | framed n o =>
    rcases o with ⟨⟨child, wf, tf⟩, files⟩
    cases child with
    | signaled k =>
      by_cases hx : 128 + k = n
      · subst hx
        simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit]
      · simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit, hx]
    | notStarted r =>
      by_cases hx : 127 = n
      · subst hx
        simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit]
      · simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit, hx]
    | exited c =>
      by_cases hx : c = n
      · subst hx
        by_cases hs : (wf || tf) = true
        · simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit, hs]
        · by_cases h0 : c = 0
          · subst h0
            rcases hl : files.lookup "results.json" with _ | b <;>
              rcases hp : least ((files.map (·.1)).filter (· != "results.json")) with _ | p <;>
              simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit, hs, hl,
                hp]
          · simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit, hs, h0]
      · simp [disposition, failures, recordBytes, FvdepCore.Phase.Child.helperExit, hx]

/-- P5c + P5b + B3 (`judgeExact`). -/
theorem judge_exact (req : Request) (digest : String) (seconds frameBytes : Nat) (run : Run) :
    judge req digest seconds frameBytes run =
      FvdepAudit.Profile.Barrier.Spec.judgeSpec req digest seconds frameBytes run := by
  unfold judge judgeSpec
  rw [disposition_spec]
  rcases h1 : (failures seconds frameBytes run).head? with _ | e <;>
    rcases h2 : recordBytes run with _ | b <;>
    rfl

/-- P5c (`judgeRecord`). -/
theorem judge_record (seconds frameBytes : Nat) (run : Run)
    (h : FvdepAudit.Profile.Barrier.Spec.failures seconds frameBytes run = []) :
    (FvdepAudit.Profile.Barrier.Spec.recordBytes run).isSome = true := by
  cases run with
  | setup d => simp [failures] at h
  | timedOut => simp [failures] at h
  | overflow => simp [failures] at h
  | invalid => simp [failures] at h
  | framed n o =>
    simp only [recordBytes]
    rcases hl : o.files.lookup "results.json" with _ | b
    · simp [failures, hl] at h
    · rfl

theorem headStage_spec (role : Role) (lib batch : List String) :
    ∀ obs : List Observed, headStage role lib batch obs = headSpec role lib batch obs
  | [] => rfl
  | o :: os => by
    simp only [headStage, headSpec]
    rcases o with ⟨m, _ | it, st, en⟩
    · rfl
    · cases it with
      | stop e => rfl
      | tree h start =>
        simp only [headEvent, header_first]
        rcases hh : (headerRules role lib batch m h).head? with _ | f
        · simp only [Option.map_none]
          exact headStage_spec role lib batch os
        · rfl

theorem bodyStage_spec : ∀ obs : List Observed, bodyStage obs = bodySpec obs
  | [] => rfl
  | o :: os => by
    simp only [bodyStage, bodySpec, bodyStage_spec os]
    rfl

/-- C1 + P5b (`concludeFirst`). -/
theorem conclude_first (req : Request) (obs : List Observed) :
    conclude req obs = FvdepAudit.Profile.Barrier.Spec.concludeSpec req obs := by
  simp only [conclude, concludeSpec, headStage_spec, bodyStage_spec]
  rfl

end FvdepAudit.Profile.Barrier.Proof
