import FvdepAudit.Index.Command.Proof.Basic

/-! `fvdep index [--check]` against the run written apart (`IndexRun`): the completed runs = exactly
the runs written apart; an interrupted run = a prefix of one; every run's file effects + output
lines. Headers = the ledger statements. -/

namespace FvdepAudit.Index.Command.Proof

open FvdepCore FvdepCore.Doc FvdepCore.Index FvdepCore.Index.Command FvdepCore.Index.Assemble
open FvdepAudit.Index.Command.Spec

/-- U4 C1 + C9 + C8 `IndexExact`: a completed run of `fvdep index [--check]` = exactly a run
written apart (`IndexRun`). -/
theorem index_exact (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response))
    (code : UInt32) :
    Plan.Runs (Index.Command.plan h check) evs (some code) ↔ IndexRun h check evs code := by
  unfold Index.Command.plan IndexRun
  rw [runs_fit fits_probe]
  refine exists_congr fun rp => exists_congr fun rest => and_congr_right fun _ => ?_
  cases rp with
  | error r => exact runs_stop _ (List.cons_ne_nil _ _) rest code
  | ok x =>
    cases x with
    | none => exact runs_stop _ (List.cons_ne_nil _ _) rest code
    | some b =>
      dsimp only
      refine Iff.trans ?_ (text_trim b _).symm
      unfold onProbe
      by_cases ht : trimText (textOfBytes b) = toolchain
      · have hp : probeStage (.probe (.ok (some b))) = .ok (textOfBytes b) := ite_eq_left ht
        rw [hp, ite_eq_left (show trimText (textOfBytes b) = Toolchain from ht)]
        exact runs_onFacts h check _ rest code
      · have hp :
          probeStage (.probe (.ok (some b))) = .error (mismatch (trimText (textOfBytes b))) :=
          ite_eq_right ht
        rw [hp, ite_eq_right (show ¬trimText (textOfBytes b) = Toolchain from ht)]
        exact runs_stop _ (List.cons_ne_nil _ _) rest code

/-- U2 X5 for `fvdep index`: an interrupted run performed a prefix of a completed run written
apart. -/
theorem index_prefix (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response)) :
    Plan.Runs (Index.Command.plan h check) evs none →
      ∃ rest code, IndexRun h check (evs ++ rest) code := by
  intro hr
  obtain ⟨rest, code, hc⟩ := runs_extends hr
  exact ⟨rest, code, (index_exact h check _ code).mp hc⟩

/-- U4 C1: every run, completed or interrupted, reads `index.json` alone + only with `--check`, and
replaces `index.json` alone + only without it. -/
theorem index_files (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response))
    (r : Option UInt32) :
    Plan.Runs (Index.Command.plan h check) evs r →
      ∀ x ∈ evs,
        (∀ f, x.1 = .read f → f = .index ∧ check = true) ∧
          ∀ f b, x.1 = .replace f b → f = .index ∧ check = false := by
  intro hr x hx
  have hs := every_runs hr (every_plan h check) x hx
  exact ⟨hs.1, hs.2.1⟩

/-- Interface §1's line rule for `fvdep index`: every output write of every run = one or more
lines, each ending in LF, with no Unicode `Cc` character inside a line. -/
theorem index_lines (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response))
    (r : Option UInt32) :
    Plan.Runs (Index.Command.plan h check) evs r →
      ∀ x ∈ evs,
        ∀ s,
          (x.1 = .out s ∨ x.1 = .err s) →
            ∃ ls : List String,
              ls ≠ [] ∧
                s = String.join (ls.map (· ++ "\n")) ∧
                ∀ l ∈ ls, ∀ c ∈ l.toList, ¬(c.toNat < 32 ∨ 127 ≤ c.toNat ∧ c.toNat ≤ 159) := by
  intro hr x hx s hs
  obtain ⟨ms, hm, rfl⟩ := (every_runs hr (every_plan h check) x hx).2.2 s hs
  refine ⟨ms.map escapeControls, by simpa using hm, ?_, ?_⟩
  · rw [List.map_map]
    rfl
  · intro l hl c hc
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hl
    exact isControl_false.mp (escapeControls_clean m c hc)

end FvdepAudit.Index.Command.Proof
