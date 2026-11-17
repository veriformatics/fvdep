import FvdepAudit.Phase.Spec

/-! Proofs of the phase claims (contract `docs/contracts/U5-sandbox.md` P5, P8; statements =
`FvdepLedger.Rows.PhaseClaims`). -/

namespace FvdepAudit.Phase.Proof

open FvdepCore.Phase FvdepCore.Sandbox FvdepAudit.Phase.Spec

/-- P5: a step passes exactly when bwrap reports exit 0, the frame is complete + records the child
exiting 0, + no size cap was hit. -/
theorem verdict_pass (s : Step) (r : StepResult) :
    stepVerdict s r = .pass ↔
      r.outcome = Outcome.exited 0 ∧
        r.frame = Frame.ok (Child.exited 0) true ∧ r.exhausted = false := by
  rcases r with ⟨o, f, ex, d⟩
  cases o with
  | exited n =>
    cases f with
    | ok child complete =>
      cases child with
      | exited c =>
        simp only [stepVerdict, Child.helperExit, bne_iff_ne, ne_eq]
        by_cases hc : c = n
        · subst hc
          cases ex
          · cases c with
            | zero => cases complete <;> simp_all
            | succ c => by_cases hs : s = .libraryRoots <;> simp_all
          · simp
        · simp only [hc, not_false_eq_true, ↓reduceIte]
          simp only [reduceCtorEq, false_iff, not_and, Outcome.exited.injEq, Frame.ok.injEq,
            Child.exited.injEq]
          intro hn hc0
          omega
      | signaled k =>
        simp only [stepVerdict, Child.helperExit, bne_iff_ne, ne_eq]
        split <;> (try split) <;> simp_all
      | notStarted w =>
        simp only [stepVerdict, Child.helperExit, bne_iff_ne, ne_eq]
        split <;> (try split) <;> simp_all
    | missing => simp [stepVerdict]
    | invalid => simp [stepVerdict]
    | overflow => simp [stepVerdict]
  | timedOut => simp [stepVerdict]
  | setupFailed d => simp [stepVerdict]
  | protocol => simp [stepVerdict]

/-- `verdict_failed`'s forward direction. -/
theorem failed_shape (s : Step) (r : StepResult) (reason : String)
    (h : stepVerdict s r = .failed reason) :
    ∃ c complete,
      r.outcome = Outcome.exited c ∧
        r.frame = Frame.ok (Child.exited c) complete ∧
        r.exhausted = false ∧ ((c ≠ 0 ∧ s ≠ .libraryRoots) ∨ (c = 0 ∧ complete = false)) := by
  rcases r with ⟨o, f, ex, d⟩
  cases o with
  | exited n =>
    cases f with
    | ok child complete =>
      cases child with
      | exited c =>
        simp only [stepVerdict, Child.helperExit, bne_iff_ne, ne_eq] at h
        by_cases hc : c = n
        · subst hc
          cases ex
          · refine ⟨c, complete, rfl, rfl, rfl, ?_⟩
            cases c with
            | zero => cases complete <;> simp_all
            | succ c => by_cases hs : s = .libraryRoots <;> simp_all
          · simp at h
        · simp [hc] at h
      | signaled k =>
        simp only [stepVerdict, Child.helperExit, bne_iff_ne, ne_eq] at h
        split at h <;> (try split at h) <;> simp_all
      | notStarted w =>
        simp only [stepVerdict, Child.helperExit, bne_iff_ne, ne_eq] at h
        split at h <;> (try split at h) <;> simp_all
    | missing => simp [stepVerdict] at h
    | invalid => simp [stepVerdict] at h
    | overflow => simp [stepVerdict] at h
  | timedOut => simp [stepVerdict] at h
  | setupFailed d => simp [stepVerdict] at h
  | protocol => simp [stepVerdict] at h

/-- P5: a step fails on its input exactly when bwrap + the frame agree that its child exited with
code `c`, no size cap was hit, + `c` ≠ 0 (Lean refusing the input; never a library root) or `c` = 0
with an incomplete artifact family. -/
theorem verdict_failed (s : Step) (r : StepResult) :
    (∃ reason, stepVerdict s r = .failed reason) ↔
      ∃ c complete,
        r.outcome = Outcome.exited c ∧
          r.frame = Frame.ok (Child.exited c) complete ∧
          r.exhausted = false ∧ ((c ≠ 0 ∧ s ≠ .libraryRoots) ∨ (c = 0 ∧ complete = false)) := by
  constructor
  · rintro ⟨reason, h⟩
    exact failed_shape s r reason h
  · rintro ⟨c, complete, ho, hf, hx, hc⟩
    rcases r with ⟨o, f, ex, d⟩
    simp only at ho hf hx
    subst ho hf hx
    rcases hc with ⟨hc, hs⟩ | ⟨rfl, rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      exact ⟨d, by simp [stepVerdict, Child.helperExit, hs]⟩
    · exact ⟨"a build output is missing", by simp [stepVerdict, Child.helperExit]⟩

/-- P8: the driver executes exactly the steps up to + including the first one that does not pass,
in order, + returns that step with its verdict; every step passing ⇒ all run + `none`. -/
theorem drive_trace (answer : Step → StepResult) :
    ∀ (steps acc : List Step),
      ((∀ s ∈ steps, stepVerdict s (answer s) = .pass) →
          (drive (record answer) steps).run acc = (none, acc ++ steps)) ∧
        ∀ pre s post,
          steps = pre ++ s :: post →
            (∀ p ∈ pre, stepVerdict p (answer p) = .pass) →
            stepVerdict s (answer s) ≠ .pass →
            (drive (record answer) steps).run acc =
              (some (s, stepVerdict s (answer s)), acc ++ pre ++ [s])
  | [], acc =>
    ⟨fun _ => by simp [drive, StateT.run, pure, StateT.pure], fun pre s post h => by
      cases pre <;> simp at h⟩
  | x :: rest, acc => by
    have ih := drive_trace answer rest (acc ++ [x])
    constructor
    · intro hall
      have hx := hall x List.mem_cons_self
      have := ih.1 (fun s hs => hall s (List.mem_cons_of_mem x hs))
      simp only [drive, record, bind, StateT.bind, StateT.run, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, hx] at this ⊢
      simpa [List.append_assoc] using this
    · intro pre s post hsplit hpre hs
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨rfl, rfl⟩ := hsplit
        simp only [drive, record, bind, StateT.bind, StateT.run, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure]
        simp_all
      | cons p pre' =>
        simp only [List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨hxp, hrest⟩ := hsplit
        subst hxp
        have hp := hpre x List.mem_cons_self
        have := ih.2 pre' s post hrest (fun q hq => hpre q (List.mem_cons_of_mem x hq)) hs
        simp only [drive, record, bind, StateT.bind, StateT.run, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, hp] at this ⊢
        simpa [List.append_assoc] using this

theorem stem_char_inj (c d : Char) (hc : c ≠ '/') (hd : d ≠ '/')
    (h : (if c == '.' then '/' else c) = (if d == '.' then '/' else d)) : c = d := by
  by_cases hc' : c = '.'
  · by_cases hd' : d = '.'
    · rw [hc', hd']
    · simp [hc', hd'] at h; exact absurd h.symm hd
  · by_cases hd' : d = '.'
    · simp [hc', hd'] at h; exact absurd h hc
    · simpa [hc', hd'] using h

/-- S2: distinct module names without `/` have distinct path stems (U3 T3's names have none). -/
theorem stem_injective (a b : String) (ha : '/' ∉ a.toList) (hb : '/' ∉ b.toList)
    (h : stem a = stem b) : a = b := by
  have hl :
    a.toList.map (fun c => if c == '.' then '/' else c) =
      b.toList.map (fun c => if c == '.' then '/' else c) := by
    simpa [stem, String.toList_map] using congrArg String.toList h
  apply String.ext
  have key :
    ∀ xs ys : List Char,
      '/' ∉ xs →
        '/' ∉ ys →
        xs.map (fun c => if c == '.' then '/' else c) =
          ys.map (fun c => if c == '.' then '/' else c) →
        xs = ys := by
    intro xs
    induction xs with
    | nil =>
      intro ys _ _ h; cases ys <;> simp_all
    | cons x xs ih =>
      intro ys hx hy h
      cases ys with
      | nil => simp at h
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at h
        simp only [List.mem_cons, not_or] at hx hy
        rw [stem_char_inj x y (Ne.symm hx.1) (Ne.symm hy.1) h.1, ih ys hx.2 hy.2 h.2]
  exact key _ _ ha hb hl

end FvdepAudit.Phase.Proof
