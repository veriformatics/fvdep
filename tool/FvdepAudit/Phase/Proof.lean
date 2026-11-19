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

/-- K2 + P5: an import is the consumer's own refusal exactly when it names no listed, phase-1,
toolchain or library-held module. -/
theorem import_absent (listed built : List String) (present : String → Bool) (m : String) :
    importClass listed built present m = .absent ↔
      m ∉ listed ∧ m ∉ built ∧ FvdepCore.Build.toolchainModule m = false ∧ present m = false := by
  unfold importClass
  by_cases h1 : m ∈ listed <;> by_cases h2 : m ∈ built <;>
    cases h3 : FvdepCore.Build.toolchainModule m <;>
    cases h4 : present m <;>
    simp_all

/-- K2 + P5: an import reads the library exactly when it names no listed, phase-1 or toolchain
module + the library holds its source. -/
theorem import_library (listed built : List String) (present : String → Bool) (m : String) :
    importClass listed built present m = .library ↔
      m ∉ listed ∧ m ∉ built ∧ FvdepCore.Build.toolchainModule m = false ∧ present m = true := by
  unfold importClass
  by_cases h1 : m ∈ listed <;> by_cases h2 : m ∈ built <;>
    cases h3 : FvdepCore.Build.toolchainModule m <;>
    cases h4 : present m <;>
    simp_all

/-- S1: the snapshot reads a component exactly when it is the module's file, a regular file within
the per-file cap + the remaining total, under the smaller of the two caps. -/
theorem snap_reads (l : SourceLimits) (used : Nat) (leaf : Bool) (o : Opened) (cap : Nat) :
    snapDecide l used leaf o = .read cap ↔
      leaf = true ∧
        ∃ size,
          o = .file .regular size ∧
            size ≤ l.fileBytes ∧
            used + size ≤ l.totalBytes ∧ cap = min l.fileBytes (l.totalBytes - used) := by
  cases o with
  | error n => simp [snapDecide]
  | file k size =>
    cases leaf with
    | false => cases k <;> simp [snapDecide]
    | true =>
      cases k with
      | regular =>
        simp only [snapDecide, beq_self_eq_true, ↓reduceIte, true_and, Opened.file.injEq,
          exists_eq_left']
        by_cases h1 : l.fileBytes < size
        · simp only [h1, ↓reduceIte, reduceCtorEq, false_iff, not_and]
          intro h; omega
        · by_cases h2 : l.totalBytes < used + size
          · simp only [h1, h2, ↓reduceIte, reduceCtorEq, false_iff, not_and]
            intro _ h; omega
          · simp only [h1, h2, ↓reduceIte, Snap.read.injEq]
            constructor
            · intro h; exact ⟨by omega, by omega, h.symm⟩
            · intro h; exact h.2.2.symm
      | _ => simp [snapDecide]

/-- S1: the snapshot descends exactly into a directory on the way. -/
theorem snap_descends (l : SourceLimits) (used : Nat) (leaf : Bool) (o : Opened) :
    snapDecide l used leaf o = .descend ↔ leaf = false ∧ ∃ size, o = .file .directory size := by
  cases o with
  | error n => simp [snapDecide]
  | file k size =>
    cases leaf with
    | false => cases k <;> simp [snapDecide]
    | true =>
      cases k with
      | regular =>
        simp only [snapDecide, beq_self_eq_true, ↓reduceIte]
        split
        · simp
        · split <;> simp
      | _ => simp [snapDecide]

/-- S1: a leaf read is accepted exactly when it stayed within its cap. -/
theorem snap_read_accepts (l : SourceLimits) (used cap n total : Nat) :
    snapRead l used cap n = .ok total ↔ n ≤ cap ∧ total = used + n := by
  unfold snapRead
  by_cases h : n ≤ cap
  · simp only [h, ↓reduceIte, Except.ok.injEq, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp only [h, ↓reduceIte, false_and, iff_false]
    split <;> simp

theorem snap_names_go (ms seen : List String) :
    snapNames.go seen ms = none ↔
      (∀ m ∈ ms, ((m.splitOn ".").all fun c => FvdepCore.Manifest.isComponent c.toList) = true) ∧
        ms.Nodup ∧ ∀ m ∈ ms, m ∉ seen := by
  induction ms generalizing seen with
  | nil => simp [snapNames.go]
  | cons m rest
    ih =>
    by_cases hp : ((m.splitOn ".").all fun c => FvdepCore.Manifest.isComponent c.toList) = true
    · by_cases hs : m ∈ seen
      · simp [snapNames.go, hp, hs]
      · have e : snapNames.go seen (m :: rest) = snapNames.go (m :: seen) rest := by
          simp [snapNames.go, hp, hs]
        rw [e, ih]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hp
            · exact h1 x hx
          · exact List.nodup_cons.mpr ⟨fun hm => h3 m hm List.mem_cons_self, h2⟩
          · intro x hx hxs
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hs hxs
            · exact h3 x hx (List.mem_cons_of_mem m hxs)
        · rintro ⟨h1, h2, h3⟩
          refine ⟨fun x hx => h1 x (List.mem_cons_of_mem m hx), (List.nodup_cons.mp h2).2, ?_⟩
          intro x hx hxs
          rcases List.mem_cons.mp hxs with rfl | hxs
          · exact (List.nodup_cons.mp h2).1 hx
          · exact h3 x (List.mem_cons_of_mem _ hx) hxs
    · have e : snapNames.go seen (m :: rest) = some (m, .notModuleName) := by
        simp [snapNames.go, hp]
      rw [e]
      simp only [reduceCtorEq, false_iff, not_and]
      intro h
      exact absurd (h m List.mem_cons_self) hp

/-- S1: the names pass exactly when every listed name is dot-separated U3 T3 components + none is
listed twice. -/
theorem snap_names_none (ms : List String) :
    snapNames ms = none ↔
      (∀ m ∈ ms, ((m.splitOn ".").all fun c => FvdepCore.Manifest.isComponent c.toList) = true) ∧
        ms.Nodup := by
  simp [snapNames, snap_names_go]

/-- P5 + P8: phase 1's observation = `ok e1` exactly when its driver passed every step, `failed r`
exactly when the stopping step failed with `r`, the stopping step's infrastructure otherwise. -/
theorem observe1_exact (o : Option (Step × Verdict)) (e1 : String) :
    (observe1 o e1 = .phase1 (.ok e1) ↔ o = none) ∧
      (∀ r, observe1 o e1 = .phase1 (.failed r) ↔ ∃ s, o = some (s, .failed r)) ∧
      ∀ (c : FvdepCore.Evidence.Infra) (d : String) (s : Step),
        o = some (s, .infra c d) → observe1 o e1 = .infra c d := by
  rcases o with _ | ⟨s, v⟩
  · simp [observe1]
  · cases v <;> simp [observe1]

/-- P5 + P8 for phase 2, bound to the e1 it was built on. -/
theorem observe2_exact (o : Option (Step × Verdict)) (e1 e2 : String) :
    (observe2 e1 o e2 = .phase2 e1 (.ok e2) ↔ o = none) ∧
      (∀ r, observe2 e1 o e2 = .phase2 e1 (.failed r) ↔ ∃ s, o = some (s, .failed r)) ∧
      ∀ (c : FvdepCore.Evidence.Infra) (d : String) (s : Step),
        o = some (s, .infra c d) → observe2 e1 o e2 = .infra c d := by
  rcases o with _ | ⟨s, v⟩
  · simp [observe2]
  · cases v <;> simp [observe2]

/-- P6: phase 2 runs on `e1` exactly when phase 1 observed `ok e1`. -/
theorem handoff_exact (o : FvdepCore.Evidence.Obs) (e1 : String) :
    handoff o = some e1 ↔ o = .phase1 (.ok e1) := by
  match o with
  | .phase1 (.ok d) => simp [handoff]
  | .phase1 (.failed r) => simp [handoff]
  | .implProfile _ | .phase2 _ _ | .statement _ _ _ | .graph _ _ _ | .axioms _ _ | .kernel _ _ _ |
    .infra _ _ | .compare _ _ _ _ => simp [handoff]

/-- P8: the driver never stops on a passing step (the outcome `observe1` + `observe2` read). -/
theorem drive_stops_not_pass (answer : Step → StepResult) :
    ∀ (steps acc : List Step) (s : Step) (v : Verdict) (t : List Step),
      (drive (record answer) steps).run acc = (some (s, v), t) → v ≠ .pass
  | [], acc, s, v, t, h => by
    have e := (drive_trace answer [] acc).1 (by simp)
    rw [e] at h
    cases h
  | x :: rest, acc, s, v, t, h => by
    by_cases hx : stepVerdict x (answer x) = .pass
    · have ih := drive_stops_not_pass answer rest (acc ++ [x]) s v t
      simp only [drive, record, bind, StateT.bind, StateT.run, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, hx] at h ih
      exact ih h
    · have e := (drive_trace answer (x :: rest) acc).2 [] x rest rfl (by simp) hx
      rw [e] at h
      injection h with h1 _
      injection h1 with h2
      injection h2 with _ h3
      rw [← h3]
      exact hx

/-- P1: the deadline window = each compile in K2's order, then the roots check, then the export. -/
theorem steps_plan (order : List String) :
    steps order = order.map Step.compile ++ [.consumerRoots, .exportStep] := rfl

/-- P2: a module's artifact family — `.olean`, `.ilean`, `.c`, + under a `module` header
`.olean.server`, `.olean.private`, `.ir`, `.ir.sig`. -/
theorem family_exact (isModule : Bool) (m f : String) :
    f ∈ family isModule m ↔
      f = stem m ++ ".olean" ∨
        isModule = true ∧
          (f = stem m ++ ".olean.server" ∨
            f = stem m ++ ".olean.private" ∨ f = stem m ++ ".ir" ∨ f = stem m ++ ".ir.sig") ∨
        f = stem m ++ ".ilean" ∨ f = stem m ++ ".c" := by
  cases isModule <;> simp [family, or_assoc]

/-- S2 → H3: distinct module names without `/` frame distinct paths. -/
theorem source_files_distinct (ms : List (String × ByteArray)) :
    (ms.map (·.1)).Nodup → (∀ m ∈ ms, '/' ∉ m.1.toList) → ((sourceFiles ms).map (·.1)).Nodup := by
  intro hn hs
  simp only [sourceFiles, List.map_map]
  induction ms with
  | nil => simp
  | cons x xs
    ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, Function.comp] at hn ⊢
    refine ⟨?_, ih hn.2 (fun m hm => hs m (List.mem_cons_of_mem x hm))⟩
    rintro ⟨y, hy, hxy⟩
    have hyx : stem y.1 = stem x.1 := by
      have h := congrArg String.toList hxy
      simp only [String.toList_append] at h
      exact String.ext (List.append_cancel_right h)
    have := stem_injective y.1 x.1 (hs y (List.mem_cons_of_mem x hy)) (hs x List.mem_cons_self) hyx
    exact hn.1 ⟨y, hy, this⟩

theorem import_listed (listed built : List String) (present : String → Bool) (m : String) :
    importClass listed built present m = .listed ↔ m ∈ listed := by
  unfold importClass
  by_cases h1 : m ∈ listed <;> by_cases h2 : m ∈ built <;>
    cases h3 : FvdepCore.Build.toolchainModule m <;>
    cases h4 : present m <;>
    simp_all

theorem import_built (listed built : List String) (present : String → Bool) (m : String) :
    importClass listed built present m = .built ↔ m ∉ listed ∧ m ∈ built := by
  unfold importClass
  by_cases h1 : m ∈ listed <;> by_cases h2 : m ∈ built <;>
    cases h3 : FvdepCore.Build.toolchainModule m <;>
    cases h4 : present m <;>
    simp_all

theorem import_toolchain (listed built : List String) (present : String → Bool) (m : String) :
    importClass listed built present m = .toolchain ↔
      m ∉ listed ∧ m ∉ built ∧ FvdepCore.Build.toolchainModule m = true := by
  unfold importClass
  by_cases h1 : m ∈ listed <;> by_cases h2 : m ∈ built <;>
    cases h3 : FvdepCore.Build.toolchainModule m <;>
    cases h4 : present m <;>
    simp_all

theorem snap_read_refuses (l : SourceLimits) (used n : Nat) :
    min l.fileBytes (l.totalBytes - used) < n →
      (l.totalBytes - used < l.fileBytes →
          snapRead l used (min l.fileBytes (l.totalBytes - used)) n =
            .error (.grewTotal l.totalBytes)) ∧
        (l.fileBytes < l.totalBytes - used →
          snapRead l used (min l.fileBytes (l.totalBytes - used)) n =
            .error (.grewFile l.fileBytes)) ∧
        (l.fileBytes = l.totalBytes - used →
          snapRead l used (min l.fileBytes (l.totalBytes - used)) n =
              .error (.grewFile l.fileBytes) ∨
            snapRead l used (min l.fileBytes (l.totalBytes - used)) n =
              .error (.grewTotal l.totalBytes)) := by
  intro h
  refine ⟨fun h2 => ?_, fun h2 => ?_, fun h2 => ?_⟩
  · unfold snapRead
    split
    · omega
    · split
      · omega
      · rfl
  · unfold snapRead
    split
    · omega
    · split
      · rfl
      · omega
  · left
    unfold snapRead
    split
    · omega
    · split
      · rfl
      · omega

theorem snap_names_go_some (seen ms : List String) (m : String) (r : Refusal) :
    snapNames.go seen ms = some (m, r) →
      m ∈ ms ∧
        (r = .notModuleName →
          ((m.splitOn ".").all fun c => FvdepCore.Manifest.isComponent c.toList) = false) ∧
        (r = .listedTwice → m ∈ seen ∨ 2 ≤ ms.count m) := by
  induction ms generalizing seen with
  | nil => simp [snapNames.go]
  | cons x xs ih =>
    intro h
    by_cases hp : ((x.splitOn ".").all fun c => FvdepCore.Manifest.isComponent c.toList) = true
    · by_cases hs : x ∈ seen
      · have e : snapNames.go seen (x :: xs) = some (x, .listedTwice) := by
          simp [snapNames.go, hp, hs]
        rw [e] at h
        injection h with h
        injection h with h1 h2
        subst h1 h2
        exact ⟨List.mem_cons_self, (fun h => by cases h), fun _ => Or.inl hs⟩
      · have e : snapNames.go seen (x :: xs) = snapNames.go (x :: seen) xs := by
          simp [snapNames.go, hp, hs]
        rw [e] at h
        obtain ⟨h1, h2, h3⟩ := ih (x :: seen) h
        refine ⟨List.mem_cons_of_mem x h1, h2, fun hr => ?_⟩
        rcases h3 hr with h4 | h4
        · rcases List.mem_cons.mp h4 with rfl | h4
          · right
            have := List.count_pos_iff.mpr h1
            simp
            omega
          · exact Or.inl h4
        · right
          exact Nat.le_trans h4 List.count_le_count_cons
    · have e : snapNames.go seen (x :: xs) = some (x, .notModuleName) := by simp [snapNames.go, hp]
      rw [e] at h
      injection h with h
      injection h with h1 h2
      subst h1 h2
      exact ⟨List.mem_cons_self, (fun _ => by simpa using hp), (fun h => by cases h)⟩

theorem snap_names_some (ms : List String) (m : String) (r : Refusal) :
    snapNames ms = some (m, r) →
      m ∈ ms ∧
        (r = .notModuleName ∧
            ((m.splitOn ".").all fun c => FvdepCore.Manifest.isComponent c.toList) = false ∨
          r = .listedTwice ∧ 2 ≤ ms.count m) := by
  intro h
  have hr : r = .notModuleName ∨ r = .listedTwice := by
    have key :
      ∀ (seen ms : List String) (m : String) (r : Refusal),
        snapNames.go seen ms = some (m, r) → r = .notModuleName ∨ r = .listedTwice := by
      intro seen ms
      induction ms generalizing seen with
      | nil =>
        intro m r h; simp [snapNames.go] at h
      | cons x xs ih =>
        intro m r h
        simp only [snapNames.go] at h
        split at h
        · injection h with h; injection h with _ h; exact Or.inl h.symm
        · split at h
          · injection h with h; injection h with _ h; exact Or.inr h.symm
          · exact ih _ m r h
    exact key [] ms m r h
  obtain ⟨h1, h2, h3⟩ := snap_names_go_some [] ms m r h
  refine ⟨h1, ?_⟩
  rcases hr with rfl | rfl
  · exact Or.inl ⟨rfl, h2 rfl⟩
  · rcases h3 rfl with h | h
    · simp at h
    · exact Or.inr ⟨rfl, h⟩

theorem family_nodup (isModule : Bool) (m : String) : (family isModule m).Nodup := by
  have key : ∀ a b : String, stem m ++ a = stem m ++ b ↔ a = b := by
    intro a b
    constructor
    · intro h
      have h' := congrArg String.toList h
      simp only [String.toList_append] at h'
      exact String.ext (List.append_cancel_left h')
    · intro h
      rw [h]
  cases isModule <;> simp [family, key]

theorem source_files_exact (ms : List (String × ByteArray)) (p : String) (b : ByteArray) :
    (p, b) ∈ sourceFiles ms ↔ ∃ m, (m, b) ∈ ms ∧ p = stem m ++ ".lean" := by
  simp only [sourceFiles, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨m, b'⟩, h, h1, h2⟩
    subst h2
    exact ⟨m, h, h1.symm⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨(m, b), h, rfl, rfl⟩

theorem phase_plan_first (order : List String) :
    phasePlan 1 order = .libraryRoots :: steps order ∧ phasePlan 2 order = steps order := by
  simp [phasePlan]

end FvdepAudit.Phase.Proof
