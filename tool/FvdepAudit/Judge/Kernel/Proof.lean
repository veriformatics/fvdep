import FvdepAudit.Judge.Kernel.Spec
import FvdepCore.Judge.Profile

/-! Proofs: K2's status table (contract `docs/contracts/U7-judge.md` K2) — `kernelStatus` reports
accept, reject, decline, infrastructure + timeout exactly in the spec's cases (crash = the rest) —
+ V2's bridge (U2's challenge profile from v1). -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Evidence FvdepCore.Phase FvdepCore.Sandbox FvdepCore.Judge
  FvdepAudit.Judge.Kernel.Spec

theorem bytesAre_iff (s : String) (b : ByteArray) :
    bytesAre s b = true ↔ b.data.toList = utf8 s := by simp only [bytesAre, utf8, beq_iff_eq]

theorem bytesAre_empty (b : ByteArray) : bytesAre "" b = true ↔ b.data.toList = [] := by
  rw [bytesAre_iff]
  simp [utf8]

theorem bytesStart_iff (p : String) (b : ByteArray) :
    bytesStart p b = true ↔ utf8 p <+: b.data.toList := by
  simp only [bytesStart, utf8, List.isPrefixOf_iff_prefix]

theorem utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by simp [utf8]

/-- A list split as head ++ a nonempty middle ++ tail, the middle's members all `P`. -/
theorem mid_iff {α : Type} (p q xs : List α) (P : α → Prop) :
    (p <+: xs ∧
        q <:+ xs ∧
        p.length + q.length < xs.length ∧
        ∀ d ∈ (xs.drop p.length).take (xs.length - p.length - q.length), P d) ↔
      ∃ ds, ds ≠ [] ∧ (∀ d ∈ ds, P d) ∧ xs = p ++ ds ++ q := by
  constructor
  · rintro ⟨⟨t, rfl⟩, hq, hl, hd⟩
    simp only [List.length_append] at hl
    have hq' : q = t.drop (t.length - q.length) := by
      have h1 := List.suffix_iff_eq_drop.1 hq
      rw [List.length_append] at h1
      have : p.length + t.length - q.length = p.length + (t.length - q.length) := by omega
      rw [this, List.drop_append, List.drop_of_length_le (by omega), List.nil_append,
        Nat.add_sub_cancel_left] at h1
      exact h1
    refine ⟨t.take (t.length - q.length), ?_, ?_, ?_⟩
    · intro h
      have := congrArg List.length h
      simp only [List.length_take, List.length_nil] at this
      omega
    · intro d hd'
      apply hd
      have e : (p ++ t).length - p.length - q.length = t.length - q.length := by
        simp only [List.length_append]
        omega
      rw [e, List.drop_left]
      exact hd'
    · rw [List.append_assoc]
      congr 1
      conv =>
        lhs; rw [← List.take_append_drop (t.length - q.length) t]
      rw [← hq']
  · rintro ⟨ds, hne, hd, rfl⟩
    have hpos : 0 < ds.length := by
      cases ds with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    refine ⟨⟨ds ++ q, by simp⟩, ⟨p ++ ds, by simp⟩, ?_, ?_⟩
    · simp only [List.length_append]
      omega
    · intro d hd'
      apply hd
      have e : (p ++ ds ++ q).length - p.length - q.length = ds.length := by
        simp only [List.length_append]
        omega
      rw [e, List.append_assoc, List.drop_left, List.take_left] at hd'
      exact hd'

theorem isConAccept_iff (b : ByteArray) :
    isConAccept b = true ↔
      ∃ ds : List UInt8,
        ds ≠ [] ∧
          (∀ d ∈ ds, 48 ≤ d ∧ d ≤ 57) ∧
          b.data.toList = utf8 conAcceptHead ++ ds ++ utf8 conAcceptTail := by
  have hd : ∀ d : UInt8, isDigitByte d = true ↔ 48 ≤ d ∧ d ≤ 57 := fun d => by simp [isDigitByte]
  rw [← mid_iff]
  simp only [isConAccept, Bool.and_eq_true, List.isPrefixOf_iff_prefix, List.isSuffixOf_iff_suffix,
    decide_eq_true_eq, List.all_eq_true, hd, utf8, and_assoc]

/-! ## The table -/

theorem acceptsB_iff (k : Kernel) (c : Nat) (out err : ByteArray) :
    acceptsB k c out err = true ↔ Accepts k c out err := by
  rcases k with _ | _ | _ <;> rcases c with _ | c <;>
    simp [acceptsB, Accepts, bytesAre_iff, isConAccept_iff, utf8]

theorem rejectsB_iff (k : Kernel) (c : Nat) (out err : ByteArray) :
    rejectsB k c out err = true ↔ Rejects k c out err := by
  rcases k with _ | _ | _ <;> rcases c with _ | _ | c <;>
    simp [rejectsB, Rejects, bytesStart_iff, utf8_append]

theorem declinesB_iff (k : Kernel) (c : Nat) (err : ByteArray) :
    declinesB k c err = true ↔ Declines k c err := by
  rcases k with _ | _ | _ <;> rcases c with _ | _ | _ | c <;>
    simp [declinesB, Declines, bytesStart_iff]

theorem accepts_code {k : Kernel} {c : Nat} {out err : ByteArray} (h : Accepts k c out err) :
    c = 0 := by rcases k with _ | _ | _ <;> rcases c with _ | c <;> simp_all [Accepts]

theorem rejects_code {k : Kernel} {c : Nat} {out err : ByteArray} (h : Rejects k c out err) :
    c = 1 := by rcases k with _ | _ | _ <;> rcases c with _ | _ | c <;> simp_all [Rejects]

theorem declines_code {k : Kernel} {c : Nat} {err : ByteArray} (h : Declines k c err) : c = 2 := by
  rcases k with _ | _ | _ <;> rcases c with _ | _ | _ | c <;> simp_all [Declines]

theorem table_accept (k : Kernel) (c : Nat) (out err : ByteArray) (whole : Bool) :
    kernelTable k c out err whole = .accept ↔ whole = true ∧ Accepts k c out err := by
  rw [← acceptsB_iff]
  unfold kernelTable
  by_cases ha : acceptsB k c out err = true <;> by_cases hr : rejectsB k c out err = true <;>
    by_cases hd : declinesB k c err = true <;>
    cases whole <;>
    simp [ha, hr, hd]

theorem table_reject (k : Kernel) (c : Nat) (out err : ByteArray) (whole : Bool) :
    kernelTable k c out err whole = .reject ↔ Rejects k c out err := by
  have hx : Rejects k c out err → acceptsB k c out err = false := fun h => by
    have := rejects_code h
    subst this
    rcases k with _ | _ | _ <;> rfl
  have hdc :
    ∀ (b : Bool) (d : String), (if b = true then KernelStatus.decline d else .crash) ≠ .reject :=
    fun b _ => by cases b <;> simp
  rw [← rejectsB_iff]
  unfold kernelTable
  by_cases hr : rejectsB k c out err = true
  · have ha := hx ((rejectsB_iff k c out err).1 hr)
    cases whole <;> simp [ha, hr]
  · by_cases ha : acceptsB k c out err = true <;> cases whole <;> simp [ha, hr, hdc]

theorem table_decline (k : Kernel) (c : Nat) (out err : ByteArray) (whole : Bool) :
    (∃ d, kernelTable k c out err whole = .decline d) ↔ Declines k c err := by
  have hx : Declines k c err → acceptsB k c out err = false ∧ rejectsB k c out err = false :=
    fun h => by
    have := declines_code h
    subst this
    rcases k with _ | _ | _ <;> exact ⟨rfl, rfl⟩
  rw [← declinesB_iff]
  unfold kernelTable
  by_cases hd : declinesB k c err = true
  · obtain ⟨ha, hr⟩ := hx ((declinesB_iff k c err).1 hd)
    cases whole <;> simp [ha, hr, hd]
  · by_cases ha : acceptsB k c out err = true <;> by_cases hr : rejectsB k c out err = true <;>
      cases whole <;>
      simp [ha, hr, hd]

theorem table_ne_timeout (k : Kernel) (c : Nat) (out err : ByteArray) (whole : Bool) (s : Nat) :
    kernelTable k c out err whole ≠ .timeout s := by
  unfold kernelTable
  split
  · exact fun h => nomatch h
  · split
    · exact fun h => nomatch h
    · split
      · exact fun h => nomatch h
      · exact fun h => nomatch h

theorem shape_status (s : KernelStatus) :
    ((KResult.status s).shape = .accept ↔ s = .accept) ∧
      ((KResult.status s).shape = .reject ↔ s = .reject) ∧
      ((KResult.status s).shape = .decline ↔ ∃ d, s = .decline d) ∧
      (∀ t, (KResult.status s).shape = .timeout t ↔ s = .timeout t) ∧
      ∀ c, (KResult.status s).shape ≠ .infra c := by
  cases s <;> simp [KResult.shape]

/-! ## K2 -/

/-- U7 K2 `kernelStatusExact`. -/
theorem kernelStatus_exact (k : Kernel) (r : KernelRun) :
    ((kernelStatus k r).shape = .accept ↔
        ∃ c, Exited r c ∧ r.whole = true ∧ Accepts k c r.stdout r.stderr) ∧
      ((kernelStatus k r).shape = .reject ↔ ∃ c, Exited r c ∧ Rejects k c r.stdout r.stderr) ∧
      ((kernelStatus k r).shape = .decline ↔ ∃ c, Exited r c ∧ Declines k c r.stderr) ∧
      ((∃ code, (kernelStatus k r).shape = .infra code) ↔ IsInfra r) ∧
      ∀ s, (kernelStatus k r).shape = .timeout s ↔ r.outcome = .timedOut ∧ s = r.deadline := by
  rcases r with ⟨outcome, frame, out, err, whole, dl⟩
  cases outcome with
  | setupFailed d => simp [kernelStatus, KResult.shape, Exited, IsInfra]
  | protocol => simp [kernelStatus, KResult.shape, Exited, IsInfra]
  | timedOut =>
    simp [kernelStatus, KResult.shape, Exited, IsInfra]
    exact fun _ => eq_comm
  | exited n =>
    cases frame with
    | invalid => simp [kernelStatus, KResult.shape, Exited, IsInfra]
    | overflow => simp [kernelStatus, KResult.shape, Exited, IsInfra]
    | ok child files full =>
      by_cases h1 : child.helperExit = n
      · by_cases h2 : files = 0
        · subst h2
          cases full
          · cases child with
            | notStarted w =>
              simp [kernelStatus, KResult.shape, Exited, IsInfra, h1]
              exact ⟨_, _, ⟨rfl, rfl⟩, Or.inr (Or.inr ⟨w, rfl⟩)⟩
            | signaled sg =>
              simp only [Child.helperExit] at h1
              subst h1
              simp [kernelStatus, KResult.shape, Exited, IsInfra, Child.helperExit]
            | exited c =>
              simp only [Child.helperExit] at h1
              subst h1
              obtain ⟨sa, sr, sd, st, si⟩ := shape_status (kernelTable k c out err whole)
              have hk :
                kernelStatus k ⟨.exited c, .ok (.exited c) 0 false, out, err, whole, dl⟩ =
                  .status (kernelTable k c out err whole) := by
                simp [kernelStatus, Child.helperExit]
              rw [hk, sa, sr, sd, table_accept, table_reject, table_decline]
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simp [Exited]
              · simp [Exited]
              · simp [Exited]
              · simp only [si, exists_false, false_iff]
                simp [IsInfra, Child.helperExit]
              · intro t
                rw [st]
                simp [table_ne_timeout]
          · simp [kernelStatus, KResult.shape, Exited, IsInfra, h1]
        · simp [kernelStatus, KResult.shape, Exited, IsInfra, h1, h2]
          refine ⟨child, files, ?_⟩
          cases full <;> simp [h2]
      · have hne : child ≠ .exited n := fun hc =>
          h1
            (by
              rw [hc]; rfl)
        simp [kernelStatus, KResult.shape, Exited, IsInfra, h1, hne]
        refine ⟨child, files, ?_⟩
        cases full <;> simp [h1]

/-! ## K4 -/

/-- U7 K4 `pinCheckExact`. -/
theorem pinCheck_exact (p : VProfile) (f : String) (d : Kernel → Option String) :
    pinCheck p f d = none ↔
      f = p.fingerprint ∧ ∀ k ∈ kernels, ∀ h, d k = some h → h = (p.kernel k).sha256 := by
  unfold pinCheck
  by_cases hf : f = p.fingerprint
  · subst hf
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, true_and,
      List.findSome?_eq_none_iff]
    apply forall_congr'
    intro k
    apply forall_congr'
    intro _
    cases hd : d k with
    | none => simp
    | some h => by_cases e : h = (p.kernel k).sha256 <;> simp [e]
  · simp [hf]

/-! ## V2 -/

/-- U7 V2 `profileBridge`. -/
theorem profile_bridge :
    v1.evidence = ⟨"fvdep/verification/1", ["propext", "Classical.choice", "Quot.sound"]⟩ := rfl

end FvdepAudit.Judge.Proof
