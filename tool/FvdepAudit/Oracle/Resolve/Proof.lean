import FvdepAudit.Oracle.Resolve.Spec

/-! The oracle's entry resolution against its spec (contract `docs/contracts/U5b-oracle.md` E1–E5):
the target grammar's operations, the row, the coherence, E5's countdown = the spec's size, the
entry stage + its budget refusal, the signature stage + its type refusal. Headers = the ledger
statements. -/

namespace FvdepAudit.Oracle.Resolve.Proof

open Lean FvdepCore FvdepCore.Ids FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Assemble FvdepCore.Oracle FvdepAudit.Oracle.Resolve.Spec

/-- E1: an operation target = exactly the printed `<id>@<x.y.z>` (U2 I4's canonical reference). -/
theorem target_op (s : String) (m : ModuleId) (v : EntryVersion) :
    Target.parse s = some (.op m v) ↔ toString (⟨m, some v⟩ : ModuleRef) = s := by
  unfold Target.parse
  constructor
  · intro h
    match hp : ModuleRef.parse s with
    | some ⟨m', some v'⟩ =>
      rw [hp] at h
      simp only [Option.some.injEq, Target.op.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ModuleRef.toString_parse hp
    | some ⟨_, none⟩ =>
      rw [hp] at h
      cases h
    | none =>
      rw [hp] at h
      dsimp only at h
      split at h <;> cases h
  · intro h
    subst h
    rw [ModuleRef.parse_toString]

/-- E1: a row the stage returns is the target's operation of the index. -/
theorem rowOf_listed (i : IndexFile) (m : ModuleId) (v : EntryVersion) (o : Operation) :
    rowOf i m v = some o → Listed i m v o := by
  intro h
  unfold rowOf at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.1, hp.2⟩

/-- E1: no row exactly when the index lists no operation with the target's id + version. -/
theorem rowOf_none (i : IndexFile) (m : ModuleId) (v : EntryVersion) :
    rowOf i m v = none ↔ ∀ o, ¬Listed i m v o := by
  unfold rowOf Listed
  rw [List.find?_eq_none]
  constructor
  · intro h o ⟨hm, hid, hv⟩
    have := h o hm
    simp [hid, hv] at this
  · intro h o hm
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro hid hv
    exact h o ⟨hm, hid, hv⟩

/-- E2: coherent exactly when the stage finds no failure. -/
theorem coherence_none (h : ByteArray → String) (tc : String) (i : IndexFile) (o : Operation)
    (M : Name) (srcs : List Src) : coherence h tc i o M srcs = none ↔ Coherent h tc i o M srcs := by
  unfold coherence Coherent
  cases hf : (closure (factsOf srcs) M).find? fun n => !srcs.any fun s => nameOf s.module == n with
  | some n =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [reduceCtorEq, false_iff, not_and]
    intro hall
    obtain ⟨s, hs, hn⟩ := hall n hm
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, beq_iff_eq] at hp
    exact absurd hn (hp s hs)
  | none =>
    have hall : ∀ n ∈ closure (factsOf srcs) M, ∃ s ∈ srcs, nameOf s.module = n := by
      intro n hn
      have := List.find?_eq_none.mp hf n hn
      simpa using this
    dsimp only
    rw [and_iff_right hall]
    by_cases h2 : i.toolchain = trimText tc
    · simp only [h2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, true_and]
      by_cases h3 : o.digest = h (entryFrame (factsOf srcs) M)
      · simp [h3]
      · have h3' : (h (entryFrame (factsOf srcs) M) != o.digest) = true := by
          simpa [bne_iff_ne] using fun e => h3 e.symm
        simp [h3', h3]
    · have h2' : (i.toolchain != trimText tc) = true := by simpa [bne_iff_ne] using h2
      simp [h2', h2]

theorem size_bvar_some {i : Nat} {env : List Expr} {v : Expr} (hv : env[i]? = some v) :
    size (.bvar i) env = 1 + size v (env.drop (i + 1)) := by
  rw [size.eq_def]
  dsimp only
  split <;> simp_all

theorem size_bvar_none {i : Nat} {env : List Expr} (hv : env[i]? = none) :
    size (.bvar i) env = 1 := by
  rw [size.eq_def]
  dsimp only
  split <;> simp_all

theorem within_bvar_some {k i : Nat} {env : List Expr} {v : Expr} (hv : env[i]? = some v) :
    within (k + 1) (.bvar i) env = within k v (env.drop (i + 1)) := by
  rw [within.eq_def]
  dsimp only
  split <;> simp_all

theorem within_bvar_none {k i : Nat} {env : List Expr} (hv : env[i]? = none) :
    within (k + 1) (.bvar i) env = some k := by
  rw [within.eq_def]
  dsimp only
  split <;> simp_all

theorem size_pos (e : Expr) (env : List Expr) : 0 < size e env := by
  cases e with
  | bvar i =>
    cases hv : env[i]? with
    | some v =>
      rw [size_bvar_some hv]
      omega
    | none =>
      rw [size_bvar_none hv]
      omega
  | _ =>
    rw [size.eq_def]
    dsimp only
    omega

/-- One node more on both sides. -/
theorem step_ite (n k : Nat) :
    (if n ≤ k then some (k - n) else none) =
      if 1 + n ≤ k + 1 then some (k + 1 - (1 + n)) else none := by
  by_cases h : n ≤ k
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- E5: the countdown = the spec's size: the budget left, or `none` past it. -/
theorem within_eq (k : Nat) (e : Expr) (env : List Expr) :
    within k e env = if size e env ≤ k then some (k - size e env) else none := by
  have hp := size_pos e env
  match k, e with
  | 0, e => rw [within.eq_def, ite_eq_right (by omega)]
  | k + 1, .mdata d b =>
    have ih := within_eq k b env
    rw [within.eq_def, size.eq_def]
    dsimp only
    rw [ih]
    exact step_ite _ _
  | k + 1, .letE n t v b nd =>
    have ih := within_eq k b (v :: env)
    rw [within.eq_def, size.eq_def]
    dsimp only
    rw [ih]
    exact step_ite _ _
  | k + 1, .bvar i =>
    match hv : env[i]? with
    | some v =>
      have := env_le hv
      rw [within_bvar_some hv, size_bvar_some hv, within_eq k v (env.drop (i + 1))]
      exact step_ite _ _
    | none =>
      rw [within_bvar_none hv, size_bvar_none hv, ite_eq_left (by omega)]
      simp
  | k + 1, .app f a =>
    have ihf := within_eq k f env
    rw [within.eq_def, size.eq_def]
    dsimp only
    rw [ihf]
    by_cases hf : size f env ≤ k
    · rw [ite_eq_left hf]
      dsimp only
      rw [within_eq (k - size f env) a env]
      by_cases ha : size a env ≤ k - size f env
      · rw [ite_eq_left ha, ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_right ha, ite_eq_right (by omega)]
    · rw [ite_eq_right hf, ite_eq_right (by omega)]
  | k + 1, .fvar _ | k + 1, .mvar _ | k + 1, .sort _ | k + 1, .const _ _ | k + 1, .lam _ _ _ _ |
    k + 1, .forallE _ _ _ _ | k + 1, .lit _ | k + 1,
    .proj _ _ _ =>
    rw [within.eq_def, size.eq_def]
    dsimp only
    rw [ite_eq_left (by omega)]
    simp
termination_by sizeOf e + envSize env
decreasing_by all_goals (simp; omega)

/-- E5: the stage's countdown passes the budget exactly when the spec's size does. -/
theorem within_none (k : Nat) (e : Expr) (env : List Expr) :
    within k e env = none ↔ k < size e env := by
  rw [within_eq]
  by_cases h : size e env ≤ k
  · rw [ite_eq_left h]
    simp only [reduceCtorEq, false_iff]
    omega
  · rw [ite_eq_right h]
    simp only [true_iff]
    omega

/-- The countdown's `some` = within the budget. -/
theorem within_some {k : Nat} {e : Expr} {env : List Expr} {r : Nat} (h : within k e env = some r) :
    size e env ≤ k := by
  rw [within_eq] at h
  by_cases hs : size e env ≤ k
  · exact hs
  · rw [ite_eq_right hs] at h
    cases h

theorem within_isSome {k : Nat} {e : Expr} {env : List Expr} (h : size e env ≤ k) :
    within k e env = some (k - size e env) := by rw [within_eq, ite_eq_left h]

/-- E3 + E5: the entry stage yields `spec` exactly when the spec's checks all hold. -/
theorem entry_exact (budget : Nat) (m : ModuleId) (v : EntryVersion) (mods : List Name)
    (ds : List Export.Decl) (spec : Name) :
    entrySpec budget m v mods ds = .ok spec ↔ EntryOk budget m v mods ds spec := by
  unfold entrySpec EntryOk EntryDecl
  dsimp only
  constructor
  · intro h
    cases hd : ds.find? (fun x => x.name == .str (entryModule m v) "entry") with
    | none =>
      rw [hd] at h
      cases h
    | some d =>
      rw [hd] at h
      dsimp only at h
      obtain ⟨n, kind, lps, ty, value⟩ := d
      cases kind <;> cases value <;> dsimp only at h <;> try cases h
      rename_i val
      cases hw : within budget val [] with
      | none =>
        rw [hw] at h
        cases h
      | some r =>
        rw [hw] at h
        dsimp only at h
        cases hdec : decode noFacts moduleForm val [] [.str (entryModule m v) "entry"] with
        | error x =>
          rw [hdec] at h
          cases h
        | ok payload =>
          rw [hdec] at h
          dsimp only at h
          by_cases hid : ((entryOf (.entry (entryModule m v) payload)).id != toString m) = true
          · simp only [hid, ↓reduceIte] at h
            cases h
          · simp only [hid, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hver :
              ((entryOf (.entry (entryModule m v) payload)).version != toString v) = true
            · simp only [hver, ↓reduceIte] at h
              cases h
            · simp only [hver, Bool.false_eq_true, ↓reduceIte] at h
              generalize hs : (entryOf (.entry (entryModule m v) payload)).spec = sp at h
              cases sp with
              | str p fn =>
                dsimp only at h
                by_cases hpc :
                  (p == leanModule m v && FvdepCore.Manifest.isComponent fn.toList) = true
                · simp only [hpc, ↓reduceIte] at h
                  by_cases hm : mods.contains (leanModule m v) = true
                  · simp only [hm, ↓reduceIte, Except.ok.injEq] at h
                    subst h
                    simp only [Bool.and_eq_true, beq_iff_eq] at hpc
                    refine
                      ⟨⟨n, .defn, lps, ty, some val⟩, val, payload, rfl, rfl, rfl, within_some hw,
                        hdec, ?_, ?_, hs.symm, ⟨fn, by rw [hpc.1], hpc.2⟩, ?_⟩
                    · simpa [bne_iff_ne] using hid
                    · simpa [bne_iff_ne] using hver
                    · simpa using hm
                  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
                    cases h
                · simp only [hpc, Bool.false_eq_true, ↓reduceIte] at h
                  cases h
              | anonymous =>
                dsimp only at h
                cases h
              | num p k =>
                dsimp only at h
                cases h
  · rintro ⟨d, val, payload, hd, hk, hv, hsz, hdec, hid, hver, hspec, ⟨fn, hfn, hcomp⟩, hm⟩
    rw [hd]
    dsimp only
    obtain ⟨n, kind, lps, ty, value⟩ := d
    dsimp only at hk hv
    subst hk
    subst hv
    dsimp only
    rw [within_isSome hsz]
    dsimp only
    rw [show decode noFacts moduleForm val [] [.str (entryModule m v) "entry"] = .ok payload from
        hdec]
    dsimp only
    have hid' : ((entryOf (.entry (entryModule m v) payload)).id != toString m) = false := by
      simpa [bne_iff_ne] using hid
    have hver' : ((entryOf (.entry (entryModule m v) payload)).version != toString v) = false := by
      simpa [bne_iff_ne] using hver
    simp only [hid', hver', Bool.false_eq_true, ↓reduceIte]
    rw [← hspec, hfn]
    dsimp only
    have hpc :
      (leanModule m v == leanModule m v && FvdepCore.Manifest.isComponent fn.toList) = true := by
      simp [hcomp]
    have hm' : mods.contains (leanModule m v) = true := by simpa using hm
    simp only [hpc, hm', ↓reduceIte]

/-- E5: the entry stage's budget refusal exactly when the spec's size passes the budget. -/
theorem entry_budget (budget : Nat) (m : ModuleId) (v : EntryVersion) (mods : List Name)
    (ds : List Export.Decl) :
    entrySpec budget m v mods ds = .error .budget ↔ EntryOver budget m v ds := by
  unfold entrySpec EntryOver EntryDecl
  dsimp only
  constructor
  · intro h
    cases hd : ds.find? (fun x => x.name == .str (entryModule m v) "entry") with
    | none =>
      rw [hd] at h
      cases h
    | some d =>
      rw [hd] at h
      dsimp only at h
      obtain ⟨n, kind, lps, ty, value⟩ := d
      cases kind <;> cases value <;> dsimp only at h <;> try cases h
      rename_i val
      cases hw : within budget val [] with
      | none => exact ⟨_, val, rfl, rfl, rfl, (within_none _ _ _).mp hw⟩
      | some r =>
        rw [hw] at h
        dsimp only at h
        cases hdec : decode noFacts moduleForm val [] [.str (entryModule m v) "entry"] with
        | error x =>
          rw [hdec] at h
          cases h
        | ok payload =>
          rw [hdec] at h
          dsimp only at h
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · split at h
                · split at h
                  · cases h
                  · cases h
                · cases h
              · cases h
  · rintro ⟨d, val, hd, hk, hv, hsz⟩
    rw [hd]
    obtain ⟨n, kind, lps, ty, value⟩ := d
    dsimp only at hk hv
    subst hk
    subst hv
    dsimp only
    rw [(within_none budget val []).mpr hsz]

/-- E4: the signature stage yields `sig` exactly when the spec's checks hold. -/
theorem sig_exact (spec : Name) (ds : List Export.Decl) (sig : Protocol.Sig) :
    specSig spec ds = .ok sig ↔ SigOk spec ds sig := by
  unfold specSig SigOk
  cases hd : ds.find? (fun x => x.name == spec) with
  | none => simp
  | some d =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases hk : d.kind = .defn
    · simp only [hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, true_and]
      cases hs : Protocol.sigOf d.type with
      | none => simp
      | some ar =>
        obtain ⟨args, r⟩ := ar
        obtain ⟨op, args', r'⟩ := sig
        simp only [Except.ok.injEq, Protocol.Sig.mk.injEq, Option.some.injEq, Prod.mk.injEq]
        have hf : fnOf spec = lastPart spec := by cases spec <;> rfl
        rw [hf]
        constructor
        · rintro ⟨rfl, rfl, rfl⟩
          exact ⟨⟨rfl, rfl⟩, rfl⟩
        · rintro ⟨⟨rfl, rfl⟩, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
    · have : (d.kind != .defn) = true := by simpa [bne_iff_ne] using hk
      simp [this, hk]

/-- E4: the type refusal exactly when the spec is a definition whose type `sigOf` refuses. -/
theorem sig_refused (spec : Name) (ds : List Export.Decl) :
    specSig spec ds = .error .cannotCarry ↔ SigRefused spec ds := by
  unfold specSig SigRefused
  cases hd : ds.find? (fun x => x.name == spec) with
  | none => simp
  | some d =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases hk : d.kind = .defn
    · simp only [hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, true_and]
      cases Protocol.sigOf d.type <;> simp
    · have : (d.kind != .defn) = true := by simpa [bne_iff_ne] using hk
      simp [this, hk]

end FvdepAudit.Oracle.Resolve.Proof
