import FvdepAudit.Registry.Spec

/-! The walk's leaf readers = the spec's literal relations: string + name literals, application
spines, definition lookups, the standard `++` instance, the forms' own constants. -/

namespace FvdepAudit.Registry.Proof

open Lean FvdepCore.Index.Registry FvdepAudit.Registry.Spec

theorem strLit_sound {e : Expr} {s : String} (h : strLit? e = some s) : StrLit e s := by
  induction e with
  | mdata m e ih => exact .mdata (ih h)
  | lit l =>
    cases l with
    | strVal t =>
      simp only [strLit?, Option.some.injEq] at h
      subst h
      exact .lit
    | natVal => simp [strLit?] at h
  | _ => simp [strLit?] at h

theorem strLit_complete {e : Expr} {s : String} (h : StrLit e s) : strLit? e = some s := by
  induction h with
  | lit => rfl
  | mdata _ ih => simpa [strLit?] using ih

theorem strLit_iff (e : Expr) (s : String) : strLit? e = some s ↔ StrLit e s :=
  ⟨strLit_sound, strLit_complete⟩

theorem strLits_iff :
    ∀ (es : List Expr) (ss : List String), es.mapM strLit? = some ss ↔ StrLits es ss
  | [], ss => by
    cases ss with
    | nil => simp [StrLits.nil]
    | cons s
      ss =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq, reduceCtorEq, false_iff]
      intro h
      cases h
  | e :: es, ss => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
    constructor
    · intro h
      cases hs : strLit? e with
      | none => simp [hs] at h
      | some s =>
        cases hr : es.mapM strLit? with
        | none => simp [hs, hr] at h
        | some rest =>
          simp only [hs, hr, Option.bind_some, Option.some.injEq] at h
          subst h
          exact .cons (strLit_sound hs) ((strLits_iff es rest).mp hr)
    · intro h
      cases h with
      | cons he hes =>
        rw [strLit_complete he, (strLits_iff es _).mpr hes]
        rfl

theorem headArgs_sound :
    ∀ {e : Expr} {acc : List Expr} {c : Name} {args : List Expr},
      headArgs? e acc = some (c, args) → ∃ pre, AppOf c e pre ∧ args = pre ++ acc
  | .mdata _ e, acc, c, args, h => by
    obtain ⟨pre, hp, rfl⟩ := headArgs_sound (e := e) h
    exact ⟨pre, .mdata hp, rfl⟩
  | .app f a, acc, c, args, h => by
    obtain ⟨pre, hp, rfl⟩ := headArgs_sound (e := f) h
    exact ⟨pre ++ [a], .app hp, by simp⟩
  | .const c' _, acc, c, args, h => by
    simp only [headArgs?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], .const, rfl⟩
  | .bvar _, _, _, _, h => by simp [headArgs?] at h
  | .fvar _, _, _, _, h => by simp [headArgs?] at h
  | .mvar _, _, _, _, h => by simp [headArgs?] at h
  | .sort _, _, _, _, h => by simp [headArgs?] at h
  | .lam .., _, _, _, h => by simp [headArgs?] at h
  | .forallE .., _, _, _, h => by simp [headArgs?] at h
  | .letE .., _, _, _, h => by simp [headArgs?] at h
  | .lit _, _, _, _, h => by simp [headArgs?] at h
  | .proj .., _, _, _, h => by simp [headArgs?] at h

theorem headArgs_complete {c : Name} {e : Expr} {pre : List Expr} (h : AppOf c e pre) :
    ∀ acc, headArgs? e acc = some (c, pre ++ acc) := by
  induction h with
  | const =>
    intro acc; rfl
  | app _ ih =>
    intro acc
    simp only [headArgs?, ih, List.append_assoc, List.singleton_append]
  | mdata _ ih =>
    intro acc; simpa [headArgs?] using ih acc

theorem mkStrN_eq : mkStrN = mkStrNames := rfl

theorem mkStrs_sound {e : Expr} {n : Name} (h : mkStrs? e = some n) :
    ∃ k c args ts,
      mkStrNames[k]? = some c ∧
        AppOf c e args ∧
        args.length = k + 1 ∧ StrLits args ts ∧ n = ts.foldl Name.str .anonymous := by
  unfold mkStrs? at h
  split at h
  · rename_i c a as hh
    split at h
    · rename_i hc
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨pre, hp, hpre⟩ := headArgs_sound hh
      simp only [List.append_nil] at hpre
      subst hpre
      refine ⟨as.length, c, a :: as, ts, ?_, hp, by simp, (strLits_iff _ _).mp hts, rfl⟩
      rw [← mkStrN_eq]
      simpa using hc
    · cases h
  · cases h

theorem mkStrs_complete {k : Nat} {c : Name} {e : Expr} {args : List Expr} {ts : List String}
    (hk : mkStrNames[k]? = some c) (ha : AppOf c e args) (hl : args.length = k + 1)
    (hs : StrLits args ts) : mkStrs? e = some (ts.foldl Name.str .anonymous) := by
  have hh := headArgs_complete ha []
  simp only [List.append_nil] at hh
  cases args with
  | nil => simp at hl
  | cons a as =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    subst hl
    unfold mkStrs?
    rw [hh]
    simp only [mkStrN_eq, hk, beq_self_eq_true, ↓reduceIte]
    rw [(strLits_iff _ _).mpr hs]
    rfl

/-- No `Name.mkStrN` head is `Name.str` or `Name.mkStr`. -/
theorem mkStrs_not_str {k : Nat} {c : Name} (hk : mkStrNames[k]? = some c) :
    (c == ``Name.str || c == ``Name.mkStr) = false := by
  match k, hk with
  | 0, hk | 1, hk | 2, hk | 3, hk | 4, hk | 5, hk | 6, hk | 7,
    hk =>
    simp only [mkStrNames, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hk
    subst hk
    decide
  | k + 8, hk => simp [mkStrNames] at hk

theorem nameLit_sound (e : Expr) (n : Name) (h : nameLit? e = some n) : NameLit e n := by
  unfold nameLit? at h
  split at h
  · rename_i e'
    exact .mdata (nameLit_sound e' n h)
  · rename_i c us
    split at h
    · rename_i hc
      cases h
      simp only [beq_iff_eq] at hc
      subst hc
      exact .anonymous
    · cases h
  · rename_i c us p s
    split at h
    · rename_i hc
      split at h
      · rename_i t ht
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        have hc' : c = ``Name.str ∨ c = ``Name.mkStr := by simpa using hc
        exact .str hc' (nameLit_sound p m hm) (strLit_sound ht)
      · cases h
    · obtain ⟨k, c', args, ts, hk, ha, hl, hs, rfl⟩ := mkStrs_sound h
      exact .mkStrs hk ha hl hs
  · obtain ⟨k, c', args, ts, hk, ha, hl, hs, rfl⟩ := mkStrs_sound h
    exact .mkStrs hk ha hl hs
termination_by sizeOf e

/-- A `Name.mkStrN` application: `nameLit?` takes its `mkStrs?` arm. -/
theorem nameLit_mkStrs {k : Nat} {c : Name} {e : Expr} {args : List Expr}
    (hk : mkStrNames[k]? = some c) (ha : AppOf c e args) (hl : args.length = k + 1) :
    nameLit? e = mkStrs? e ∨ ∃ m e', e = .mdata m e' ∧ AppOf c e' args := by
  cases ha with
  | const => simp at hl
  | mdata ha' => exact .inr ⟨_, _, rfl, ha'⟩
  | @app f a pre hf =>
    left
    cases hf with
    | const =>
      unfold nameLit?; rfl
    | mdata _ =>
      unfold nameLit?; rfl
    | @app g b pre' hg =>
      cases hg with
      | @const us =>
        have hn := mkStrs_not_str hk
        unfold nameLit?
        simp only [hn, Bool.false_eq_true, ↓reduceIte]
      | mdata _ =>
        unfold nameLit?; rfl
      | app _ =>
        unfold nameLit?; rfl

theorem nameLit_complete {e : Expr} {n : Name} (h : NameLit e n) : nameLit? e = some n := by
  induction h with
  | mdata _ ih => simpa [nameLit?] using ih
  | anonymous => simp [nameLit?]
  | @str c us p s n t hc _ hs
    ih =>
    have hc' : (c == ``Name.str || c == ``Name.mkStr) = true := by
      rcases hc with rfl | rfl <;> decide
    unfold nameLit?
    simp only [hc', ↓reduceIte, strLit_complete hs, ih, Option.map_some]
  | @mkStrs k c e args ts hk ha hl
    hs =>
    have hm := mkStrs_complete hk ha hl hs
    induction e generalizing args with
    | mdata m e' ih' =>
      cases ha with
      | mdata ha' =>
        unfold nameLit?
        exact ih' ha' hl hs hm
    | _ =>
      rcases nameLit_mkStrs hk ha hl with h | ⟨m, e', he, _⟩
      · rw [h, hm]
      · cases he

theorem nameLit_iff (e : Expr) (n : Name) : nameLit? e = some n ↔ NameLit e n :=
  ⟨nameLit_sound e n, nameLit_complete⟩

theorem valueOf_iff (F : Facts) (p : List Name) (c : Name) (ok : Decl → Bool) (x : Expr) :
    valueOf? F p c ok = some x ↔
      c ∉ p ∧
        ∃ d,
          F.decls.find? (·.name == c) = some d ∧
            d.kind = .defn ∧ ok d = true ∧ d.value = some x := by
  unfold valueOf?
  by_cases hp : c ∈ p
  · simp [hp]
  · simp only [hp, ↓reduceIte, not_false_eq_true, true_and]
    cases hd : F.decls.find? (·.name == c) with
    | none => simp
    | some d =>
      simp only [Option.some.injEq, exists_eq_left']
      by_cases hk : d.kind = .defn
      · by_cases ho : ok d = true
        · simp [hk, ho]
        · simp [hk, ho]
      · simp [hk]

theorem rootDef_iff (F : Facts) (p : List Name) (c : Name) (x : Expr) :
    rootDef? F p c = some x ↔ RootDef F p c x := by
  unfold rootDef? RootDef
  rw [valueOf_iff]
  simp [rootModule]

theorem entryDef_iff (F : Facts) (p : List Name) (c m : Name) (x : Expr) :
    entryDef? F p c = some (m, x) ↔ EntryDef F p c m x := by
  unfold entryDef? EntryDef
  split
  · rename_i m'
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, valueOf_iff, beq_iff_eq]
    constructor
    · rintro ⟨y, ⟨hp, d, hd, hk, hm, hv⟩, rfl, rfl⟩
      exact ⟨rfl, hp, d, hd, hk, hm, hv⟩
    · rintro ⟨hc, hp, d, hd, hk, hm, hv⟩
      cases hc
      exact ⟨x, ⟨hp, d, hd, hk, hm, hv⟩, rfl, rfl⟩
  · rename_i hc
    simp only [reduceCtorEq, false_iff, not_and]
    intro he
    exact absurd he (hc m)

theorem ownsConst_iff (F : Facts) (p : List Name) (f : Form) (c : Name) :
    ownsConst F p f c = true ↔ Owns F p f c := by
  cases f with
  | name => simp [ownsConst, Owns]
  | enum cs => simp [ownsConst, Owns]
  | ctor c' => simp [ownsConst, Owns]
  | entry f =>
    simp only [ownsConst, Owns, Option.isSome_iff_exists]
    constructor
    · rintro ⟨⟨m, x⟩, h⟩
      exact ⟨m, x, (entryDef_iff F p c m x).mp h⟩
    · rintro ⟨m, x, h⟩
      exact ⟨(m, x), (entryDef_iff F p c m x).mpr h⟩
  | _ => simp [ownsConst, Owns]

theorem stdAppend_iff (i : Expr) : stdAppend i = true ↔ StdAppend i := by
  constructor
  · intro h
    unfold stdAppend at h
    split at h
    · rename_i u₁ A u₂ T
      exact ⟨u₁, u₂, A, T, rfl⟩
    · cases h
  · rintro ⟨u₁, u₂, A, T, rfl⟩
    rfl

end FvdepAudit.Registry.Proof
