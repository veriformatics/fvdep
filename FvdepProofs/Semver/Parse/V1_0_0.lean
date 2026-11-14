import Fvdep.Semver.Parse.V1_0_0

/-! Obligations of `Fvdep.Semver.Parse.V1_0_0`: `parse s = some v ↔ Valid v ∧ render v = s`
(`onlyValid` + `canonical` from `parse_spec`, `complete`). -/

namespace FvdepProofs.Semver.Parse.V1_0_0

open Fvdep.Semver.Version.V1_0_0 Fvdep.Semver.Parse.V1_0_0

/-! ## Characters -/

theorem isDigit_toNat {c : Char} (h : c.isDigit = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨UInt32.le_iff_toNat_le.mp h.1, UInt32.le_iff_toNat_le.mp h.2⟩

theorem digit_spec :
    ∀ d,
      d < 10 → (digit d).toNat = 48 + d ∧ (digit d).isDigit = true ∧ (digit d = '0' ↔ d = 0) := by
  decide

theorem digit_of_isDigit {c : Char} (h : c.isDigit = true) : digit (c.toNat - 48) = c := by
  have := isDigit_toNat h
  unfold digit
  rw [show 48 + (c.toNat - 48) = c.toNat by omega, Char.ofNat_toNat]

theorem identChar_of_isDigit {c : Char} (h : c.isDigit = true) : identChar c = true := by
  simp [identChar, h]

theorem dot_not_identChar : identChar '.' = false := by decide

theorem plus_not_identChar : identChar '+' = false := by decide

theorem dash_isDigit : Char.isDigit '-' = false := by decide

theorem dot_isDigit : Char.isDigit '.' = false := by decide

theorem plus_isDigit : Char.isDigit '+' = false := by decide

/-! ## Numbers -/

/-- `numeric`'s accumulator step. -/
def step (n : Nat) (c : Char) : Nat := 10 * n + (c.toNat - 48)

theorem foldl_step_ge (cs : List Char) (a : Nat) : a ≤ cs.foldl step a := by
  induction cs generalizing a with
  | nil => exact Nat.le_refl a
  | cons c cs ih =>
    simp only [List.foldl]
    exact
      Nat.le_trans
        (by
          unfold step; omega)
        (ih _)

theorem decimal_eq (n : Nat) :
    decimal n = if n < 10 then [digit n] else decimal (n / 10) ++ [digit (n % 10)] := by
  rw [decimal]

theorem decimal_facts (n : Nat) :
    decimal n ≠ [] ∧
      (∀ c ∈ decimal n, c.isDigit = true) ∧
      (decimal n).foldl step 0 = n ∧ (n ≠ 0 → (decimal n).head? ≠ some '0') := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decimal_eq]
    by_cases hn : n < 10
    · obtain ⟨ht, hd, hz⟩ := digit_spec n hn
      simp only [hn, ↓reduceIte]
      refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton.mp hc]
        exact hd
      · simp only [List.foldl, step, ht]
        omega
      · intro h0 hh
        exact h0 (hz.mp (Option.some.inj hh))
    · obtain ⟨hne, hdig, hval, hhead⟩ := ih (n / 10) (by omega)
      obtain ⟨ht, hd, -⟩ := digit_spec (n % 10) (Nat.mod_lt _ (by decide))
      simp only [hn, ↓reduceIte]
      refine ⟨by simp, ?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hdig c hc
        · rw [List.mem_singleton.mp hc]
          exact hd
      · rw [List.foldl_append, hval]
        simp only [List.foldl, step, ht]
        omega
      · intro _
        cases h : decimal (n / 10) with
        | nil => exact absurd h hne
        | cons c cs =>
          have hc := hhead (by omega)
          rw [h] at hc
          simpa using hc

/-- A digit string whose first digit is no `0` (unless it is `0` itself) is the decimal spelling of
its value; stated over the reversed string (induction peels the last digit). -/
theorem decimal_foldl_rev :
    ∀ rs : List Char,
      rs ≠ [] →
        (∀ c ∈ rs, c.isDigit = true) →
        ¬(rs.reverse.head? = some '0' ∧ rs.length > 1) →
        decimal (rs.reverse.foldl step 0) = rs.reverse
  | [], h, _, _ => absurd rfl h
  | [d], _, hd, _ => by
    have hdd := hd d (List.mem_singleton_self d)
    have := isDigit_toNat hdd
    simp only [List.reverse_singleton, List.foldl, step, Nat.mul_zero, Nat.zero_add]
    rw [decimal_eq]
    simp only [show d.toNat - 48 < 10 by omega, ↓reduceIte, digit_of_isDigit hdd]
  | d :: e :: rs', _, hd, hh => by
    have hdd := hd d (List.mem_cons_self ..)
    have hdb := isDigit_toNat hdd
    have hsub : ∀ c ∈ e :: rs', c.isDigit = true := fun c hc => hd c (List.mem_cons_of_mem _ hc)
    have hrev : (d :: e :: rs').reverse = (e :: rs').reverse ++ [d] := List.reverse_cons ..
    cases hi : (e :: rs').reverse with
    | nil => simp at hi
    | cons h0
      rest =>
      have hh0 : h0 ≠ '0' := by
        intro e0
        apply hh
        rw [hrev, hi, e0]
        exact ⟨rfl, by simp⟩
      have hih :=
        decimal_foldl_rev (e :: rs') (List.cons_ne_nil _ _) hsub
          (by
            rw [hi]
            intro ⟨h1, _⟩
            exact hh0 (Option.some.inj h1))
      rw [hi] at hih
      have hh0d : h0.isDigit = true :=
        hsub h0
          (by
            rw [← List.mem_reverse, hi]; exact List.mem_cons_self ..)
      have hb0 := isDigit_toNat hh0d
      have h1 : 1 ≤ h0.toNat - 48 := by
        have : h0.toNat ≠ 48 := fun e =>
          hh0
            (Char.toNat_inj.mp
              (by
                rw [e]; rfl))
        omega
      have hv : 1 ≤ (h0 :: rest).foldl step 0 := by
        simp only [List.foldl]
        exact
          Nat.le_trans
            (by
              unfold step; omega)
            (foldl_step_ge rest _)
      rw [hrev, hi, List.foldl_append]
      generalize hw : (h0 :: rest).foldl step 0 = w at hih hv ⊢
      simp only [List.foldl_cons, List.foldl_nil, step]
      rw [decimal_eq]
      simp only [show ¬(10 * w + (d.toNat - 48) < 10) by omega, ↓reduceIte]
      rw [show (10 * w + (d.toNat - 48)) / 10 = w by omega,
        show (10 * w + (d.toNat - 48)) % 10 = d.toNat - 48 by omega, hih, digit_of_isDigit hdd]

theorem decimal_of_canonical {cs : List Char} (hne : cs ≠ []) (hd : ∀ c ∈ cs, c.isDigit = true)
    (hz : ¬(cs.head? = some '0' ∧ cs.length > 1)) : decimal (cs.foldl step 0) = cs := by
  have := decimal_foldl_rev cs.reverse (by simpa using hne) (by simpa using hd) (by simpa using hz)
  simpa using this

theorem numeric_eq (cs : List Char) :
    numeric cs =
      if cs.isEmpty || !cs.all Char.isDigit || (cs.head? == some '0' && cs.length > 1) then none
      else some (cs.foldl step 0) := rfl

theorem numeric_decimal (n : Nat) : numeric (decimal n) = some n := by
  obtain ⟨hne, hd, hv, hh⟩ := decimal_facts n
  rw [numeric_eq]
  have h1 : (decimal n).isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  have h2 : (decimal n).all Char.isDigit = true := List.all_eq_true.mpr hd
  have h3 : ((decimal n).head? == some '0' && decide ((decimal n).length > 1)) = false := by
    by_cases h0 : n = 0
    · subst h0
      rw [decimal_eq]
      decide
    · have := hh h0
      simp [this]
  simp [h1, h2, h3, hv]

theorem numeric_spec {cs : List Char} {n : Nat} (h : numeric cs = some n) :
    decimal n = cs ∧ ∀ c ∈ cs, c.isDigit = true := by
  rw [numeric_eq] at h
  split at h
  · cases h
  · rename_i hc
    cases h
    have hne : cs ≠ [] := fun e => hc (by simp [e])
    have hall : cs.all Char.isDigit = true := by
      cases ha : cs.all Char.isDigit
      · exact absurd (by simp [ha]) hc
      · rfl
    have hz : ¬(cs.head? = some '0' ∧ cs.length > 1) := fun ⟨a, b⟩ => hc (by simp [a, b])
    have hd := List.all_eq_true.mp hall
    exact ⟨decimal_of_canonical hne hd hz, hd⟩

/-! ## Identifiers -/

theorem preIdent_num (n : Nat) : preIdent (decimal n) = some (.num n) := by
  obtain ⟨hne, hd, -, -⟩ := decimal_facts n
  have hi : (decimal n).all identChar = true :=
    List.all_eq_true.mpr fun c hc => identChar_of_isDigit (hd c hc)
  have hdg : (decimal n).all Char.isDigit = true := List.all_eq_true.mpr hd
  simp [preIdent, List.isEmpty_eq_false_iff.mpr hne, hi, hdg, numeric_decimal]

theorem preIdent_alnum {s : List Char} (h1 : s ≠ []) (h2 : ∀ c ∈ s, identChar c = true)
    (h3 : ∃ c ∈ s, c.isDigit = false) : preIdent s = some (.alnum s) := by
  have hi : s.all identChar = true := List.all_eq_true.mpr h2
  have hdg : s.all Char.isDigit = false := by
    obtain ⟨c, hc, hcd⟩ := h3
    cases h : s.all Char.isDigit
    · rfl
    · have := List.all_eq_true.mp h c hc
      simp [hcd] at this
  simp [preIdent, List.isEmpty_eq_false_iff.mpr h1, hi, hdg]

theorem preIdent_spec {cs : List Char} {i : Ident} (h : preIdent cs = some i) :
    renderIdent i = cs ∧
      ∀ s, i = .alnum s → s ≠ [] ∧ (∀ c ∈ s, identChar c = true) ∧ ∃ c ∈ s, c.isDigit = false := by
  unfold preIdent at h
  split at h
  · cases h
  · rename_i hc
    have hne : cs ≠ [] := fun e => hc (by simp [e])
    have hall : cs.all identChar = true := by
      cases ha : cs.all identChar
      · exact absurd (by simp [ha]) hc
      · rfl
    split at h
    · rename_i hdig
      cases hn : numeric cs with
      | none => simp [hn] at h
      | some n =>
        simp only [hn, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨(numeric_spec hn).1, fun _ e => by cases e⟩
    · rename_i hdig
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, fun s e => ?_⟩
      cases e
      refine ⟨hne, List.all_eq_true.mp hall, ?_⟩
      refine Classical.byContradiction fun hno => hdig ?_
      exact
        List.all_eq_true.mpr fun c hc => by
          cases hcd : c.isDigit
          · exact absurd ⟨c, hc, hcd⟩ hno
          · rfl

theorem buildIdent_valid {b : List Char} (h1 : b ≠ []) (h2 : ∀ c ∈ b, identChar c = true) :
    buildIdent b = some b := by
  simp [buildIdent, List.isEmpty_eq_false_iff.mpr h1, List.all_eq_true.mpr h2]

theorem buildIdent_spec {cs b : List Char} (h : buildIdent cs = some b) :
    b = cs ∧ b ≠ [] ∧ ∀ c ∈ b, identChar c = true := by
  unfold buildIdent at h
  split at h
  · cases h
  · rename_i hc
    have hne : cs ≠ [] := fun e => hc (by simp [e])
    have hall : cs.all identChar = true := by
      cases ha : cs.all identChar
      · exact absurd (by simp [ha]) hc
      · rfl
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, hne, List.all_eq_true.mp hall⟩

/-! ## Splitting + joining -/

theorem splitFirst_of_not_mem {sep : Char} :
    ∀ {s : List Char}, sep ∉ s → splitFirst sep s = (s, none)
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : sep ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitFirst, hc, splitFirst_of_not_mem hcs]

theorem splitFirst_append {sep : Char} {b : List Char} :
    ∀ {a : List Char}, sep ∉ a → splitFirst sep (a ++ sep :: b) = (a, some b)
  | [], _ => by simp [splitFirst]
  | c :: cs, h => by
    have hc : c ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : sep ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitFirst, hc, splitFirst_append hcs]

theorem splitFirst_none {sep : Char} :
    ∀ {s a : List Char}, splitFirst sep s = (a, none) → s = a ∧ sep ∉ a
  | [], a, h => by
    simp only [splitFirst, Prod.mk.injEq] at h
    exact
      ⟨h.1, by
        rw [← h.1]; simp⟩
  | c :: cs, a, h => by
    simp only [splitFirst] at h
    split at h
    · simp at h
    · rename_i hc
      cases hr : splitFirst sep cs with
      | mk a' o =>
        simp only [hr, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := splitFirst_none hr
        subst h1
        exact ⟨rfl, by simp [Ne.symm hc, h2]⟩

theorem splitFirst_some {sep : Char} :
    ∀ {s a b : List Char}, splitFirst sep s = (a, some b) → s = a ++ sep :: b ∧ sep ∉ a
  | [], a, b, h => by simp [splitFirst] at h
  | c :: cs, a, b, h => by
    simp only [splitFirst] at h
    split at h
    · rename_i hc
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact
        ⟨by
          rw [hc]; rfl, List.not_mem_nil⟩
    · rename_i hc
      cases hr : splitFirst sep cs with
      | mk a' o =>
        simp only [hr, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := splitFirst_some hr
        subst h1
        exact ⟨rfl, by simp [Ne.symm hc, h2]⟩

theorem splitOn_ne_nil (sep : Char) : ∀ s, splitOn sep s ≠ []
  | [] => by simp [splitOn]
  | c :: cs => by
    simp only [splitOn]
    split
    · simp
    · cases splitOn sep cs <;> simp

theorem splitOn_of_not_mem {sep : Char} : ∀ {w : List Char}, sep ∉ w → splitOn sep w = [w]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : sep ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hc, splitOn_of_not_mem hcs]

theorem splitOn_append_sep {sep : Char} {rest : List Char} :
    ∀ {w : List Char}, sep ∉ w → splitOn sep (w ++ sep :: rest) = w :: splitOn sep rest
  | [], _ => by simp [splitOn]
  | c :: cs, h => by
    have hc : c ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : sep ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hc, splitOn_append_sep hcs]

theorem splitOn_joinDot :
    ∀ {ws : List (List Char)}, ws ≠ [] → (∀ w ∈ ws, '.' ∉ w) → splitOn '.' (joinDot ws) = ws
  | [], h, _ => absurd rfl h
  | [w], _, hw => splitOn_of_not_mem (hw w (List.mem_singleton_self w))
  | w :: v :: ws, _, hw => by
    simp only [joinDot]
    rw [splitOn_append_sep (hw w (List.mem_cons_self ..)),
      splitOn_joinDot (List.cons_ne_nil _ _) (fun u hu => hw u (List.mem_cons_of_mem _ hu))]

theorem joinDot_cons_cons (c : Char) (w : List Char) (ws : List (List Char)) :
    joinDot ((c :: w) :: ws) = c :: joinDot (w :: ws) := by cases ws <;> rfl

theorem joinDot_splitOn : ∀ s : List Char, joinDot (splitOn '.' s) = s
  | [] => rfl
  | c :: cs => by
    have ih := joinDot_splitOn cs
    simp only [splitOn]
    split
    · rename_i hc
      subst hc
      cases h : splitOn '.' cs with
      | nil => exact absurd h (splitOn_ne_nil _ cs)
      | cons v ws =>
        rw [h] at ih
        simp only [joinDot, List.nil_append, ih]
    · cases h : splitOn '.' cs with
      | nil => exact absurd h (splitOn_ne_nil _ cs)
      | cons w ws =>
        rw [h] at ih
        simp only [joinDot_cons_cons, ih]

theorem mem_joinDot {c : Char} :
    ∀ {ws : List (List Char)}, c ∈ joinDot ws → c = '.' ∨ ∃ w ∈ ws, c ∈ w
  | [], h => by simp [joinDot] at h
  | [w], h => .inr ⟨w, List.mem_singleton_self w, h⟩
  | w :: v :: ws, h => by
    simp only [joinDot, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact .inr ⟨w, List.mem_cons_self .., h⟩
    · exact .inl h
    · rcases mem_joinDot h with h | ⟨u, hu, hcu⟩
      · exact .inl h
      · exact .inr ⟨u, List.mem_cons_of_mem _ hu, hcu⟩

/-! ## mapM -/

theorem mapM_preIdent :
    ∀ {ws : List (List Char)} {is : List Ident},
      ws.mapM preIdent = some is →
        is.map renderIdent = ws ∧
          ∀ i ∈ is,
            ∀ s, i = .alnum s → s ≠ [] ∧ (∀ c ∈ s, identChar c = true) ∧ ∃ c ∈ s, c.isDigit = false
  | [], is, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | w :: ws, is, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨i, hi, is', his, rfl⟩ := h
    obtain ⟨h1, h2⟩ := preIdent_spec hi
    obtain ⟨h3, h4⟩ := mapM_preIdent his
    refine ⟨by simp [h1, h3], ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h2
    · exact h4 j hj

theorem mapM_buildIdent :
    ∀ {ws bs : List (List Char)},
      ws.mapM buildIdent = some bs → bs = ws ∧ ∀ b ∈ bs, b ≠ [] ∧ ∀ c ∈ b, identChar c = true
  | [], bs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | w :: ws, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs, rfl⟩ := h
    obtain ⟨rfl, h2, h3⟩ := buildIdent_spec hb
    obtain ⟨rfl, h4⟩ := mapM_buildIdent hbs
    refine ⟨rfl, ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨h2, h3⟩
    · exact h4 u hu

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, -, ys', hys, rfl⟩ := h
    simp [mapM_length hys]

theorem mapM_render {α : Type} {f : List Char → Option α} {g : α → List Char} :
    ∀ {xs : List α}, (∀ x ∈ xs, f (g x) = some x) → (xs.map g).mapM f = some xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, List.mapM_cons, h x (List.mem_cons_self ..),
      mapM_render (fun y hy => h y (List.mem_cons_of_mem _ hy)), Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

theorem mapM_self {f : List Char → Option (List Char)} :
    ∀ {xs : List (List Char)}, (∀ x ∈ xs, f x = some x) → xs.mapM f = some xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x (List.mem_cons_self ..),
      mapM_self (fun y hy => h y (List.mem_cons_of_mem _ hy)), Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

/-! ## The obligations -/

theorem render_eq (v : Version) :
    render v =
      joinDot [decimal v.major, decimal v.minor, decimal v.patch] ++
        ((if v.pre.isEmpty then [] else '-' :: joinDot (v.pre.map renderIdent)) ++
          if v.build.isEmpty then [] else '+' :: joinDot v.build) := by
  simp [render, joinDot, List.append_assoc]

theorem parse_spec {s : List Char} {v : Version} (h : parse s = some v) :
    Valid v ∧ render v = s := by
  rcases h1 : splitFirst '+' s with ⟨main, build?⟩
  rcases h2 : splitFirst '-' main with ⟨core, pre?⟩
  rcases h3 : splitOn '.' core with _ | ⟨ma, _ | ⟨mi, _ | ⟨pa, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp only [parse, h1, h2, h3, reduceCtorEq] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨major, hM, minor, hm, patch, hp, h⟩ := h
  obtain ⟨pre, build, hpre, hb, rfl⟩ :
    ∃ pre build,
      (pre? = none ∧ pre = [] ∨ ∃ p, pre? = some p ∧ (splitOn '.' p).mapM preIdent = some pre) ∧
        (build? = none ∧ build = [] ∨
          ∃ b, build? = some b ∧ (splitOn '.' b).mapM buildIdent = some build) ∧
        v = ⟨major, minor, patch, pre, build⟩ :=
    by
    cases pre? with
    | none =>
      cases build? with
      | none =>
        simp only [Option.bind_some, Option.some.injEq] at h
        exact ⟨[], [], .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, h.symm⟩
      | some b =>
        simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨build, hb, hv⟩ := h
        exact ⟨[], build, .inl ⟨rfl, rfl⟩, .inr ⟨b, rfl, hb⟩, hv.symm⟩
    | some p =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨pre, hpre, h⟩ := h
      cases build? with
      | none =>
        simp only [Option.bind_some, Option.some.injEq] at h
        exact ⟨pre, [], .inr ⟨p, rfl, hpre⟩, .inl ⟨rfl, rfl⟩, h.symm⟩
      | some b =>
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨build, hb, hv⟩ := h
        exact ⟨pre, build, .inr ⟨p, rfl, hpre⟩, .inr ⟨b, rfl, hb⟩, hv.symm⟩
  have hcore : core = joinDot [decimal major, decimal minor, decimal patch] := by
    rw [(numeric_spec hM).1, (numeric_spec hm).1, (numeric_spec hp).1, ← h3, joinDot_splitOn]
  -- the pre-release part
  have hP :
    ∃ P : List Char,
      main = core ++ P ∧
        P = (if pre.isEmpty then [] else '-' :: joinDot (pre.map renderIdent)) ∧
        ∀ i ∈ pre,
          ∀ s,
            i = .alnum s → s ≠ [] ∧ (∀ c ∈ s, identChar c = true) ∧ ∃ c ∈ s, c.isDigit = false := by
    rcases hpre with ⟨rfl, rfl⟩ | ⟨p, rfl, hpre⟩
    · exact ⟨[], by simpa using (splitFirst_none h2).1, rfl, by simp⟩
    · obtain ⟨hmap, hval⟩ := mapM_preIdent hpre
      have hne : pre ≠ [] := by
        intro e
        subst e
        exact splitOn_ne_nil '.' p (List.length_eq_zero_iff.mp (mapM_length hpre).symm)
      refine ⟨'-' :: p, (splitFirst_some h2).1, ?_, hval⟩
      simp [List.isEmpty_eq_false_iff.mpr hne, hmap, joinDot_splitOn]
  -- the build part
  have hB :
    ∃ B : List Char,
      s = main ++ B ∧
        B = (if build.isEmpty then [] else '+' :: joinDot build) ∧
        ∀ b ∈ build, b ≠ [] ∧ ∀ c ∈ b, identChar c = true := by
    rcases hb with ⟨rfl, rfl⟩ | ⟨b, rfl, hb⟩
    · exact ⟨[], by simpa using (splitFirst_none h1).1, rfl, by simp⟩
    · obtain ⟨rfl, hval⟩ := mapM_buildIdent hb
      have hne : splitOn '.' b ≠ [] := splitOn_ne_nil '.' b
      refine ⟨'+' :: b, (splitFirst_some h1).1, ?_, hval⟩
      simp [List.isEmpty_eq_false_iff.mpr hne, joinDot_splitOn]
  obtain ⟨P, hmain, hPe, hpv⟩ := hP
  obtain ⟨B, hs, hBe, hbv⟩ := hB
  refine ⟨⟨fun i hi => ?_, hbv⟩, ?_⟩
  · cases i with
    | num _ => trivial
    | alnum s => exact hpv _ hi s rfl
  · rw [render_eq, hs, hmain, hcore, hPe, hBe, List.append_assoc]

theorem onlyValid : Fvdep.Semver.Parse.V1_0_0.onlyValid := fun _ _ h => (parse_spec h).1

theorem canonical : Fvdep.Semver.Parse.V1_0_0.canonical := fun _ _ h => (parse_spec h).2

theorem decimal_no {c : Char} (hc : c.isDigit = false) (n : Nat) : c ∉ decimal n := by
  intro h
  have := (decimal_facts n).2.1 c h
  rw [hc] at this
  cases this

/-- `parse` of a string whose `+` split, `-` split + core split are known. -/
theorem parse_assemble {s main C : List Char} {preQ buildQ : Option (List Char)}
    {major minor patch : Nat} {pre : List Ident} {build : List (List Char)}
    (hplus : splitFirst '+' s = (main, buildQ)) (hdash : splitFirst '-' main = (C, preQ))
    (hcore : splitOn '.' C = [decimal major, decimal minor, decimal patch])
    (hpre : preQ = none ∧ pre = [] ∨ ∃ p, preQ = some p ∧ (splitOn '.' p).mapM preIdent = some pre)
    (hbuild :
      buildQ = none ∧ build = [] ∨
        ∃ b, buildQ = some b ∧ (splitOn '.' b).mapM buildIdent = some build) :
    parse s = some ⟨major, minor, patch, pre, build⟩ := by
  unfold parse
  simp only [hplus, hdash, hcore, numeric_decimal, Option.bind_eq_bind, Option.bind_some]
  rcases hpre with ⟨rfl, rfl⟩ | ⟨p, rfl, hp⟩
  · rcases hbuild with ⟨rfl, rfl⟩ | ⟨b, rfl, hb⟩
    · rfl
    · simp [hb]
  · rcases hbuild with ⟨rfl, rfl⟩ | ⟨b, rfl, hb⟩
    · simp [hp]
    · simp [hp, hb]

theorem complete : Fvdep.Semver.Parse.V1_0_0.complete := by
  intro v hv
  obtain ⟨hpre, hbuild⟩ := hv
  cases v with
  | mk major minor patch pre
    build =>
    have hIdent :
      ∀ i ∈ pre, preIdent (renderIdent i) = some i ∧ '.' ∉ renderIdent i ∧ '+' ∉ renderIdent i := by
      intro i hi
      have hv := hpre i hi
      cases i with
      | num n => exact ⟨preIdent_num n, decimal_no dot_isDigit n, decimal_no plus_isDigit n⟩
      | alnum s =>
        obtain ⟨h1, h2, h3⟩ := hv
        refine ⟨preIdent_alnum h1 h2 h3, fun h => ?_, fun h => ?_⟩
        · have := h2 _ h
          rw [dot_not_identChar] at this
          cases this
        · have := h2 _ h
          rw [plus_not_identChar] at this
          cases this
    have hBuild : ∀ b ∈ build, buildIdent b = some b ∧ '.' ∉ b ∧ '+' ∉ b := by
      intro b hb
      obtain ⟨h1, h2⟩ := hbuild b hb
      refine ⟨buildIdent_valid h1 h2, fun h => ?_, fun h => ?_⟩
      · have := h2 _ h
        rw [dot_not_identChar] at this
        cases this
      · have := h2 _ h
        rw [plus_not_identChar] at this
        cases this
    have hcoreSplit :
      splitOn '.' (joinDot [decimal major, decimal minor, decimal patch]) =
        [decimal major, decimal minor, decimal patch] :=
      splitOn_joinDot (List.cons_ne_nil _ _) (by simp [decimal_no dot_isDigit])
    have hcoreNo :
      ∀ c,
        c.isDigit = false →
          c ≠ '.' → c ∉ joinDot [decimal major, decimal minor, decimal patch] := by
      intro c hc hdot h
      rcases mem_joinDot h with h | ⟨w, hw, hcw⟩
      · exact hdot h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> exact decimal_no hc _ hcw
    have hcoreDash := hcoreNo '-' dash_isDigit (by decide)
    have hcorePlus := hcoreNo '+' plus_isDigit (by decide)
    have hPreM :
      pre ≠ [] → (splitOn '.' (joinDot (pre.map renderIdent))).mapM preIdent = some pre :=
      fun hne => by
      rw [splitOn_joinDot (by simpa using hne)
          (by
            intro w hw
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
            exact (hIdent i hi).2.1)]
      exact mapM_render fun i hi => (hIdent i hi).1
    have hBuildM : build ≠ [] → (splitOn '.' (joinDot build)).mapM buildIdent = some build :=
      fun hne => by
      rw [splitOn_joinDot hne fun w hw => (hBuild w hw).2.1]
      exact mapM_self fun b hb => (hBuild b hb).1
    have hCJplus :
      '+' ∉
        joinDot [decimal major, decimal minor, decimal patch] ++
          '-' :: joinDot (pre.map renderIdent) := by
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨hcorePlus, by decide, fun h => ?_⟩
      rcases mem_joinDot h with h | ⟨w, hw, hcw⟩
      · cases h
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact (hIdent i hi).2.2 hcw
    rw [render_eq]
    by_cases hp : pre = []
    · subst hp
      by_cases hb : build = []
      · subst hb
        exact
          parse_assemble (main := joinDot [decimal major, decimal minor, decimal patch]) (buildQ :=
            none) (preQ := none) (by simpa using splitFirst_of_not_mem hcorePlus)
            (splitFirst_of_not_mem hcoreDash) hcoreSplit (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩)
      · exact
          parse_assemble (main := joinDot [decimal major, decimal minor, decimal patch]) (buildQ :=
            some (joinDot build)) (preQ := none)
            (by simpa [hb] using splitFirst_append (b := joinDot build) hcorePlus)
            (splitFirst_of_not_mem hcoreDash) hcoreSplit (.inl ⟨rfl, rfl⟩)
            (.inr ⟨_, rfl, hBuildM hb⟩)
    · by_cases hb : build = []
      · subst hb
        exact
          parse_assemble (main :=
            joinDot [decimal major, decimal minor, decimal patch] ++
              '-' :: joinDot (pre.map renderIdent))
            (buildQ := none) (preQ := some (joinDot (pre.map renderIdent)))
            (by simpa [hp] using splitFirst_of_not_mem hCJplus) (splitFirst_append hcoreDash)
            hcoreSplit (.inr ⟨_, rfl, hPreM hp⟩) (.inl ⟨rfl, rfl⟩)
      · exact
          parse_assemble (main :=
            joinDot [decimal major, decimal minor, decimal patch] ++
              '-' :: joinDot (pre.map renderIdent))
            (buildQ := some (joinDot build)) (preQ := some (joinDot (pre.map renderIdent)))
            (by simpa [hp, hb] using splitFirst_append (b := joinDot build) hCJplus)
            (splitFirst_append hcoreDash) hcoreSplit (.inr ⟨_, rfl, hPreM hp⟩)
            (.inr ⟨_, rfl, hBuildM hb⟩)

end FvdepProofs.Semver.Parse.V1_0_0
