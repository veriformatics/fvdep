import FvdepAudit.Registry.Proof.Forms

/-! `decode` (+ `spine`, its list loop) = the spec relation `Denotes`: completeness by induction on
the relation, soundness by the walk's own induction principle. -/

namespace FvdepAudit.Registry.Proof

open Lean FvdepCore.Index.Registry FvdepAudit.Registry.Spec

/-- A cons chain's elements, reversed (the spine's accumulator order). -/
def revElems : Val → List Val
  | .cons x xs => revElems xs ++ [x]
  | _ => []

/-- A `nil`-terminated cons chain. -/
inductive IsList : Val → Prop
  | nil : IsList .nil
  | cons {x xs : Val} : IsList xs → IsList (.cons x xs)

theorem ofRev_append (xs ys : List Val) (t : Val) :
    Val.ofRev (xs ++ ys) t = Val.ofRev ys (Val.ofRev xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simp [Val.ofRev, ih]

theorem ofRev_rev {v : Val} (h : IsList v) : Val.ofRev (revElems v) .nil = v := by
  induction h with
  | nil => rfl
  | cons _ ih => simp [revElems, ofRev_append, Val.ofRev, ih]

theorem revElems_vappend (a b : Val) : revElems (vappend a b) = revElems b ++ revElems a := by
  induction a with
  | cons h t _ iht => simp [vappend, revElems, iht]
  | _ => simp [vappend, revElems]

theorem isList_vappend {a b : Val} (ha : IsList a) (hb : IsList b) : IsList (vappend a b) := by
  induction ha with
  | nil => exact hb
  | cons _ ih => exact .cons ih

theorem decode_of_spine {F : Facts} {fe : Form} {e : Expr} {env : List Expr} {p : List Name}
    {v : Val} (hl : IsList v) (hs : ∀ acc, spine F fe e env p acc = .ok (revElems v ++ acc)) :
    decode F (.list fe) e env p = .ok v := by
  rw [decode, hs []]
  simp [ofRev_rev hl]

theorem owns_false {F : Facts} {p : List Name} {f : Form} {c : Name} (h : ¬Owns F p f c) :
    ownsConst F p f c = false := by
  cases h' : ownsConst F p f c
  · rfl
  · exact absurd ((ownsConst_iff F p f c).mp h') h

/-- `Denotes` → `decode` (+ the spine's accumulator law). -/
theorem complete {F : Facts} {f : Form} {e : Expr} {env : List Expr} {p : List Name} {v : Val}
    (h : Denotes F f e env p v) :
    (∀ fe, f = .list fe → IsList v) ∧
      (∀ fe, f = .list fe → ∀ acc, spine F fe e env p acc = .ok (revElems v ++ acc)) ∧
      decode F f e env p = .ok v := by
  induction h with
  | any => exact ⟨by simp, by simp, by rw [decode.eq_def]⟩
  | @mdata f m e env p v hf _ ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    have hs :
      ∀ fe, f = .list fe → ∀ acc, spine F fe (.mdata m e) env p acc = .ok (revElems v ++ acc) :=
      fun fe hfe acc => by
      rw [spine]; exact hB fe hfe acc
    refine ⟨hA, hs, ?_⟩
    cases f with
    | list fe => exact decode_of_spine (hA _ rfl) (hs _ rfl)
    | any => exact absurd rfl hf
    | _ =>
      rw [decode.eq_def]; exact hC
  | @letE f n t x b nd env p v hf _ ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    have hs :
      ∀ fe,
        f = .list fe → ∀ acc, spine F fe (.letE n t x b nd) env p acc = .ok (revElems v ++ acc) :=
      fun fe hfe acc => by
      rw [spine]; exact hB fe hfe acc
    refine ⟨hA, hs, ?_⟩
    cases f with
    | list fe => exact decode_of_spine (hA _ rfl) (hs _ rfl)
    | any => exact absurd rfl hf
    | _ =>
      rw [decode.eq_def]; exact hC
  | @bvar f i env p x v hf hx _ ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    have hs :
      ∀ fe, f = .list fe → ∀ acc, spine F fe (.bvar i) env p acc = .ok (revElems v ++ acc) :=
      fun fe hfe acc => by
      rw [spine]
      split
      · rename_i y hy
        rw [hx] at hy
        cases hy
        exact hB fe hfe acc
      · rename_i hy
        rw [hx] at hy
        cases hy
    refine ⟨hA, hs, ?_⟩
    cases f with
    | list fe => exact decode_of_spine (hA _ rfl) (hs _ rfl)
    | any => exact absurd rfl hf
    | _ =>
      rw [decode.eq_def]
      dsimp only
      split
      · rename_i y hy
        rw [hx] at hy
        cases hy
        exact hC
      · rename_i hy
        rw [hx] at hy
        cases hy
  | @root f c us env p x v hf hown hroot _
    ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    have hr := (rootDef_iff F p c x).mpr hroot
    have ho := owns_false hown
    have hs :
      ∀ fe, f = .list fe → ∀ acc, spine F fe (.const c us) env p acc = .ok (revElems v ++ acc) :=
      fun fe hfe acc => by
      rw [spine]
      split
      · rename_i y hy
        rw [hr] at hy
        cases hy
        exact hB fe hfe acc
      · rename_i hy
        rw [hr] at hy
        cases hy
    refine ⟨hA, hs, ?_⟩
    cases f with
    | list fe => exact decode_of_spine (hA _ rfl) (hs _ rfl)
    | any => exact absurd rfl hf
    | _ =>
      rw [decode.eq_def]
      dsimp only
      simp only [ho, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i y hy
        rw [hr] at hy
        cases hy
        exact hC
      · rename_i hy
        rw [hr] at hy
        cases hy
  | str => exact ⟨by simp, by simp, by rw [decode.eq_def]⟩
  | anonymous =>
    exact
      ⟨by simp, by simp, by
        rw [decode.eq_def]; simp [ownsConst]⟩
  | name hn =>
    refine ⟨by simp, by simp, ?_⟩
    rw [decode.eq_def]
    dsimp only
    rw [nameLit_complete hn]
  | enum hc =>
    exact
      ⟨by simp, by simp, by
        rw [decode.eq_def]; simp [ownsConst, hc]⟩
  | ctor =>
    exact
      ⟨by simp, by simp, by
        rw [decode.eq_def]; simp [ownsConst]⟩
  | app _ _ ih₁ ih₂ =>
    refine ⟨by simp, by simp, ?_⟩
    rw [decode.eq_def]
    simp only [ih₁.2.2, ih₂.2.2]
  | none =>
    exact
      ⟨by simp, by simp, by
        rw [decode.eq_def]; rfl⟩
  | some _ ih =>
    refine ⟨by simp, by simp, ?_⟩
    rw [decode.eq_def]
    simp only [ih.2.2]
  | @entry f c m us env p x v hent _
    ih =>
    refine ⟨by simp, by simp, ?_⟩
    have he := (entryDef_iff F p c m x).mpr hent
    have ho : ownsConst F p (.entry f) c = true := by simp [ownsConst, he]
    rw [decode.eq_def]
    dsimp only
    simp only [ho, ↓reduceIte]
    split
    · rename_i m' y hy
      rw [he] at hy
      cases hy
      simp only [ih.2.2]
    · rename_i hy
      rw [he] at hy
      cases hy
  | @nil f us T env
    p =>
    have hB :
      ∀ acc, spine F f (.app (.const ``List.nil us) T) env p acc = .ok (revElems .nil ++ acc) :=
      fun acc => by
      rw [spine]; rfl
    exact
      ⟨fun _ _ => .nil, fun fe hf acc => by
        cases hf; exact hB acc, decode_of_spine .nil hB⟩
  | @cons f us T h t env p x xs _ _ ihh
    iht =>
    obtain ⟨hA, hB, _⟩ := iht
    have hl : IsList (.cons x xs) := .cons (hA _ rfl)
    have hs :
      ∀ acc,
        spine F f (.app (.app (.app (.const ``List.cons us) T) h) t) env p acc =
          .ok (revElems (.cons x xs) ++ acc) :=
      fun acc => by
      rw [spine]
      simp only [ihh.2.2]
      rw [hB _ rfl]
      simp [revElems]
    exact
      ⟨fun _ _ => hl, fun fe hf acc => by
        cases hf; exact hs acc, decode_of_spine hl hs⟩
  | @append f us A B C i xs ys env p a b hstd _ _ iha
    ihb =>
    obtain ⟨hAa, hBa, _⟩ := iha
    obtain ⟨hAb, hBb, _⟩ := ihb
    have hl : IsList (vappend a b) := isList_vappend (hAa _ rfl) (hAb _ rfl)
    have hi : stdAppend i = true := (stdAppend_iff i).mpr hstd
    have hs :
      ∀ acc,
        spine F f
            (.app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend us) A) B) C) i) xs) ys)
            env p acc =
          .ok (revElems (vappend a b) ++ acc) :=
      fun acc => by
      rw [spine]
      simp only [hi, ↓reduceIte]
      rw [hBa _ rfl acc]
      dsimp only
      rw [hBb _ rfl, revElems_vappend, List.append_assoc]
    exact
      ⟨fun _ _ => hl, fun fe hf acc => by
        cases hf; exact hs acc, decode_of_spine hl hs⟩

/-- `decode` → `Denotes` (+ the spine's accumulator law), by the walk's induction principle. -/
theorem sound (F : Facts) :
    (∀ f e env p, ∀ v, decode F f e env p = .ok v → Denotes F f e env p v) ∧
      (∀ fe e env p acc,
        ∀ out,
          spine F fe e env p acc = .ok out →
            ∃ w, Denotes F (.list fe) e env p w ∧ out = revElems w ++ acc) := by
  refine
    decode.mutual_induct F (motive1 := fun f e env p =>
      ∀ v, decode F f e env p = .ok v → Denotes F f e env p v) (motive2 := fun fe e env p acc =>
      ∀ out,
        spine F fe e env p acc = .ok out →
          ∃ w, Denotes F (.list fe) e env p w ∧ out = revElems w ++ acc)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- 1 any
  · intro e env p v h
    rw [decode.eq_def] at h
    cases h
    exact .any
  -- 2 list ok
  · intro e env p fe acc hs ih v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [hs] at h
    cases h
    obtain ⟨w, hw, hacc⟩ := ih acc hs
    subst hacc
    rw [List.append_nil, ofRev_rev ((complete hw).1 fe rfl)]
    exact hw
  -- 3 list error
  · intro e env p fe n hs _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [hs] at h
    cases h
  -- 4 mdata
  · intro f env p data e hany hlist ih v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · exact .mdata hany (ih v h)
  -- 5 letE
  · intro f env p n t x b nd hany hlist ih v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · exact .letE hany (ih v h)
  -- 6 bvar some
  · intro f env p i x hx _ hany hlist ih v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · dsimp only at h
      split at h
      · rename_i y hy
        rw [hx] at hy
        cases hy
        exact .bvar hany hx (ih v h)
      · rename_i hy
        rw [hx] at hy
        cases hy
  -- 7 bvar none
  · intro f env p i hx hany hlist v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · dsimp only at h
      split at h
      · rename_i y hy
        rw [hx] at hy
        cases hy
      · cases h
  -- 8 lit str
  · intro env p s _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    cases h
    exact .str
  -- 9 lit other
  · intro f env p l hany hlist hns v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · dsimp only at h
      split at h
      · exact (hns _ rfl rfl).elim
      · cases h
  -- 10 entry ok
  · intro env p c us fe m x hent _ y hy hown _ _ ih v h
    rw [decode.eq_def] at h
    dsimp only at h
    simp only [hown, ↓reduceIte] at h
    split at h
    · rename_i m' x' hx'
      rw [hent] at hx'
      cases hx'
      rw [hy] at h
      cases h
      exact .entry ((entryDef_iff F p c m x).mp hent) (ih y hy)
    · rename_i hx'
      rw [hent] at hx'
      cases hx'
  -- 11 entry error
  · intro env p c us fe m x hent _ n hy hown _ _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    simp only [hown, ↓reduceIte] at h
    split at h
    · rename_i m' x' hx'
      rw [hent] at hx'
      cases hx'
      rw [hy] at h
      cases h
    · cases h
  -- 12 entry none
  · intro env p c us fe hent hown _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    simp only [hown, ↓reduceIte] at h
    split at h
    · rename_i m' x' hx'
      rw [hent] at hx'
      cases hx'
    · cases h
  -- 13 name: Name.anonymous
  · intro env p c us hown _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    simp only [hown, ↓reduceIte] at h
    cases h
    have hc : c = ``Name.anonymous := by simpa [ownsConst] using hown
    subst hc
    exact .anonymous
  -- 14 enum / ctor
  · intro f env p c us hown hany hlist hentry hname v h
    cases f with
    | enum cs =>
      rw [decode.eq_def] at h
      dsimp only at h
      simp only [hown, ↓reduceIte] at h
      cases h
      exact .enum (by simpa [ownsConst] using hown)
    | ctor c' =>
      rw [decode.eq_def] at h
      dsimp only at h
      simp only [hown, ↓reduceIte] at h
      cases h
      have hc : c = c' := by simpa [ownsConst] using hown
      subst hc
      exact .ctor
    | entry fe => exact (hentry _ rfl).elim
    | name => exact (hname rfl).elim
    | any => exact absurd rfl hany
    | list fe => exact (hlist _ rfl).elim
    | _ => simp [ownsConst] at hown
  -- 15 root some
  · intro f env p c us hown x hr _ hany hlist ih v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · dsimp only at h
      have ho : ownsConst F p f c = false := by simpa using hown
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i y hy
        rw [hr] at hy
        cases hy
        refine .root hany ?_ ((rootDef_iff F p c x).mp hr) (ih v h)
        intro hown'
        exact absurd ((ownsConst_iff F p f c).mpr hown') hown
      · rename_i hy
        rw [hr] at hy
        cases hy
  -- 16 root none
  · intro f env p c us hown hr hany hlist v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · dsimp only at h
      have ho : ownsConst F p f c = false := by simpa using hown
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i y hy
        rw [hr] at hy
        cases hy
      · cases h
  -- 17 name literal
  · intro env p e₁ e₂ n hn _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [hn] at h
    cases h
    exact .name (nameLit_sound _ _ hn)
  -- 18 name, not a literal
  · intro env p e₁ e₂ hn _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [hn] at h
    cases h
  -- 19 Option.none
  · intro env p e₂ fo us _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    cases h
    exact .none
  -- 20 Option.some ok
  · intro env p e₂ fo us T x hx _ _ ih v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [hx] at h
    cases h
    exact .some (ih x hx)
  -- 21 Option.some error
  · intro env p e₂ fo us T n hx _ _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [hx] at h
    cases h
  -- 22 opt, other head
  · intro env p e₁ e₂ fo hnone hsome _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    split at h
    · exact (hnone _ rfl).elim
    · exact (hsome _ _ rfl).elim
    · cases h
  -- 23 app ok ok
  · intro env p e₁ e₂ ff fa x₁ h₁ x₂ h₂ _ _ ih₁ ih₂ v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [h₁] at h
    dsimp only at h
    rw [h₂] at h
    cases h
    exact .app (ih₁ x₁ h₁) (ih₂ x₂ h₂)
  -- 24 app ok error
  · intro env p e₁ e₂ ff fa x₁ h₁ n h₂ _ _ _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [h₁] at h
    dsimp only at h
    rw [h₂] at h
    cases h
  -- 25 app error
  · intro env p e₁ e₂ ff fa n h₁ _ _ _ v h
    rw [decode.eq_def] at h
    dsimp only at h
    rw [h₁] at h
    cases h
  -- 26 app, other form
  · intro f env p e₁ e₂ hany hlist hname hopt happ v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · dsimp only at h
      split at h
      · exact (hname rfl).elim
      · exact (hopt _ rfl).elim
      · exact (happ _ _ rfl).elim
      · cases h
  -- 27 other expression
  · intro f e env p hany hlist h1 h2 h3 h4 h5 h6 v h
    rw [decode.eq_def] at h
    split at h
    · exact absurd rfl hany
    · exact (hlist _ rfl).elim
    · split at h <;>
        first
        | exact (h1 _ _ rfl).elim
        | exact (h2 _ _ _ _ _ rfl).elim
        | exact (h3 _ rfl).elim
        | exact (h4 _ rfl).elim
        | exact (h5 _ _ rfl).elim
        | exact (h6 _ _ rfl).elim
        | cases h
  -- 28 spine mdata
  · intro fe env p acc data e ih out h
    rw [spine] at h
    obtain ⟨w, hw, rfl⟩ := ih out h
    exact ⟨w, .mdata (by simp) hw, rfl⟩
  -- 29 spine letE
  · intro fe env p acc n t x b nd ih out h
    rw [spine] at h
    obtain ⟨w, hw, rfl⟩ := ih out h
    exact ⟨w, .letE (by simp) hw, rfl⟩
  -- 30 spine bvar some
  · intro fe env p acc i x hx _ ih out h
    rw [spine] at h
    split at h
    · rename_i y hy
      rw [hx] at hy
      cases hy
      obtain ⟨w, hw, rfl⟩ := ih out h
      exact ⟨w, .bvar (by simp) hx hw, rfl⟩
    · rename_i hy
      rw [hx] at hy
      cases hy
  -- 31 spine bvar none
  · intro fe env p acc i hx out h
    rw [spine] at h
    split at h
    · rename_i y hy
      rw [hx] at hy
      cases hy
    · cases h
  -- 32 spine nil
  · intro fe env p acc us T out h
    rw [spine] at h
    cases h
    exact ⟨.nil, .nil, rfl⟩
  -- 33 spine cons ok
  · intro fe env p acc us T hd t x hx ihh iht out h
    rw [spine] at h
    rw [hx] at h
    dsimp only at h
    obtain ⟨w, hw, rfl⟩ := iht out h
    exact ⟨.cons x w, .cons (ihh x hx) hw, by simp [revElems]⟩
  -- 34 spine cons error
  · intro fe env p acc us T hd t n hx _ out h
    rw [spine] at h
    rw [hx] at h
    cases h
  -- 35 spine append ok
  · intro fe env p acc us A B C i xs ys hi acc' hxs ihx ihy out h
    rw [spine] at h
    simp only [hi, ↓reduceIte] at h
    rw [hxs] at h
    dsimp only at h
    obtain ⟨a, ha, rfl⟩ := ihx acc' hxs
    obtain ⟨b, hb, rfl⟩ := ihy out h
    refine ⟨vappend a b, .append ((stdAppend_iff i).mp hi) ha hb, ?_⟩
    rw [revElems_vappend, List.append_assoc]
  -- 36 spine append error
  · intro fe env p acc us A B C i xs ys hi n hxs _ out h
    rw [spine] at h
    simp only [hi, ↓reduceIte] at h
    rw [hxs] at h
    cases h
  -- 37 spine append, other instance
  · intro fe env p acc us A B C i xs ys hi out h
    rw [spine] at h
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  -- 38 spine root some
  · intro fe env p acc c us x hr _ ih out h
    rw [spine] at h
    split at h
    · rename_i y hy
      rw [hr] at hy
      cases hy
      obtain ⟨w, hw, rfl⟩ := ih out h
      exact ⟨w, .root (by simp) (by simp [Owns]) ((rootDef_iff F p c x).mp hr) hw, rfl⟩
    · rename_i hy
      rw [hr] at hy
      cases hy
  -- 39 spine root none
  · intro fe env p acc c us hr out h
    rw [spine] at h
    split at h
    · rename_i y hy
      rw [hr] at hy
      cases hy
    · cases h
  -- 40 spine other
  · intro fe e env p acc h1 h2 h3 h4 h5 h6 h7 out h
    rw [spine.eq_def] at h
    split at h <;>
      first
      | exact (h1 _ _ rfl).elim
      | exact (h2 _ _ _ _ _ rfl).elim
      | exact (h3 _ rfl).elim
      | exact (h4 _ _ rfl).elim
      | exact (h5 _ _ _ _ rfl).elim
      | exact (h6 _ _ _ _ _ _ _ rfl).elim
      | exact (h7 _ _ rfl).elim
      | cases h

/-- C8 `RegistryDecodeExact`: the walk accepts exactly what the spec relation relates. -/
theorem decode_exact (F : Facts) (f : Form) (e : Expr) (env : List Expr) (p : List Name) (v : Val) :
    decode F f e env p = .ok v ↔ Denotes F f e env p v :=
  ⟨(sound F).1 f e env p v, fun h => (complete h).2.2⟩

end FvdepAudit.Registry.Proof
