import FvdepAudit.Index.Rules.Spec

/-! The helpers the checks decide with, against the relations written apart: the printed-name
order + `least`, `constsOnto` (`Mentions`), alpha-equivalence (`erase` + `erasedEq`), the flags. -/

namespace FvdepAudit.Index.Rules.Proof

open Lean FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepAudit.Index.Rules.Spec

/-! ## Order -/

theorem lexLt_irrefl : ∀ a : List Char, lexLt a a = false
  | [] => rfl
  | x :: xs => by simp [lexLt, lexLt_irrefl xs]

theorem lexLt_trans : ∀ {a b c : List Char}, lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], _ :: _, _ :: _, _, _ => rfl
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr ⟨by omega, lexLt_trans h₁ h₂⟩

/-- The fold `least` runs: the kept name has no strictly smaller name among those it saw. -/
theorem least_fold (xs : List Name) (m : Name) (seen : List Name)
    (hm : ∀ y ∈ seen, lexLt (key y) (key m) = false) (hs : m ∈ seen) :
    let r := xs.foldl (fun m y => if lexLt (key y) (key m) then y else m) m
    r ∈ seen ++ xs ∧ ∀ y ∈ seen ++ xs, lexLt (key y) (key r) = false := by
  induction xs generalizing m seen with
  | nil => simpa using ⟨hs, hm⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hx : lexLt (key x) (key m) = true
    · simp only [hx, ↓reduceIte]
      have :=
        ih x (seen ++ [x])
          (fun y hy => by
            rcases List.mem_append.mp hy with hy | hy
            · cases hyx : lexLt (key y) (key x)
              · rfl
              · have := hm y hy
                rw [lexLt_trans hyx hx] at this
                exact absurd this (by simp)
            · simp only [List.mem_singleton] at hy
              subst hy
              exact lexLt_irrefl _)
          (by simp)
      simpa [List.append_assoc] using this
    · simp only [Bool.not_eq_true] at hx
      simp only [hx, Bool.false_eq_true, ↓reduceIte]
      have :=
        ih m (seen ++ [x])
          (fun y hy => by
            rcases List.mem_append.mp hy with hy | hy
            · exact hm y hy
            · simp only [List.mem_singleton] at hy
              subst hy
              exact hx)
          (by simp [hs])
      simpa [List.append_assoc] using this

theorem least_none (xs : List Name) : least xs = none ↔ xs = [] := by cases xs <;> simp [least]

theorem least_some {xs : List Name} {c : Name} (h : least xs = some c) :
    c ∈ xs ∧ ∀ y ∈ xs, lexLt (key y) (key c) = false := by
  cases xs with
  | nil => simp [least] at h
  | cons x xs =>
    simp only [least, Option.some.injEq] at h
    subst h
    have := least_fold xs x [x] (by simp [lexLt_irrefl]) (by simp)
    simpa using this

/-- `least` over exactly the carriers of `P`: `none` ↔ no carrier; else a least carrier. -/
theorem least_carriers {xs : List Name} {P : Name → Prop} (h : ∀ c, c ∈ xs ↔ P c) :
    (least xs = none ↔ ∀ c, ¬P c) ∧ ∀ c, least xs = some c → IsLeast P c := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [least_none]
    constructor
    · intro e c hc
      rw [← h c, e] at hc
      simp at hc
    · intro hn
      cases xs with
      | nil => rfl
      | cons x _ => exact absurd ((h x).mp (by simp)) (hn x)
  · obtain ⟨hm, hl⟩ := least_some hc
    exact ⟨(h c).mp hm, fun c' hc' => hl c' ((h c').mpr hc')⟩

/-! ## Constants a value names -/

theorem mem_constsOnto (e : Expr) (acc : List Name) (n : Name) :
    n ∈ constsOnto e acc ↔ Mentions e n ∨ n ∈ acc := by
  induction e generalizing acc with
  | const c _ => simp [constsOnto, Mentions, eq_comm]
  | app f a ihf iha => simp [constsOnto, Mentions, ihf, iha, or_assoc]
  | lam _ t b _ iht ihb => simp [constsOnto, Mentions, iht, ihb, or_assoc]
  | forallE _ t b _ iht ihb => simp [constsOnto, Mentions, iht, ihb, or_assoc]
  | letE _ t v b _ iht ihv ihb => simp [constsOnto, Mentions, iht, ihv, ihb, or_assoc]
  | mdata _ e ih => simp [constsOnto, Mentions, ih]
  | proj _ _ e ih => simp [constsOnto, Mentions, ih]
  | bvar => simp [constsOnto, Mentions]
  | fvar => simp [constsOnto, Mentions]
  | mvar => simp [constsOnto, Mentions]
  | sort => simp [constsOnto, Mentions]
  | lit => simp [constsOnto, Mentions]

theorem mem_bodyConsts (d : Decl) (n : Name) :
    n ∈ bodyConsts d ↔ ∃ v, d.kind = .defn ∧ d.value = some v ∧ Mentions v n := by
  rcases d with ⟨_, _, kind, value, _, _, _, _, _⟩
  cases kind <;> cases value <;> simp [bodyConsts, mem_constsOnto]

/-! ## Flags -/

theorem hasFlag_iff (F : Facts) (d : Decl) (fl : Flag) :
    hasFlag F d fl = true ↔ HasFlag F d fl := by
  cases fl
  case implementedBy =>
    simp [hasFlag, HasFlag, LeanForm, leanForm, Option.any_eq_true, Decidable.imp_iff_not_or]
  all_goals simp [hasFlag, HasFlag, LeanForm, leanForm, Option.any_eq_true]

/-! ## Alpha-equivalence -/

/-- The image of `erase`: no metadata, binder names anonymous, binder annotations default. -/
def Erased : Expr → Prop
  | .app f a => Erased f ∧ Erased a
  | .lam n t b i => n = .anonymous ∧ i = .default ∧ Erased t ∧ Erased b
  | .forallE n t b i => n = .anonymous ∧ i = .default ∧ Erased t ∧ Erased b
  | .letE n t v b nd => n = .anonymous ∧ nd = false ∧ Erased t ∧ Erased v ∧ Erased b
  | .mdata _ _ => False
  | .proj _ _ e => Erased e
  | _ => True

theorem erased_erase (e : Expr) : Erased (erase e) := by induction e <;> simp_all [erase, Erased]

theorem levelEq_iff : ∀ a b : Level, levelEq a b = true ↔ a = b
  | .zero, b => by cases b <;> simp [levelEq]
  | .succ a, b => by cases b <;> simp [levelEq, levelEq_iff a]
  | .max a a', b => by cases b <;> simp [levelEq, levelEq_iff a, levelEq_iff a']
  | .imax a a', b => by cases b <;> simp [levelEq, levelEq_iff a, levelEq_iff a']
  | .param a, b => by cases b <;> simp [levelEq]
  | .mvar a, b => by
    cases b with
    | mvar b =>
      cases a
      cases b
      simp [levelEq]
    | _ => simp [levelEq]

theorem levelsEq_iff : ∀ a b : List Level, levelsEq a b = true ↔ a = b
  | [], b => by cases b <;> simp [levelsEq]
  | x :: xs, b => by cases b <;> simp [levelsEq, levelEq_iff, levelsEq_iff xs]

theorem litEq_iff (a b : Literal) : litEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [litEq]

theorem erasedEq_iff : ∀ x y : Expr, Erased x → Erased y → (erasedEq x y = true ↔ x = y)
  | .bvar i, y, _, _ => by cases y <;> simp [erasedEq]
  | .fvar a, y, _, _ => by
    cases y with
    | fvar b =>
      cases a
      cases b
      simp [erasedEq]
    | _ => simp [erasedEq]
  | .mvar a, y, _, _ => by
    cases y with
    | mvar b =>
      cases a
      cases b
      simp [erasedEq]
    | _ => simp [erasedEq]
  | .sort u, y, _, _ => by cases y <;> simp [erasedEq, levelEq_iff]
  | .const c us, y, _, _ => by cases y <;> simp [erasedEq, levelsEq_iff]
  | .app f a, y, hx, hy => by
    cases y with
    | app g b =>
      simp only [Erased] at hx hy
      simp [erasedEq, erasedEq_iff f g hx.1 hy.1, erasedEq_iff a b hx.2 hy.2]
    | _ => simp [erasedEq]
  | .lam n t b i, y, hx, hy => by
    cases y with
    | lam n' t' b' i' =>
      simp only [Erased] at hx hy
      obtain ⟨rfl, rfl, ht, hb⟩ := hx
      obtain ⟨rfl, rfl, ht', hb'⟩ := hy
      simp [erasedEq, erasedEq_iff t t' ht ht', erasedEq_iff b b' hb hb']
    | _ => simp [erasedEq]
  | .forallE n t b i, y, hx, hy => by
    cases y with
    | forallE n' t' b' i' =>
      simp only [Erased] at hx hy
      obtain ⟨rfl, rfl, ht, hb⟩ := hx
      obtain ⟨rfl, rfl, ht', hb'⟩ := hy
      simp [erasedEq, erasedEq_iff t t' ht ht', erasedEq_iff b b' hb hb']
    | _ => simp [erasedEq]
  | .letE n t v b nd, y, hx, hy => by
    cases y with
    | letE n' t' v' b' nd' =>
      simp only [Erased] at hx hy
      obtain ⟨rfl, rfl, ht, hv, hb⟩ := hx
      obtain ⟨rfl, rfl, ht', hv', hb'⟩ := hy
      simp [erasedEq, erasedEq_iff t t' ht ht', erasedEq_iff v v' hv hv', erasedEq_iff b b' hb hb',
        and_assoc]
    | _ => simp [erasedEq]
  | .lit l, y, _, _ => by cases y <;> simp [erasedEq, litEq_iff]
  | .mdata _ _, _, hx, _ => by simp [Erased] at hx
  | .proj s i e, y, hx, hy => by
    cases y with
    | proj s' i' e' =>
      simp only [Erased] at hx hy
      simp [erasedEq, erasedEq_iff e e' hx hy, and_assoc]
    | _ => simp [erasedEq]

theorem alphaEq_iff (a b : Expr) : alphaEq a b = true ↔ erase a = erase b :=
  erasedEq_iff _ _ (erased_erase a) (erased_erase b)

end FvdepAudit.Index.Rules.Proof
