import FvdepAudit.Judge.Proof.Raw
import FvdepAudit.Judge.Spec

/-! Proofs: one comparison step (contract `docs/contracts/U7-judge.md` X7) — on two exports' raw
records, `heads` decides each pair the way its meaning (`PairEq`) does: `none` = unequal, `some
kids` = equal exactly when every kid is, each kid ranked below the pair (a record names only
earlier records). -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepCore.Index.Rules FvdepAudit.Export.Spec
  FvdepAudit.Judge.Spec

/-! ## U4's equalities, one head at a time -/

theorem alphaEq_bvar (a b : Nat) : alphaEq (.bvar a) (.bvar b) = (a == b) := rfl

theorem alphaEq_sort (u v : Lean.Level) : alphaEq (.sort u) (.sort v) = levelEq u v := rfl

theorem alphaEq_const (c d : Lean.Name) (us vs : List Lean.Level) :
    alphaEq (.const c us) (.const d vs) = (c == d && levelsEq us vs) := rfl

theorem alphaEq_app (f a g b : Lean.Expr) :
    alphaEq (.app f a) (.app g b) = (alphaEq f g && alphaEq a b) := rfl

theorem alphaEq_lam (n n' : Lean.Name) (t b t' b' : Lean.Expr) (bi bi' : Lean.BinderInfo) :
    alphaEq (.lam n t b bi) (.lam n' t' b' bi') = (alphaEq t t' && alphaEq b b') := rfl

theorem alphaEq_forallE (n n' : Lean.Name) (t b t' b' : Lean.Expr) (bi bi' : Lean.BinderInfo) :
    alphaEq (.forallE n t b bi) (.forallE n' t' b' bi') = (alphaEq t t' && alphaEq b b') := rfl

theorem alphaEq_letE (n n' : Lean.Name) (t v b t' v' b' : Lean.Expr) (nd nd' : Bool) :
    alphaEq (.letE n t v b nd) (.letE n' t' v' b' nd') =
      (alphaEq t t' && alphaEq v v' && alphaEq b b') := rfl

theorem alphaEq_proj (s s' : Lean.Name) (i i' : Nat) (e e' : Lean.Expr) :
    alphaEq (.proj s i e) (.proj s' i' e') = (s == s' && i == i' && alphaEq e e') := rfl

theorem alphaEq_natVal (a b : Nat) : alphaEq (.lit (.natVal a)) (.lit (.natVal b)) = (a == b) := rfl

theorem alphaEq_strVal (a b : String) : alphaEq (.lit (.strVal a)) (.lit (.strVal b)) = (a == b) :=
  rfl

theorem levelEq_succ (a b : Lean.Level) : levelEq (.succ a) (.succ b) = levelEq a b := rfl

theorem levelEq_max (a b c d : Lean.Level) :
    levelEq (.max a b) (.max c d) = (levelEq a c && levelEq b d) := rfl

theorem levelEq_imax (a b c d : Lean.Level) :
    levelEq (.imax a b) (.imax c d) = (levelEq a c && levelEq b d) := rfl

theorem levelEq_param (a b : Lean.Name) : levelEq (.param a) (.param b) = (a == b) := rfl

/-! ## Heads by tag: different heads never compare equal -/

def ftag : ExprF → Nat
  | .bvar _ => 0
  | .sort _ => 1
  | .const _ _ => 2
  | .app _ _ => 3
  | .lam _ _ _ _ => 4
  | .forallE _ _ _ _ => 5
  | .letE _ _ _ _ _ => 6
  | .proj _ _ _ => 7
  | .natVal _ => 8
  | .strVal _ => 9

def litTag : Lean.Literal → Nat
  | .natVal _ => 8
  | .strVal _ => 9

def etag : Lean.Expr → Nat
  | .bvar _ => 0
  | .fvar _ => 10
  | .mvar _ => 10
  | .sort _ => 1
  | .const _ _ => 2
  | .app _ _ => 3
  | .lam _ _ _ _ => 4
  | .forallE _ _ _ _ => 5
  | .letE _ _ _ _ _ => 6
  | .lit l => litTag l
  | .mdata _ _ => 10
  | .proj _ _ _ => 7

theorem etag_denotes {N : Array Lean.Name} {L : Array Lean.Level} {X : Array Lean.Expr} {f : ExprF}
    {e : Lean.Expr} (h : ExprDenotes N L X f e) : etag e = ftag f := by
  cases f with
  | bvar k =>
    cases h
    rfl
  | sort l =>
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | const n us =>
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  | app f a =>
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  | lam n ty b bi =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    rfl
  | forallE n ty b bi =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    rfl
  | letE n ty v b nd =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h
    rfl
  | proj tn idx s =>
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  | natVal v =>
    cases h
    rfl
  | strVal s =>
    cases h
    rfl

theorem alphaEq_tag {a b : Lean.Expr} (h : etag a ≠ etag b) (ha : etag a < 10) (hb : etag b < 10) :
    alphaEq a b = false := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ | _ <;>
    rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ | _ <;>
    simp only [etag, litTag] at h ha hb <;>
    first
    | omega
    | rfl

theorem exprHeads_tag {f g : ExprF} (h : ftag f ≠ ftag g) : exprHeads f g = none := by
  cases f <;> cases g <;> simp only [ftag] at h <;>
    first
    | omega
    | rfl

def ltag : Option LevelF → Nat
  | none => 0
  | some (.succ _) => 1
  | some (.max _ _) => 2
  | some (.imax _ _) => 3
  | some (.param _) => 4

def lvtag : Lean.Level → Nat
  | .zero => 0
  | .succ _ => 1
  | .max _ _ => 2
  | .imax _ _ => 3
  | .param _ => 4
  | .mvar _ => 5

theorem levelEq_tag {a b : Lean.Level} (h : lvtag a ≠ lvtag b) (ha : lvtag a < 5)
    (hb : lvtag b < 5) : levelEq a b = false := by
  cases a <;> cases b <;> simp only [lvtag] at h ha hb <;>
    first
    | omega
    | rfl

theorem levelHeads_tag {a b : Option LevelF} (h : ltag a ≠ ltag b) : levelHeads a b = none := by
  rcases a with _ | (_ | _ | _ | _) <;> rcases b with _ | (_ | _ | _ | _) <;>
    simp only [ltag] at h <;>
    first
    | omega
    | rfl

def ntag : Option NameF → Nat
  | none => 0
  | some (.str _ _) => 1
  | some (.num _ _) => 2

def nmtag : Lean.Name → Nat
  | .anonymous => 0
  | .str _ _ => 1
  | .num _ _ => 2

theorem nameHeads_tag {a b : Option NameF} (h : ntag a ≠ ntag b) : nameHeads a b = none := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> simp only [ntag] at h <;>
    first
    | omega
    | rfl

/-! ## The contract of one step -/

/-- A pair's rank (left = the trusted export's indices): every kid ranks below its pair. -/
def rank (t : Tables) : Pair → Nat
  | .name i _ => i
  | .level i _ => t.names.size + i
  | .expr i _ => t.names.size + t.levels.size + i

/-- `heads`' contract at one pair: `none` ⇒ unequal; `some kids` ⇒ equal exactly when every kid
is, each kid ranked below the pair. -/
def Decides (t1 t2 : Tables) (p : Pair) : Option (List Pair) → Prop
  | none => ¬PairEq t1 t2 p
  | some kids => (PairEq t1 t2 p ↔ ∀ k ∈ kids, PairEq t1 t2 k) ∧ ∀ k ∈ kids, rank t1 k < rank t1 p

theorem decides_none {t1 t2 : Tables} {p : Pair} (h : ¬PairEq t1 t2 p) : Decides t1 t2 p none := h

theorem decides_some {t1 t2 : Tables} {p : Pair} {kids : List Pair}
    (h : PairEq t1 t2 p ↔ ∀ k ∈ kids, PairEq t1 t2 k) (hr : ∀ k ∈ kids, rank t1 k < rank t1 p) :
    Decides t1 t2 p (some kids) := ⟨h, hr⟩

theorem unbound {α β : Type} {a : Array α} {b : Array β} {i : Nat} (hs : b.size = a.size)
    (h : b[i]? = none) : a[i]? = none := by
  rw [Array.getElem?_eq_none_iff] at h ⊢
  omega

/-! ## Names -/

theorem name_view {t : Tables} (h : RawOk t) {i : Nat} {a : Option NameF}
    (r : t.rawNames[i]? = some a) : ∃ n, t.names[i]? = some n ∧ nmtag n = ntag a := by
  cases a with
  | none => exact ⟨_, h.name0 i r, rfl⟩
  | some f =>
    obtain ⟨n, hn, hd⟩ := h.name i f r
    cases f with
    | str p s =>
      obtain ⟨x, _, rfl⟩ := hd
      exact ⟨_, hn, rfl⟩
    | num p k =>
      obtain ⟨x, _, rfl⟩ := hd
      exact ⟨_, hn, rfl⟩

theorem decides_name {t1 t2 : Tables} (h1 : RawOk t1) (h2 : RawOk t2) (i j : Nat) :
    Decides t1 t2 (.name i j) (heads t1 t2 (.name i j)) := by
  simp only [heads]
  cases r1 : t1.rawNames[i]? with
  | none =>
    apply decides_none
    rintro ⟨_, hx, _⟩
    rw [unbound h1.namesSize r1] at hx
    cases hx
  | some a =>
    cases r2 : t2.rawNames[j]? with
    | none =>
      apply decides_none
      rintro ⟨_, _, hy⟩
      rw [unbound h2.namesSize r2] at hy
      cases hy
    | some b =>
      show Decides t1 t2 (.name i j) (nameHeads a b)
      by_cases ht : ntag a = ntag b
      · rcases a with _ | (⟨p, s⟩ | ⟨p, k⟩) <;> rcases b with _ | (⟨q, s'⟩ | ⟨q, k'⟩) <;>
          simp [ntag] at ht
        · exact
            decides_some ⟨(fun _ k hk => by cases hk), fun _ => ⟨_, h1.name0 i r1, h2.name0 j r2⟩⟩
              (fun k hk => by cases hk)
        · obtain ⟨n1, hn1, x, hx, rfl⟩ := h1.name i _ r1
          obtain ⟨n2, hn2, y, hy, rfl⟩ := h2.name j _ r2
          obtain ⟨hp, hx⟩ := extract_some hx
          obtain ⟨-, hy⟩ := extract_some hy
          by_cases hs : s = s'
          · subst hs
            simp only [nameHeads, beq_self_eq_true, ↓reduceIte]
            refine decides_some ?_ ?_
            · simp [PairEq, hn1, hn2, hx, hy]
            · simpa [rank] using hp
          · have hb : (s == s') = false := by simpa using hs
            simp only [nameHeads, hb, Bool.false_eq_true, ↓reduceIte]
            apply decides_none
            rintro ⟨z, hz1, hz2⟩
            rw [hn1] at hz1
            rw [hn2] at hz2
            cases hz1
            simp only [Option.some.injEq, Lean.Name.str.injEq] at hz2
            exact hs hz2.2.symm
        · obtain ⟨n1, hn1, x, hx, rfl⟩ := h1.name i _ r1
          obtain ⟨n2, hn2, y, hy, rfl⟩ := h2.name j _ r2
          obtain ⟨hp, hx⟩ := extract_some hx
          obtain ⟨-, hy⟩ := extract_some hy
          by_cases hs : k = k'
          · subst hs
            simp only [nameHeads, beq_self_eq_true, ↓reduceIte]
            refine decides_some ?_ ?_
            · simp [PairEq, hn1, hn2, hx, hy]
            · simpa [rank] using hp
          · have hb : (k == k') = false := by simpa using hs
            simp only [nameHeads, hb, Bool.false_eq_true, ↓reduceIte]
            apply decides_none
            rintro ⟨z, hz1, hz2⟩
            rw [hn1] at hz1
            rw [hn2] at hz2
            cases hz1
            simp only [Option.some.injEq, Lean.Name.num.injEq] at hz2
            exact hs hz2.2.symm
      · rw [nameHeads_tag ht]
        apply decides_none
        rintro ⟨z, hz1, hz2⟩
        obtain ⟨n1, hn1, ht1⟩ := name_view h1 r1
        obtain ⟨n2, hn2, ht2⟩ := name_view h2 r2
        rw [hn1] at hz1
        rw [hn2] at hz2
        cases hz1
        cases hz2
        exact ht (ht1.symm.trans ht2)

/-! ## Levels -/

theorem level_view {t : Tables} (h : RawOk t) {i : Nat} {a : Option LevelF}
    (r : t.rawLevels[i]? = some a) : ∃ v, t.levels[i]? = some v ∧ lvtag v = ltag a := by
  cases a with
  | none => exact ⟨_, h.level0 i r, rfl⟩
  | some f =>
    obtain ⟨v, hv, hd⟩ := h.level i f r
    cases f with
    | succ l =>
      obtain ⟨_, _, rfl⟩ := hd
      exact ⟨_, hv, rfl⟩
    | max a b =>
      obtain ⟨_, _, _, _, rfl⟩ := hd
      exact ⟨_, hv, rfl⟩
    | imax a b =>
      obtain ⟨_, _, _, _, rfl⟩ := hd
      exact ⟨_, hv, rfl⟩
    | param n =>
      obtain ⟨_, _, rfl⟩ := hd
      exact ⟨_, hv, rfl⟩

theorem decides_level {t1 t2 : Tables} (h1 : RawOk t1) (h2 : RawOk t2) (i j : Nat) :
    Decides t1 t2 (.level i j) (heads t1 t2 (.level i j)) := by
  simp only [heads]
  cases r1 : t1.rawLevels[i]? with
  | none =>
    apply decides_none
    rintro ⟨_, _, hx, _⟩
    rw [unbound h1.levelsSize r1] at hx
    cases hx
  | some a =>
    cases r2 : t2.rawLevels[j]? with
    | none =>
      apply decides_none
      rintro ⟨_, _, _, hy, _⟩
      rw [unbound h2.levelsSize r2] at hy
      cases hy
    | some b =>
      show Decides t1 t2 (.level i j) (levelHeads a b)
      by_cases ht : ltag a = ltag b
      · rcases a with _ | (⟨l⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨n⟩) <;>
          rcases b with _ | (⟨l'⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨n'⟩) <;>
          simp [ltag] at ht
        · exact
            decides_some
              ⟨(fun _ k hk => by cases hk), fun _ => ⟨_, _, h1.level0 i r1, h2.level0 j r2, rfl⟩⟩
              (fun k hk => by cases hk)
        · obtain ⟨v1, hv1, x, hx, rfl⟩ := h1.level i _ r1
          obtain ⟨v2, hv2, y, hy, rfl⟩ := h2.level j _ r2
          obtain ⟨hl, hx⟩ := extract_some hx
          obtain ⟨-, hy⟩ := extract_some hy
          refine decides_some ?_ ?_
          · simp [PairEq, hv1, hv2, hx, hy, levelEq_succ]
          · simpa [rank] using hl
        · obtain ⟨v1, hv1, x1, x2, hx1, hx2, rfl⟩ := h1.level i _ r1
          obtain ⟨v2, hv2, y1, y2, hy1, hy2, rfl⟩ := h2.level j _ r2
          obtain ⟨hl1, hx1⟩ := extract_some hx1
          obtain ⟨hl2, hx2⟩ := extract_some hx2
          obtain ⟨-, hy1⟩ := extract_some hy1
          obtain ⟨-, hy2⟩ := extract_some hy2
          refine decides_some ?_ ?_
          · simp [PairEq, hv1, hv2, hx1, hx2, hy1, hy2, levelEq_max]
          · simp [rank]
            omega
        · obtain ⟨v1, hv1, x1, x2, hx1, hx2, rfl⟩ := h1.level i _ r1
          obtain ⟨v2, hv2, y1, y2, hy1, hy2, rfl⟩ := h2.level j _ r2
          obtain ⟨hl1, hx1⟩ := extract_some hx1
          obtain ⟨hl2, hx2⟩ := extract_some hx2
          obtain ⟨-, hy1⟩ := extract_some hy1
          obtain ⟨-, hy2⟩ := extract_some hy2
          refine decides_some ?_ ?_
          · simp [PairEq, hv1, hv2, hx1, hx2, hy1, hy2, levelEq_imax]
          · simp [rank]
            omega
        · obtain ⟨v1, hv1, x, hx, rfl⟩ := h1.level i _ r1
          obtain ⟨v2, hv2, y, hy, rfl⟩ := h2.level j _ r2
          refine decides_some ?_ ?_
          · simp [PairEq, hv1, hv2, hx, hy, levelEq_param]
            exact eq_comm
          · have := lt_of_some hx
            simp [rank]
            omega
      · rw [levelHeads_tag ht]
        apply decides_none
        rintro ⟨x, y, hx, hy, he⟩
        obtain ⟨v1, hv1, ht1⟩ := level_view h1 r1
        obtain ⟨v2, hv2, ht2⟩ := level_view h2 r2
        rw [hv1] at hx
        rw [hv2] at hy
        cases hx
        cases hy
        have hlt : ∀ c : Option LevelF, ltag c < 5 := fun c => by
          rcases c with _ | (_ | _ | _ | _) <;> simp [ltag]
        rw [levelEq_tag
            (by
              rw [ht1, ht2]; exact ht)
            (by
              rw [ht1]; exact hlt a)
            (by
              rw [ht2]; exact hlt b)] at he
        cases he

end FvdepAudit.Judge.Proof
