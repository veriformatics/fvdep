import FvdepAudit.Judge.Proof.Heads
import FvdepAudit.Judge.Statement.Spec

/-! Proofs: S2's one-pass loose-variable ranges (contract `docs/contracts/U7-judge.md` S2) — on the
tables of an export the reader accepts, each entry of `bvarRanges` is at most `d` exactly when its
expression is closed under `d` binders. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepAudit.Export.Spec FvdepAudit.Judge.Statement.Spec

/-- The pass over the first `n` indices. -/
def ranges (t : Tables) (n : Nat) : Array Nat :=
  (List.range n).foldl (fun r i => r.push (rangeOf t r i)) #[]

theorem ranges_succ (t : Tables) (n : Nat) :
    ranges t (n + 1) = (ranges t n).push (rangeOf t (ranges t n) n) := by
  simp [ranges, List.range_succ, List.foldl_append]

theorem ranges_size (t : Tables) : ∀ n, (ranges t n).size = n
  | 0 => rfl
  | n + 1 => by rw [ranges_succ, Array.size_push, ranges_size t n]

theorem bvarRanges_eq (t : Tables) (upto : Nat) : bvarRanges t upto = ranges t (upto + 1) := rfl

/-- Each entry of the pass ≤ `d` exactly when its expression is closed under `d` binders. -/
theorem ranges_spec {t : Tables} (h : RawOk t) :
    ∀ n, ∀ i < n, ∀ e, t.exprs[i]? = some e → ∀ d, ((ranges t n).getD i 0 ≤ d ↔ Closed e d)
  | 0, _, hi, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, hi, e, he, d => by
    have ih := ranges_spec h n
    have hs := ranges_size t n
    rw [ranges_succ, Array.getD_eq_getD_getElem?, Array.getElem?_push]
    by_cases hin : i = n
    · subst hin
      simp only [hs, ↓reduceIte, Option.getD_some]
      have hr : (t.rawExprs[i]?).isSome := by
        rw [Option.isSome_iff_exists]
        have := lt_of_some he
        rw [← h.exprsSize] at this
        exact ⟨_, Array.getElem?_eq_getElem this⟩
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hr
      obtain ⟨e', he', hd⟩ := h.expr i f hf
      rw [he] at he'
      cases he'
      have child :
        ∀ (c : Nat) (x : Lean.Expr),
          (t.exprs.extract 0 i)[c]? = some x → ∀ d, ((ranges t i).getD c 0 ≤ d ↔ Closed x d) :=
        fun c x hc d => by
        obtain ⟨hlt, hx⟩ := extract_some hc
        exact ih c hlt x hx d
      cases f with
      | bvar k =>
        cases hd
        simp only [rangeOf, hf, Closed]
        omega
      | sort l =>
        obtain ⟨_, _, rfl⟩ := hd
        simp [rangeOf, hf, Closed]
      | const n us =>
        obtain ⟨_, _, _, _, rfl⟩ := hd
        simp [rangeOf, hf, Closed]
      | app f a =>
        obtain ⟨x, y, hx, hy, rfl⟩ := hd
        simp only [rangeOf, hf, Closed, Nat.max_le, child f x hx d, child a y hy d]
      | lam n ty b bi =>
        obtain ⟨_, u, w, _, hu, hw, rfl⟩ := hd
        have hb := child b w hw (d + 1)
        have hb' : (ranges t i).getD b 0 - 1 ≤ d ↔ Closed w (d + 1) :=
          ⟨fun h' => hb.1 (by omega), fun h' => by
            have := hb.2 h'; omega⟩
        simp only [rangeOf, hf, Closed, Nat.max_le, child ty u hu d, hb']
      | forallE n ty b bi =>
        obtain ⟨_, u, w, _, hu, hw, rfl⟩ := hd
        have hb := child b w hw (d + 1)
        have hb' : (ranges t i).getD b 0 - 1 ≤ d ↔ Closed w (d + 1) :=
          ⟨fun h' => hb.1 (by omega), fun h' => by
            have := hb.2 h'; omega⟩
        simp only [rangeOf, hf, Closed, Nat.max_le, child ty u hu d, hb']
      | letE n ty v b nd =>
        obtain ⟨_, u, z, w, _, hu, hz, hw, rfl⟩ := hd
        have hb := child b w hw (d + 1)
        have hb' : (ranges t i).getD b 0 - 1 ≤ d ↔ Closed w (d + 1) :=
          ⟨fun h' => hb.1 (by omega), fun h' => by
            have := hb.2 h'; omega⟩
        simp only [rangeOf, hf, Closed, Nat.max_le, child ty u hu d, child v z hz d, hb', and_assoc]
      | proj tn idx s =>
        obtain ⟨_, y, _, hy, rfl⟩ := hd
        simp only [rangeOf, hf, Closed, child s y hy d]
      | natVal v =>
        cases hd
        simp [rangeOf, hf, Closed]
      | strVal s =>
        cases hd
        simp [rangeOf, hf, Closed]
    · have hne : i ≠ (ranges t n).size := by
        rw [hs]; exact hin
      simp only [hne, ↓reduceIte]
      rw [← Array.getD_eq_getD_getElem?]
      exact ih i (by omega) e he d

theorem getD_in {a : Array Nat} {i : Nat} (hi : i < a.size) (d d' : Nat) :
    a.getD i d = a.getD i d' := by simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]

theorem raw_of_expr {t : Tables} (h : RawOk t) {i : Nat} {S : Lean.Expr}
    (hS : t.exprs[i]? = some S) :
    ∃ f, t.rawExprs[i]? = some f ∧ ExprDenotes t.names t.levels (t.exprs.extract 0 i) f S := by
  have hr : (t.rawExprs[i]?).isSome := by
    rw [Option.isSome_iff_exists]
    have := lt_of_some hS
    rw [← h.exprsSize] at this
    exact ⟨_, Array.getElem?_eq_getElem this⟩
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hr
  obtain ⟨e', he', hd⟩ := h.expr i f hf
  rw [hS] at he'
  cases he'
  exact ⟨f, hf, hd⟩

/-- S2's arrow test, sound: a closed nondependent `A → B`, `b` = B's index. -/
theorem arrowCodomain_some {t : Tables} (h : RawOk t) {ty b : Nat} {S : Lean.Expr}
    (hS : t.exprs[ty]? = some S) (hc : arrowCodomain? t ty = some b) :
    ∃ n A B bi, S = .forallE n A B bi ∧ Closed A 0 ∧ Closed B 0 ∧ t.exprs[b]? = some B := by
  obtain ⟨f, hf, hd⟩ := raw_of_expr h hS
  unfold arrowCodomain? at hc
  rw [hf] at hc
  cases f with
  | forallE n a bb bi =>
    obtain ⟨x, u, w, _, hu, hw, rfl⟩ := hd
    obtain ⟨ha, hu⟩ := extract_some hu
    obtain ⟨hb, hw⟩ := extract_some hw
    have spec := ranges_spec h (max a bb + 1)
    rw [← bvarRanges_eq] at spec
    have sa := spec a (by omega) u hu 0
    have sb := spec bb (by omega) w hw 0
    have hsz := ranges_size t (max a bb + 1)
    rw [← bvarRanges_eq] at hsz
    rw [getD_in (by omega) 0 1] at sa sb
    simp only [Nat.le_zero] at sa sb
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    split at hc
    · rename_i hz
      simp only [Option.some.injEq] at hc
      subst hc
      exact ⟨x, u, w, bi, rfl, sa.1 hz.1, sb.1 hz.2, hw⟩
    · cases hc
  | bvar _ => cases hc
  | sort _ => cases hc
  | const _ _ => cases hc
  | app _ _ => cases hc
  | lam _ _ _ _ => cases hc
  | letE _ _ _ _ _ => cases hc
  | proj _ _ _ => cases hc
  | natVal _ => cases hc
  | strVal _ => cases hc

/-- S2's arrow test, complete: no index ⇒ no closed nondependent arrow. -/
theorem arrowCodomain_none {t : Tables} (h : RawOk t) {ty : Nat} {S : Lean.Expr}
    (hS : t.exprs[ty]? = some S) (hc : arrowCodomain? t ty = none) :
    ¬∃ n A B bi, S = .forallE n A B bi ∧ Closed A 0 ∧ Closed B 0 := by
  rintro ⟨n', A, B, bi', rfl, hA, hB⟩
  obtain ⟨f, hf, hd⟩ := raw_of_expr h hS
  have ht := etag_denotes hd
  unfold arrowCodomain? at hc
  rw [hf] at hc
  cases f with
  | forallE n a bb bi =>
    obtain ⟨_, u, w, _, hu, hw, he⟩ := hd
    simp only [Lean.Expr.forallE.injEq] at he
    obtain ⟨_, hAu, hBw, _⟩ := he
    obtain ⟨ha, hu⟩ := extract_some hu
    obtain ⟨hb, hw⟩ := extract_some hw
    have spec := ranges_spec h (max a bb + 1)
    rw [← bvarRanges_eq] at spec
    have sa := spec a (by omega) u hu 0
    have sb := spec bb (by omega) w hw 0
    have hsz := ranges_size t (max a bb + 1)
    rw [← bvarRanges_eq] at hsz
    rw [getD_in (by omega) 0 1] at sa sb
    simp only [Nat.le_zero] at sa sb
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    split at hc
    · cases hc
    · rename_i hz
      exact hz ⟨sa.2 (hAu ▸ hA), sb.2 (hBw ▸ hB)⟩
  | bvar _ => simp [etag, ftag] at ht
  | sort _ => simp [etag, ftag] at ht
  | const _ _ => simp [etag, ftag] at ht
  | app _ _ => simp [etag, ftag] at ht
  | lam _ _ _ _ => simp [etag, ftag] at ht
  | letE _ _ _ _ _ => simp [etag, ftag] at ht
  | proj _ _ _ => simp [etag, ftag] at ht
  | natVal _ => simp [etag, ftag] at ht
  | strVal _ => simp [etag, ftag] at ht

end FvdepAudit.Judge.Proof
