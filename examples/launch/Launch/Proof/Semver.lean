import Launch.Semver
import Fvdep.Semver.Compare.V1_0_0
import Fvdep.Semver.Parse.V1_0_0

/-! Launch proofs (contract U7 E): the SemVer example = the library's `semver.parse` +
`semver.compare` specs. -/

namespace Launch.Proof.Semver

open Fvdep.Semver.Version.V1_0_0 (Ident Version)

/-! ## compare -/

theorem ordNat (a b : Nat) : Ord.compare a b = Fvdep.Semver.Compare.V1_0_0.nat a b := by
  simp only [Ord.compare, compareOfLessAndEq, Fvdep.Semver.Compare.V1_0_0.nat]

theorem lexChars :
    ∀ (a b : List Char),
      Launch.Semver.lex (fun x y => Ord.compare x.toNat y.toNat) a b =
        Fvdep.Semver.Compare.V1_0_0.chars a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [Launch.Semver.lex]
    rw [lexChars xs ys]
    simp only [ordNat, Fvdep.Semver.Compare.V1_0_0.chars]

theorem identEq (a b : Ident) :
    Launch.Semver.ident a b = Fvdep.Semver.Compare.V1_0_0.ident a b := by
  cases a <;> cases b
  · exact ordNat _ _
  · rfl
  · rfl
  · exact lexChars _ _

theorem lexIdents :
    ∀ (p q : List Ident),
      Launch.Semver.lex Ord.compare p q = Fvdep.Semver.Compare.V1_0_0.idents p q
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [Launch.Semver.lex, Fvdep.Semver.Compare.V1_0_0.idents, lexIdents xs ys]
    exact congrArg (fun o => o.then (Fvdep.Semver.Compare.V1_0_0.idents xs ys)) (identEq x y)

theorem compare_eq : Launch.Semver.compare = Fvdep.Semver.Compare.V1_0_0.compare := by
  funext a b
  simp only [Launch.Semver.compare, Fvdep.Semver.Compare.V1_0_0.compare, ordNat]
  congr 3
  match ha : a.pre, hb : b.pre with
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => exact lexIdents (x :: xs) (y :: ys)

/-! ## parse -/

theorem idCharEq (c : Char) : Launch.Semver.idChar c = Fvdep.Semver.Parse.V1_0_0.identChar c := by
  simp only [Launch.Semver.idChar, Fvdep.Semver.Parse.V1_0_0.identChar, Char.isAlphanum]
  cases c.isAlpha <;> cases c.isDigit <;> rfl

theorem splitAtNonempty (sep : Char) : ∀ cs : List Char, Launch.Semver.splitAt sep cs ≠ []
  | [] => by simp [Launch.Semver.splitAt]
  | c :: cs => by
    have h := splitAtNonempty sep cs
    simp only [Launch.Semver.splitAt]
    split
    · split <;> simp
    · simp

theorem splitAtEq (sep : Char) :
    ∀ cs : List Char, Launch.Semver.splitAt sep cs = Fvdep.Semver.Parse.V1_0_0.splitOn sep cs
  | [] => rfl
  | c :: cs => by
    have ih := splitAtEq sep cs
    have hne := splitAtNonempty sep cs
    simp only [Launch.Semver.splitAt, Fvdep.Semver.Parse.V1_0_0.splitOn]
    rw [← ih]
    cases h : Launch.Semver.splitAt sep cs with
    | nil => exact absurd h hne
    | cons p ps => by_cases hc : c = sep <;> simp [hc]

theorem splitFirstEq (sep : Char) :
    ∀ cs : List Char,
      Launch.Semver.splitFirst sep cs = Fvdep.Semver.Parse.V1_0_0.splitFirst sep cs
  | [] => rfl
  | c :: cs => by
    have ih := splitFirstEq sep cs
    simp only [Launch.Semver.splitFirst, Fvdep.Semver.Parse.V1_0_0.splitFirst, ih]
    by_cases hc : c = sep <;> simp [hc]

theorem foldDigits (s : List Char) :
    s.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0 =
      s.foldl (fun n c => 10 * n + (c.toNat - 48)) 0 := by
  have : (fun n (c : Char) => n * 10 + (c.toNat - '0'.toNat)) =
      fun n c => 10 * n + (c.toNat - 48) := by
    funext n c
    rw [Nat.mul_comm]
    rfl
  rw [this]

theorem numericEq (s : List Char) :
    Launch.Semver.numeric? s = Fvdep.Semver.Parse.V1_0_0.numeric s := by
  simp only [Launch.Semver.numeric?, Fvdep.Semver.Parse.V1_0_0.numeric, foldDigits]
  by_cases h1 : (s.isEmpty || !s.all Char.isDigit) = true
  · simp [h1]
  · by_cases h2 : (1 < s.length && s.head? == some '0') = true
    · have : (s.head? == some '0' && decide (s.length > 1)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
        exact ⟨h2.2, h2.1⟩
      simp [h1, h2, this]
    · have : (s.head? == some '0' && decide (s.length > 1)) = false := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h2
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases h : (s.head? == some '0') = true
        · exact Or.inr (fun hl => h2 hl h)
        · exact Or.inl (by simpa using h)
      simp [h1, h2, this]

theorem allIdChar (s : List Char) :
    s.all Launch.Semver.idChar = s.all Fvdep.Semver.Parse.V1_0_0.identChar := by
  have : Launch.Semver.idChar = Fvdep.Semver.Parse.V1_0_0.identChar := funext idCharEq
  rw [this]

theorem preIdentEq (s : List Char) :
    Launch.Semver.preIdent? s = Fvdep.Semver.Parse.V1_0_0.preIdent s := by
  simp only [Launch.Semver.preIdent?, Fvdep.Semver.Parse.V1_0_0.preIdent, allIdChar, numericEq]

theorem buildEq :
    ∀ ids : List (List Char),
      (if ids.all (fun i => !i.isEmpty && i.all Launch.Semver.idChar) then pure ids else none) =
        ids.mapM Fvdep.Semver.Parse.V1_0_0.buildIdent
  | [] => rfl
  | i :: is => by
    have ih := buildEq is
    have hi : (!i.isEmpty && i.all Launch.Semver.idChar) =
        !(i.isEmpty || !i.all Fvdep.Semver.Parse.V1_0_0.identChar) := by
      rw [allIdChar]
      cases i.isEmpty <;> cases i.all Fvdep.Semver.Parse.V1_0_0.identChar <;> rfl
    rw [List.mapM_cons, ← ih]
    simp only [List.all_cons, Fvdep.Semver.Parse.V1_0_0.buildIdent, hi]
    cases h1 : (i.isEmpty || !i.all Fvdep.Semver.Parse.V1_0_0.identChar) <;>
      cases h2 : is.all (fun i => !i.isEmpty && i.all Launch.Semver.idChar) <;> simp

theorem bindIte {α β : Type} (p : Prop) [Decidable p] (a : Option α) (k : α → Option β) :
    ((if p then a else none) >>= k) = if p then a >>= k else none >>= k := by
  split <;> rfl

theorem parse_eq : Launch.Semver.parse = Fvdep.Semver.Parse.V1_0_0.parse := by
  funext s
  have hp : Launch.Semver.preIdent? = Fvdep.Semver.Parse.V1_0_0.preIdent := funext preIdentEq
  simp only [Launch.Semver.parse, Fvdep.Semver.Parse.V1_0_0.parse, splitFirstEq, splitAtEq,
    numericEq, hp, ← buildEq, bindIte]
  rfl

end Launch.Proof.Semver
