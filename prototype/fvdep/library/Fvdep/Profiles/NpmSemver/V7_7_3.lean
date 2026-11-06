import Fvdep.Semver.Parse.V1_1_0
import Fvdep.Semver.Compare.V1_1_0
/-!
# Profile: npm `semver` 7.7.3 (`valid`, `compare`)

Model = a port of `new SemVer(text)` (strict mode) and `SemVer.compare`, checked against the real
package by `fvdep profile npm:semver@7.7.3 --check`.

`parse` (`semver.valid(text)`): the input may be at most 256 UTF-16 code units; it is trimmed of
JavaScript whitespace; the regex `^v?MAJOR.MINOR.PATCH(-PRE)?(+BUILD)?$` is the contract grammar
plus an optional leading `v`; `+m[i]` turns the core numbers into JavaScript numbers and any above
2^53 − 1 are rejected; the returned text (`.version`) leaves out build metadata.

`compare` (`semver.compare(a, b)`): the core numbers compare exactly (they are at most 2^53 − 1).
Pre-release identifiers are compared left to right; two equal identifiers are skipped, and the
first unequal pair decides. Numeric identifiers of 2^53 − 1 or more stay strings and are then
compared after JavaScript's conversion to a double (`+a < +b`), which rounds; two distinct numbers
that round to the same double make the whole comparison "equal".

Lengths count UTF-16 code units, as JavaScript does.
-/
namespace Fvdep.Profiles.NpmSemver.V7_7_3
open Fvdep.Semver
open Parse.V1_0_0 (Version Ident)
open Compare.V1_0_0 (cmpNat cmpChars)

/-! ## parse: `semver.valid(text)` -/

/-- JavaScript `String.prototype.trim` whitespace: WhiteSpace + LineTerminator code points. -/
def jsSpace (c : Char) : Bool :=
  [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20, 0xA0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004,
    0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000,
    0xFEFF].contains c.toNat

/-- `text.trim()`: drop JavaScript whitespace at both ends. -/
def trim (s : List Char) : List Char := ((s.dropWhile jsSpace).reverse.dropWhile jsSpace).reverse

/-- `text.length`: UTF-16 code units (2 for a code point above U+FFFF). -/
def utf16Length (s : List Char) : Nat := s.foldr (fun c n => (if c.toNat > 0xFFFF then 2 else 1) + n) 0

/-- The regex's optional leading `v?`. -/
def dropV : List Char → List Char
  | 'v' :: cs => cs
  | cs => cs

/-- `Number.MAX_SAFE_INTEGER` = 2^53 − 1. -/
def maxSafe : Nat := 9007199254740991

/-- The constructor's `Invalid major/minor/patch version` checks. -/
def safeCore (v : Version) : Bool := v.major ≤ maxSafe && v.minor ≤ maxSafe && v.patch ≤ maxSafe

def parse (s : List Char) : Option Version :=
  if utf16Length s > 256 then none
  else match Parse.V1_1_0.parse (dropV (trim s)) with
    | some v => if safeCore v then some { v with build := [] } else none
    | none => none

/-! ## compare: `semver.compare(a, b)` -/

/-- JavaScript's `+digits`: the nearest double (ties to even), as a whole number. Exact below 2^53. -/
def toDouble (n : Nat) : Nat :=
  if n < 2 ^ 53 then n else
  let g := 2 ^ (n.log2 - 52)
  let q := n / g
  let r := n % g
  (if 2 * r > g ∨ (2 * r = g ∧ q % 2 = 1) then q + 1 else q) * g

/-- `compareIdentifiers(a, b)` for two unequal identifiers. -/
def cmpIdent : Ident → Ident → Ordering
  | .num a, .num b => cmpNat (toDouble a) (toDouble b)
  | .num _, .alnum _ => .lt
  | .alnum _, .num _ => .gt
  | .alnum a, .alnum b => cmpChars a b

/-- The `comparePre` loop: equal identifiers (`a === b`) are skipped; the first unequal pair decides. -/
def cmpIds : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a = b then cmpIds as bs else cmpIdent a b

/-- A release ranks above any pre-release. -/
def cmpPre : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | a, b => cmpIds a b

/-- `compareMain(other) || comparePre(other)`. -/
def compare (a b : Version) : Ordering :=
  (cmpNat a.major b.major).then <| (cmpNat a.minor b.minor).then <|
    (cmpNat a.patch b.patch).then (cmpPre a.pre b.pre)

/-! ## parse vs `semver.parse@1.1.0` -/

/-- Complete: the package accepts exactly the texts of at most 256 UTF-16 code units that, after
trimming whitespace and dropping one leading `v`, the contract accepts with core numbers at most
2^53 − 1; it returns the contract's version without its build metadata. -/
theorem parse_exact (s : List Char) :
    parse s = if utf16Length s > 256 then none else
      (Parse.V1_1_0.parse (dropV (trim s))).bind fun v =>
        if safeCore v then some { v with build := [] } else none := by
  unfold parse
  split
  · rfl
  · cases Parse.V1_1_0.parse (dropV (trim s)) <;> rfl

/-- Witness: build metadata is dropped (`1.0.0+build` → `1.0.0`). -/
theorem dev_build_dropped :
    parse "1.0.0+build".toList = some ⟨1, 0, 0, [], []⟩ ∧
    Parse.V1_1_0.parse "1.0.0+build".toList = some ⟨1, 0, 0, [], ["build".toList]⟩ := by decide

/-- Witness: a leading `v` is accepted (`v1.2.3` → `1.2.3`). -/
theorem dev_v_prefix :
    parse "v1.2.3".toList = some ⟨1, 2, 3, [], []⟩ ∧
    Parse.V1_1_0.parse "v1.2.3".toList = none := by decide

/-- Witness: surrounding whitespace is trimmed (` 1.2.3 ` → `1.2.3`). -/
theorem dev_whitespace_trimmed :
    parse " 1.2.3 ".toList = some ⟨1, 2, 3, [], []⟩ ∧
    Parse.V1_1_0.parse " 1.2.3 ".toList = none := by decide

/-- The 257-character version `1.0.0-aaa…a`. -/
def longText : List Char := "1.0.0-".toList ++ List.replicate 251 'a'

set_option maxRecDepth 100000 in
/-- Witness: texts longer than 256 characters are rejected, even valid ones. -/
theorem dev_too_long :
    parse longText = none ∧
    Parse.V1_1_0.parse longText = some ⟨1, 0, 0, [.alnum (List.replicate 251 'a')], []⟩ := by
  decide

/-- Witness: a core number above 2^53 − 1 is rejected (`9007199254740992.0.0`). -/
theorem dev_unsafe_core :
    parse "9007199254740992.0.0".toList = none ∧
    Parse.V1_1_0.parse "9007199254740992.0.0".toList = some ⟨9007199254740992, 0, 0, [], []⟩ := by
  decide

/-! ## Rounding to a double is monotone -/

/-- Round `n / g` to the nearest whole number, ties to even. -/
def rnd (g n : Nat) : Nat :=
  if 2 * (n % g) > g ∨ (2 * (n % g) = g ∧ (n / g) % 2 = 1) then n / g + 1 else n / g

theorem rnd_mono (g n m : Nat) (hg : 0 < g) (h : n ≤ m) : rnd g n ≤ rnd g m := by
  have hn := Nat.div_add_mod n g
  have hm := Nat.div_add_mod m g
  have hq : n / g ≤ m / g := Nat.div_le_div_right h
  have hrn := Nat.mod_lt n hg
  have hrm := Nat.mod_lt m hg
  unfold rnd
  rcases Nat.lt_or_eq_of_le hq with hlt | heq
  · split <;> split <;> omega
  · have : n % g ≤ m % g := by
      rw [heq] at hn
      generalize g * (m / g) = t at hn hm
      omega
    rw [heq]
    split <;> split <;> omega

theorem toDouble_eq (n : Nat) (h : ¬ n < 2 ^ 53) :
    toDouble n = rnd (2 ^ (n.log2 - 52)) n * 2 ^ (n.log2 - 52) := by
  simp only [toDouble, h, ite_false, rnd]

theorem log2_ge (n : Nat) (h : ¬ n < 2 ^ 53) : 53 ≤ n.log2 :=
  (Nat.le_log2 (by intro e; subst e; exact h (by decide))).2 (by omega)

/-- Above 2^53 the rounded value stays between `2^k` and `2^(k+1)`, `k` = the bit length − 1. -/
theorem toDouble_bounds (n : Nat) (h : ¬ n < 2 ^ 53) :
    2 ^ n.log2 ≤ toDouble n ∧ toDouble n ≤ 2 ^ (n.log2 + 1) := by
  have hk := log2_ge n h
  have hn0 : n ≠ 0 := by intro e; subst e; exact h (by decide)
  have lo := Nat.log2_self_le hn0
  have hi := Nat.lt_log2_self (n := n)
  rw [toDouble_eq n h]
  generalize hg : 2 ^ (n.log2 - 52) = g
  have hgpos : 0 < g := hg ▸ Nat.two_pow_pos _
  have e1 : 2 ^ n.log2 = 2 ^ 52 * g := by
    rw [← hg, ← Nat.pow_add]; congr 1; omega
  have e2 : 2 ^ (n.log2 + 1) = 2 ^ 53 * g := by
    rw [← hg, ← Nat.pow_add]; congr 1; omega
  rw [e1, e2]; rw [e1] at lo; rw [e2] at hi
  have q1 : 2 ^ 52 ≤ n / g := (Nat.le_div_iff_mul_le hgpos).2 (Nat.mul_comm (2 ^ 52) g ▸ lo)
  have q2 : n / g < 2 ^ 53 := (Nat.div_lt_iff_lt_mul hgpos).2 (Nat.mul_comm (2 ^ 53) g ▸ hi)
  unfold rnd
  constructor
  · split
    · exact Nat.le_trans (Nat.mul_le_mul_right g q1) (Nat.mul_le_mul_right g (Nat.le_succ _))
    · exact Nat.mul_le_mul_right g q1
  · split
    · exact Nat.mul_le_mul_right g q2
    · exact Nat.mul_le_mul_right g (Nat.le_of_lt q2)

theorem toDouble_small (n : Nat) (h : n < 2 ^ 53) : toDouble n = n := by
  simp [toDouble, h]

/-- JavaScript's number conversion never reverses an order. -/
theorem toDouble_mono (n m : Nat) (h : n ≤ m) : toDouble n ≤ toDouble m := by
  by_cases hm : m < 2 ^ 53
  · rw [toDouble_small n (by omega), toDouble_small m hm]; exact h
  by_cases hn : n < 2 ^ 53
  · rw [toDouble_small n hn]
    have := (toDouble_bounds m hm).1
    have : 2 ^ 53 ≤ 2 ^ m.log2 := Nat.pow_le_pow_right (by decide) (log2_ge m hm)
    omega
  have hl : n.log2 ≤ m.log2 := by
    have hn0 : n ≠ 0 := by intro e; subst e; exact hn (by decide)
    have hm0 : m ≠ 0 := by intro e; subst e; exact hm (by decide)
    exact (Nat.le_log2 hm0).2 (Nat.le_trans (Nat.log2_self_le hn0) h)
  rcases Nat.lt_or_eq_of_le hl with hlt | heq
  · have := (toDouble_bounds n hn).2
    have := (toDouble_bounds m hm).1
    have : 2 ^ (n.log2 + 1) ≤ 2 ^ m.log2 := Nat.pow_le_pow_right (by decide) hlt
    omega
  · rw [toDouble_eq n hn, toDouble_eq m hm, heq]
    exact Nat.mul_le_mul_right _ (rnd_mono _ _ _ (Nat.two_pow_pos _) h)

/-! ## compare vs `semver.compare@1.1.0` -/

/-- The first position where two identifier lists differ, if both still have an identifier there. -/
def firstDiff : List Ident → List Ident → Option (Ident × Ident)
  | a :: as, b :: bs => if a = b then firstDiff as bs else some (a, b)
  | _, _ => none

/-- The deviation case: same core, and the first differing pre-release identifiers are two
different numbers that JavaScript rounds to the same double. -/
def collides (a b : Version) : Bool :=
  a.major == b.major && a.minor == b.minor && a.patch == b.patch &&
    match firstDiff a.pre b.pre with
    | some (.num x, .num y) => toDouble x == toDouble y
    | _ => false

theorem cmpNat_ne_eq (x y : Nat) (h : x ≠ y) : cmpNat x y ≠ .eq := by
  rw [Ne, Compare.V1_1_0.cmpNat_eq]; exact h

theorem cmpNat_toDouble (x y : Nat) (h : toDouble x ≠ toDouble y) :
    cmpNat (toDouble x) (toDouble y) = cmpNat x y := by
  have hxy : x ≠ y := fun e => h (e ▸ rfl)
  rcases Nat.lt_or_gt_of_ne hxy with l | l
  · have := toDouble_mono x y (Nat.le_of_lt l)
    simp [cmpNat, l, show toDouble x < toDouble y by omega]
  · have := toDouble_mono y x (Nat.le_of_lt l)
    have h1 : ¬ x < y := by omega
    have h2 : ¬ toDouble x < toDouble y := by omega
    simp [cmpNat, h1, h2, hxy, h]

theorem cmpIds_exact (as bs : List Ident) :
    cmpIds as bs = match firstDiff as bs with
      | some (.num x, .num y) =>
        if toDouble x = toDouble y then .eq else Compare.V1_0_0.cmpIds as bs
      | _ => Compare.V1_0_0.cmpIds as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      by_cases hab : a = b
      · subst hab
        have hr : Compare.V1_0_0.cmpIdent a a = .eq := by
          cases a <;> simp [Compare.V1_0_0.cmpIdent, cmpNat, Compare.V1_0_0.cmpChars_refl]
        simp only [cmpIds, firstDiff, ite_true, Compare.V1_0_0.cmpIds, hr, Ordering.eq_then]
        exact ih bs
      · simp only [cmpIds, firstDiff, hab, ite_false, Compare.V1_0_0.cmpIds]
        have hne : Compare.V1_0_0.cmpIdent a b ≠ .eq := fun e => hab (Compare.V1_1_0.cmpIdent_eq _ _ e)
        have hthen : ∀ o, (Compare.V1_0_0.cmpIdent a b).then o = Compare.V1_0_0.cmpIdent a b := by
          intro o; revert hne; cases Compare.V1_0_0.cmpIdent a b <;> simp [Ordering.then]
        rw [hthen]
        cases a with
        | num x =>
          cases b with
          | num y =>
            simp only [cmpIdent, Compare.V1_0_0.cmpIdent]
            by_cases hd : toDouble x = toDouble y
            · simp [hd, cmpNat]
            · simp [hd, cmpNat_toDouble x y hd]
          | alnum t => rfl
        | alnum t =>
          cases b with
          | num y => rfl
          | alnum u => rfl

theorem firstDiff_nil_left (bs : List Ident) : firstDiff [] bs = none := by cases bs <;> rfl
theorem firstDiff_nil_right (as : List Ident) : firstDiff as [] = none := by cases as <;> rfl

/-- Complete: the package compares exactly as the contract, except when the cores are equal and the
first differing pre-release identifiers are two different numbers that JavaScript rounds to the
same double (possible only from 2^53 up); then the package says "equal". -/
theorem compare_exact (a b : Version) :
    compare a b = if collides a b then .eq else Compare.V1_1_0.compare a b := by
  obtain ⟨a1, a2, a3, ap, ab⟩ := a
  obtain ⟨b1, b2, b3, bp, bb⟩ := b
  have hpre : cmpPre ap bp = match firstDiff ap bp with
      | some (.num x, .num y) =>
        if toDouble x = toDouble y then .eq else Compare.V1_0_0.cmpPre ap bp
      | _ => Compare.V1_0_0.cmpPre ap bp := by
    rcases ap with _ | ⟨x, xs⟩ <;> rcases bp with _ | ⟨y, ys⟩
    · rfl
    · rfl
    · rfl
    · exact cmpIds_exact _ _
  simp only [compare, Compare.V1_1_0.compare, Compare.V1_0_0.compare, collides, hpre]
  by_cases h1 : a1 = b1
  · subst h1
    by_cases h2 : a2 = b2
    · subst h2
      by_cases h3 : a3 = b3
      · subst h3
        simp only [cmpNat, Nat.lt_irrefl, ite_false, ite_true, Ordering.eq_then, beq_self_eq_true,
          Bool.true_and]
        split <;> simp_all
      · have := cmpNat_ne_eq a3 b3 h3
        have ht : ∀ o, (cmpNat a3 b3).then o = cmpNat a3 b3 := by
          intro o; revert this; cases cmpNat a3 b3 <;> simp [Ordering.then]
        rw [ht, ht]; simp [h3]
    · have := cmpNat_ne_eq a2 b2 h2
      have ht : ∀ o, (cmpNat a2 b2).then o = cmpNat a2 b2 := by
        intro o; revert this; cases cmpNat a2 b2 <;> simp [Ordering.then]
      rw [ht, ht]; simp [h2]
  · have := cmpNat_ne_eq a1 b1 h1
    have ht : ∀ o, (cmpNat a1 b1).then o = cmpNat a1 b1 := by
      intro o; revert this; cases cmpNat a1 b1 <;> simp [Ordering.then]
    rw [ht, ht]; simp [h1]

theorem firstDiff_mem (as bs : List Ident) (p q : Ident) (h : firstDiff as bs = some (p, q)) :
    p ∈ as ∧ q ∈ bs ∧ p ≠ q := by
  induction as generalizing bs with
  | nil => simp [firstDiff_nil_left] at h
  | cons a as ih =>
    cases bs with
    | nil => simp [firstDiff] at h
    | cons b bs =>
      simp only [firstDiff] at h
      split at h
      · obtain ⟨h1, h2, h3⟩ := ih bs h
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3⟩
      · cases h; exact ⟨List.mem_cons_self, List.mem_cons_self, ‹_›⟩

/-- Every numeric pre-release identifier is below 2^53 (JavaScript represents it exactly). -/
def smallIds (v : Version) : Prop := ∀ n, Ident.num n ∈ v.pre → n < 2 ^ 53

/-- Where every numeric pre-release identifier is below 2^53, the package compares exactly as
the contract. -/
theorem agrees (a b : Version) (ha : smallIds a) (hb : smallIds b) :
    compare a b = Compare.V1_1_0.compare a b := by
  rw [compare_exact]
  have : collides a b = false := by
    unfold collides
    split
    · rename_i x y hd
      obtain ⟨hx, hy, hxy⟩ := firstDiff_mem _ _ _ _ hd
      rw [toDouble_small x (ha x hx), toDouble_small y (hb y hy)]
      have : x ≠ y := fun e => hxy (e ▸ rfl)
      simp [this]
    · simp
  simp [this]

/-- Witness: `1.0.0-9007199254740993` and `1.0.0-9007199254740992` compare equal (both become the
double 2^53), where the contract ranks the first higher. -/
theorem dev_rounded_ids :
    compare ⟨1, 0, 0, [.num 9007199254740993], []⟩ ⟨1, 0, 0, [.num 9007199254740992], []⟩ = .eq ∧
    Compare.V1_1_0.compare ⟨1, 0, 0, [.num 9007199254740993], []⟩
      ⟨1, 0, 0, [.num 9007199254740992], []⟩ = .gt := by decide

end Fvdep.Profiles.NpmSemver.V7_7_3
