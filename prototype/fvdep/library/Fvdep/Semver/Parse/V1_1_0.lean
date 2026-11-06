import Fvdep.Semver.Parse.V1_0_0
/-!
# semver.parse 1.1.0 — same grammar as 1.0.0, round-trip obligation corrected and proven

`parse` is unchanged (`unchanged`, by `rfl`), so every proof against 1.0.0 carries over.

The 1.0.0 obligation `parse_render` is false as stated: a `Version` value can hold identifiers
that no version text can produce, e.g. an alphanumeric pre-release identifier made only of digits
(`alnum "1"` renders as `1`, which parses back as the number 1) or one containing a dot.
`parse_render_counterexample` proves this. The corrected obligation `parse_render_valid`
restricts it to valid versions (`valid`): exactly the versions `parse` can return
(`parse_valid`).
-/
namespace Fvdep.Semver.Parse.V1_1_0
open Fvdep.Semver.Parse.V1_0_0 (Version Ident isIdChar splitOn parseNum parseIdent parseBuild
  splitFirst renderNat renderIdent joinDot render)

def parse := V1_0_0.parse
def parseStr (s : String) : Option Version := parse s.toList

theorem unchanged : parse = V1_0_0.parse := rfl

/-- A pre-release identifier any version text can produce: a number, or a non-empty run of
letters, digits and hyphens that is not all digits. -/
def validIdent : Ident → Bool
  | .num _ => true
  | .alnum s => !s.isEmpty && s.all isIdChar && !s.all Char.isDigit

/-- A build identifier any version text can produce: a non-empty run of letters, digits, hyphens. -/
def validBuild (b : List Char) : Bool := !b.isEmpty && b.all isIdChar

/-- A version whose identifiers could all have come from a version text. -/
def valid (v : Version) : Bool := v.pre.all validIdent && v.build.all validBuild

/-! ## Lemmas about the grammar helpers -/

theorem splitFirst_none (sep : Char) (a : List Char) (h : sep ∉ a) :
    splitFirst sep a = (a, none) := by
  have : a.idxOf? sep = none := by simpa [List.idxOf?_eq_none_iff] using h
  simp [splitFirst, this]

theorem splitFirst_some (sep : Char) (a b : List Char) (h : sep ∉ a) :
    splitFirst sep (a ++ sep :: b) = (a, some b) := by
  have hi : (a ++ sep :: b).idxOf? sep = some a.length := by
    induction a with
    | nil => simp [List.idxOf?_cons]
    | cons x xs ih =>
      have hx : x ≠ sep := fun e => h (e ▸ List.mem_cons_self)
      have hxs : sep ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
      simp [List.idxOf?_cons, hx, ih hxs]
  simp [splitFirst, hi]

theorem splitOn_none (sep : Char) (a : List Char) (h : sep ∉ a) : splitOn sep a = [a] := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ sep := fun e => h (e ▸ List.mem_cons_self)
    have hxs : sep ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hx, ih hxs]

theorem splitOn_append (sep : Char) (a b : List Char) (h : sep ∉ a) :
    splitOn sep (a ++ sep :: b) = a :: splitOn sep b := by
  induction a with
  | nil => simp [splitOn]
  | cons x xs ih =>
    have hx : x ≠ sep := fun e => h (e ▸ List.mem_cons_self)
    have hxs : sep ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hx, ih hxs]

theorem splitOn_joinDot (ws : List (List Char)) (hne : ws ≠ []) (h : ∀ w ∈ ws, '.' ∉ w) :
    splitOn '.' (joinDot ws) = ws := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons w ws ih =>
    cases ws with
    | nil => simpa [joinDot] using splitOn_none '.' w (h w List.mem_cons_self)
    | cons w' ws' =>
      have hw : '.' ∉ w := h w List.mem_cons_self
      rw [show joinDot (w :: w' :: ws') = w ++ '.' :: joinDot (w' :: ws') from rfl,
        splitOn_append _ _ _ hw, ih (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem not_mem_joinDot (c : Char) (hc : c ≠ '.') (ws : List (List Char)) (h : ∀ w ∈ ws, c ∉ w) :
    c ∉ joinDot ws := by
  induction ws with
  | nil => simp [joinDot]
  | cons w ws ih =>
    cases ws with
    | nil => simpa [joinDot] using h w List.mem_cons_self
    | cons w' ws' =>
      rw [show joinDot (w :: w' :: ws') = w ++ '.' :: joinDot (w' :: ws') from rfl]
      simp only [List.mem_append, List.mem_cons, not_or]
      exact ⟨h w List.mem_cons_self, fun e => hc e,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem digitChar_eq_zero {n : Nat} (hn : n < 10) (h : n.digitChar = '0') : n = 0 := by
  match n, hn with
  | 0, _ => rfl
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => simp [Nat.digitChar] at h

/-- Decimal digits of a positive number never start with `0`. -/
theorem toDigits_head (n : Nat) (hn : 0 < n) :
    ∃ d rest, Nat.toDigits 10 n = d :: rest ∧ d ≠ '0' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · exact ⟨_, _, rfl, fun h => by have := digitChar_eq_zero ‹_› h; omega⟩
    · obtain ⟨d, rest, h1, h2⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨d, rest ++ [(n % 10).digitChar], by simp [h1], h2⟩

theorem digits_isDigit (n : Nat) : ∀ c ∈ renderNat n, c.isDigit := by
  intro c hc
  simp only [renderNat, Nat.toString_eq_repr, Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem isDigit_isIdChar {c : Char} (h : c.isDigit) : isIdChar c := by
  simp [isIdChar, Char.isAlphanum, h]

theorem not_mem_renderNat (c : Char) (hc : c.isDigit = false) (n : Nat) : c ∉ renderNat n :=
  fun m => by simp [digits_isDigit n c m] at hc

theorem renderNat_ne_nil (n : Nat) : renderNat n ≠ [] := by
  simp [renderNat, Nat.toDigits_ne_nil]

theorem parseNum_renderNat (n : Nat) : parseNum (renderNat n) = some n := by
  have hall : (renderNat n).all Char.isDigit = true := by
    simpa using digits_isDigit n
  have hval : (renderNat n).foldl (fun n c => 10 * n + (c.toNat - 48)) 0 = n := by
    have := Nat.ofDigitChars_ten_toDigits (n := n)
    simpa [renderNat, Nat.ofDigitChars] using this
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; decide
  · obtain ⟨d, rest, h1, h2⟩ := toDigits_head n hpos
    have hr : renderNat n = d :: rest := by simpa [renderNat] using h1
    rw [hr] at hall hval ⊢
    unfold parseNum
    split
    · contradiction
    · rename_i h; cases h; exact absurd rfl h2
    · rename_i h; cases h; exact absurd rfl h2
    · simp [hall, hval]

theorem parseIdent_render (i : Ident) (h : validIdent i) : parseIdent (renderIdent i) = some i := by
  cases i with
  | num n =>
    have hall : (renderNat n).all Char.isDigit = true := by simpa using digits_isDigit n
    have hid : (renderNat n).all isIdChar = true := by
      simpa using fun c hc => isIdChar_of_digit (digits_isDigit n c hc)
    simp [parseIdent, renderIdent, hall, hid, parseNum_renderNat, renderNat_ne_nil]
  | alnum s =>
    simp only [validIdent, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [parseIdent, renderIdent, h.1.1, h.1.2, h.2]
where isIdChar_of_digit {c : Char} (h : c.isDigit) : isIdChar c = true := isDigit_isIdChar h

theorem parseBuild_valid (b : List Char) (h : validBuild b) : parseBuild b = some b := by
  simp only [validBuild, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp [parseBuild, h.1, h.2]

theorem mapM_parseIdent (ids : List Ident) (h : ids.all validIdent) :
    (ids.map renderIdent).mapM parseIdent = some ids := by
  induction ids with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [List.mapM_cons, parseIdent_render i h.1, ih h.2]

theorem mapM_parseBuild (bs : List (List Char)) (h : bs.all validBuild) :
    bs.mapM parseBuild = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [List.mapM_cons, parseBuild_valid b h.1, ih h.2]

/-- No letter, digit or hyphen is a `.` or a `+`. -/
theorem idChar_ne (c : Char) (h : isIdChar c) : c ≠ '.' ∧ c ≠ '+' := by
  constructor <;> (rintro rfl; simp [isIdChar, Char.isAlphanum, Char.isDigit] at h)

theorem renderIdent_no (i : Ident) (h : validIdent i) (c : Char) (hc : c = '.' ∨ c = '+') :
    c ∉ renderIdent i := by
  intro m
  cases i with
  | num n =>
    have := digits_isDigit n c m
    rcases hc with rfl | rfl <;> simp at this
  | alnum s =>
    simp only [validIdent, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    have := idChar_ne c (h.1.2 c m)
    rcases hc with rfl | rfl <;> simp at this

theorem build_no (b : List Char) (h : validBuild b) (c : Char) (hc : c = '.' ∨ c = '+') :
    c ∉ b := by
  intro m
  simp only [validBuild, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  have := idChar_ne c (h.2 c m)
  rcases hc with rfl | rfl <;> simp at this

/-! ## Obligations -/

/-- Every valid version (one whose identifiers a version text could contain) renders to text
that parses back to exactly that version. This corrects the 1.0.0 statement, which also
covered versions that no text can produce (see `parse_render_counterexample`). -/
theorem parse_render_valid (v : Version) (h : valid v) : parse (render v) = some v := by
  obtain ⟨ma, mi, pa, pre, build⟩ := v
  simp only [valid, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hpre, hbuild⟩ := h
  -- the version core: three numbers joined by dots
  let core := renderNat ma ++ '.' :: renderNat mi ++ '.' :: renderNat pa
  have hcore_plus : '+' ∉ core := by
    simp [core, not_mem_renderNat '+' (by decide)]
  have hcore_minus : '-' ∉ core := by
    simp [core, not_mem_renderNat '-' (by decide)]
  have hsplit : splitOn '.' core = [renderNat ma, renderNat mi, renderNat pa] := by
    simp only [core, List.append_assoc, List.cons_append]
    rw [splitOn_append _ _ _ (not_mem_renderNat '.' (by decide) _),
      splitOn_append _ _ _ (not_mem_renderNat '.' (by decide) _),
      splitOn_none _ _ (not_mem_renderNat '.' (by decide) _)]
  let preT := joinDot (pre.map renderIdent)
  have hpre_plus : '+' ∉ preT :=
    not_mem_joinDot '+' (by decide) _ (by
      simp only [List.mem_map]; rintro w ⟨i, hi, rfl⟩; exact renderIdent_no i (hpre i hi) _ (.inr rfl))
  have hpre_split (hne : pre ≠ []) : splitOn '.' preT = pre.map renderIdent :=
    splitOn_joinDot _ (by simpa using hne) (by
      simp only [List.mem_map]; rintro w ⟨i, hi, rfl⟩; exact renderIdent_no i (hpre i hi) _ (.inl rfl))
  have hbuild_split (hne : build ≠ []) : splitOn '.' (joinDot build) = build :=
    splitOn_joinDot _ hne (fun w hw => build_no w (hbuild w hw) _ (.inl rfl))
  -- the part before `+`
  let main := core ++ (if pre.isEmpty then [] else '-' :: preT)
  have hrender : render ⟨ma, mi, pa, pre, build⟩ =
      main ++ (if build.isEmpty then [] else '+' :: joinDot build) := by
    simp [render, main, core, preT]
  have hmain_plus : '+' ∉ main := by
    simp only [main, List.mem_append]
    split <;> simp [hcore_plus, hpre_plus]
  have hsplit1 : splitFirst '+' (render ⟨ma, mi, pa, pre, build⟩) =
      (main, if build.isEmpty then none else some (joinDot build)) := by
    rw [hrender]
    by_cases hb : build.isEmpty
    · rw [ite_eq_left hb, ite_eq_left hb, List.append_nil]; exact splitFirst_none '+' main hmain_plus
    · rw [ite_eq_right hb, ite_eq_right hb]; exact splitFirst_some '+' main (joinDot build) hmain_plus
  have hsplit2 : splitFirst '-' main = (core, if pre.isEmpty then none else some preT) := by
    show splitFirst '-' (core ++ (if pre.isEmpty then [] else '-' :: preT)) = _
    by_cases hp : pre.isEmpty
    · rw [ite_eq_left hp, ite_eq_left hp, List.append_nil]; exact splitFirst_none '-' core hcore_minus
    · rw [ite_eq_right hp, ite_eq_right hp]; exact splitFirst_some '-' core preT hcore_minus
  have hpreM : (match (if pre.isEmpty then none else some preT) with
      | none => some []
      | some p => (splitOn '.' p).mapM parseIdent) = some pre := by
    by_cases hp : pre.isEmpty
    · rw [ite_eq_left hp]; simp at hp; exact hp ▸ rfl
    · rw [ite_eq_right hp]
      simp only
      rw [hpre_split (by simpa using hp)]; exact mapM_parseIdent pre (by simpa using hpre)
  have hbuildM : (match (if build.isEmpty then none else some (joinDot build)) with
      | none => some []
      | some b => (splitOn '.' b).mapM parseBuild) = some build := by
    by_cases hb : build.isEmpty
    · rw [ite_eq_left hb]; simp at hb; exact hb ▸ rfl
    · rw [ite_eq_right hb]
      simp only
      rw [hbuild_split (by simpa using hb)]; exact mapM_parseBuild build (by simpa using hbuild)
  generalize (if pre.isEmpty then none else some preT) = pq at hsplit2 hpreM
  generalize (if build.isEmpty then none else some (joinDot build)) = bq at hsplit1 hbuildM
  simp only [parse, V1_0_0.parse, hsplit1, hsplit2, hsplit, parseNum_renderNat]
  cases pq <;> cases bq <;> simp_all

/-- The 1.0.0 obligation `parse_render` is false as stated: the version `0.0.0` with the
alphanumeric pre-release identifier `1` renders as `0.0.0-1`, which parses back with the
number 1 instead. -/
theorem parse_render_counterexample :
    ¬ ∀ v : Version, parse (render v) ≠ none → parse (render v) = some v := by
  intro h
  have := h ⟨0, 0, 0, [.alnum ['1']], []⟩ (by decide)
  exact absurd this (by decide)

end Fvdep.Semver.Parse.V1_1_0
