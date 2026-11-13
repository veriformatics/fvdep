/-! Library identifiers (contract `docs/contracts/U2-core.md` I1–I6; `docs/library.md` Naming):
module ids, entry versions + their order, Lean module names, module references, reserved consumer
module names, commit ids. Text is handled as `List Char`; a parser accepts a text only when its
value prints back to exactly that text, so every accepted text is canonical by construction, and the
theorems are the round trips + injectivity. Id characters are finite symbols (`Sym`), so
per-character facts are decided over 36 values. -/

namespace FvdepCore.Ids

/-! ## Symbols + segments -/

/-- An id character: 0–25 = `a`–`z`, 26–35 = `0`–`9`. -/
abbrev Sym := Fin 36

def Sym.char (s : Sym) : Char :=
  if s.val < 26 then Char.ofNat (97 + s.val) else Char.ofNat (22 + s.val)

/-- The upper-case letter of a segment head (`docs/library.md`: UpperCamelCase). -/
def capital (h : Fin 26) : Char := Char.ofNat (65 + h.val)

def Sym.ofChar? (c : Char) : Option Sym :=
  if h : 97 ≤ c.toNat ∧ c.toNat ≤ 122 then some ⟨c.toNat - 97, by omega⟩
  else if h : 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some ⟨c.toNat - 22, by omega⟩ else none

/-- The symbol `c` spells (canonical: it prints back to `c`). -/
def Sym.parse (c : Char) : Option Sym := (Sym.ofChar? c).filter fun s => s.char == c

theorem Sym.ofChar?_char : ∀ s : Sym, Sym.ofChar? s.char = some s := by decide

theorem Sym.parse_char (s : Sym) : Sym.parse s.char = some s := by
  simp [Sym.parse, Sym.ofChar?_char s]

theorem Sym.char_of_parse {c : Char} {s : Sym} (h : Sym.parse c = some s) : s.char = c := by
  unfold Sym.parse at h
  cases hc : Sym.ofChar? c with
  | none => simp [hc] at h
  | some t =>
    simp only [hc, Option.filter_some] at h
    split at h
    · cases h
      simp_all
    · cases h

/-- No id symbol is `.` or `_`, and none is an upper-case letter. -/
theorem Sym.char_ne :
    ∀ s : Sym,
      s.char ≠ '.' ∧ s.char ≠ '_' ∧ s.char ≠ '@' ∧ ¬(65 ≤ s.char.toNat ∧ s.char.toNat ≤ 90) := by
  decide

theorem Sym.char_sep (s : Sym) (c : Char) (hc : c = '.' ∨ c = '_' ∨ c = '@') : s.char ≠ c := by
  have := Sym.char_ne s
  rcases hc with rfl | rfl | rfl <;> simp_all

theorem capital_ne :
    ∀ h : Fin 26,
      capital h ≠ '.' ∧ capital h ≠ '_' ∧ 65 ≤ (capital h).toNat ∧ (capital h).toNat ≤ 90 := by
  decide

theorem capital_inj : ∀ a b : Fin 26, capital a = capital b → a = b := by decide

theorem Sym.char_inj : ∀ a b : Sym, a.char = b.char → a = b := by decide

/-- `[a-z][a-z0-9]*`: a head letter + tail symbols. -/
structure Seg where
  head : Fin 26
  tail : List Sym
  deriving DecidableEq, Repr

def Seg.chars (g : Seg) : List Char := Sym.char ⟨g.head.val, by omega⟩ :: g.tail.map Sym.char

/-- The segment as an UpperCamelCase word (Lean module name part). -/
def Seg.camel (g : Seg) : List Char := capital g.head :: g.tail.map Sym.char

def Seg.parse : List Char → Option Seg
  | [] => none
  | c :: cs =>
    match Sym.parse c, cs.mapM Sym.parse with
    | some h, some t => if hh : h.val < 26 then some ⟨⟨h.val, hh⟩, t⟩ else none
    | _, _ => none

theorem mapM_parse_map (t : List Sym) : (t.map Sym.char).mapM Sym.parse = some t := by
  induction t with
  | nil => rfl
  | cons s t ih => simp [List.mapM_cons, Sym.parse_char, ih]

theorem map_of_mapM_parse {cs : List Char} {t : List Sym} (h : cs.mapM Sym.parse = some t) :
    t.map Sym.char = cs := by
  induction cs generalizing t with
  | nil =>
    simp at h
    subst h
    rfl
  | cons c cs ih =>
    simp only [List.mapM_cons] at h
    cases hc : Sym.parse c with
    | none => simp [hc] at h
    | some s =>
      cases hr : cs.mapM Sym.parse with
      | none => simp [hc, hr] at h
      | some r =>
        simp [hc, hr] at h
        subst h
        simp [Sym.char_of_parse hc, ih hr]

theorem Seg.parse_chars (g : Seg) : Seg.parse g.chars = some g := by
  unfold Seg.chars
  simp only [Seg.parse, Sym.parse_char, mapM_parse_map, g.head.isLt, ↓reduceDIte]

theorem Seg.chars_of_parse {cs : List Char} {g : Seg} (h : Seg.parse cs = some g) :
    g.chars = cs := by
  cases cs with
  | nil => simp [Seg.parse] at h
  | cons c cs =>
    simp only [Seg.parse] at h
    cases hc : Sym.parse c with
    | none => simp [hc] at h
    | some s =>
      cases hr : cs.mapM Sym.parse with
      | none => simp [hc, hr] at h
      | some t =>
        simp only [hc, hr] at h
        split at h
        · cases h
          simp [Seg.chars, Sym.char_of_parse hc, map_of_mapM_parse hr]
        · cases h

/-! ## Cutting text at a separator -/

/-- `cs` cut at every `sep`: the pieces between them (one piece when `sep` never occurs). -/
def cut (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: cut sep cs
    else
      match cut sep cs with
      | p :: ps => (c :: p) :: ps
      | [] => [[c]]

/-- Pieces joined with `sep` between them. -/
def join (sep : Char) : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: ps => p ++ sep :: join sep ps

theorem cut_ne_nil (sep : Char) (cs : List Char) : cut sep cs ≠ [] := by
  cases cs with
  | nil => simp [cut]
  | cons c cs =>
    unfold cut
    split
    · simp
    · split <;> simp

/-- A piece free of `sep`, then `sep` + the rest: the cut starts with that piece. -/
theorem cut_append (sep : Char) (p rest : List Char) (hp : sep ∉ p) :
    cut sep (p ++ sep :: rest) = p :: cut sep rest := by
  induction p with
  | nil => simp [cut]
  | cons c p ih =>
    have hc : c ≠ sep := fun h => hp (h ▸ List.mem_cons_self ..)
    have hp' : sep ∉ p := fun h => hp (List.mem_cons_of_mem _ h)
    simp only [List.cons_append, cut, hc, ↓reduceIte, ih hp']

theorem cut_free (sep : Char) (p : List Char) (hp : sep ∉ p) : cut sep p = [p] := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    have hc : c ≠ sep := fun h => hp (h ▸ List.mem_cons_self ..)
    have hp' : sep ∉ p := fun h => hp (List.mem_cons_of_mem _ h)
    simp only [cut, hc, ↓reduceIte, ih hp']

theorem cut_join (sep : Char) (ps : List (List Char)) (hne : ps ≠ []) (hfree : ∀ p ∈ ps, sep ∉ p) :
    cut sep (join sep ps) = ps := by
  induction ps with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    cases ps with
    | nil => simp [join, cut_free sep p (hfree p (by simp))]
    | cons q qs =>
      simp only [join]
      rw [cut_append sep p _ (hfree p (by simp)), ih (by simp) (fun x hx => hfree x (by simp [hx]))]

theorem join_cut (sep : Char) (cs : List Char) : join sep (cut sep cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    unfold cut
    split
    · rename_i h
      have hn := cut_ne_nil sep cs
      cases hcut : cut sep cs with
      | nil => exact absurd hcut hn
      | cons p ps =>
        rw [hcut] at ih
        simp [join, ih, h]
    · split
      · rename_i p ps hcut
        rw [hcut] at ih
        cases ps with
        | nil => simp_all [join]
        | cons q qs => simp_all [join]
      · rename_i hcut
        exact absurd hcut (cut_ne_nil sep cs)

theorem Seg.char_free (g : Seg) (c : Char) (hc : c = '.' ∨ c = '_' ∨ c = '@') : c ∉ g.chars := by
  intro hm
  simp only [Seg.chars, List.mem_cons, List.mem_map] at hm
  rcases hm with h | ⟨s, _, h⟩
  · exact Sym.char_sep _ c hc h.symm
  · exact Sym.char_sep s c hc h

theorem join_free (sep c : Char) (hc : c ≠ sep) (ps : List (List Char)) (h : ∀ p ∈ ps, c ∉ p) :
    c ∉ join sep ps := by
  induction ps with
  | nil => simp [join]
  | cons p ps ih =>
    cases ps with
    | nil => simpa [join] using h p (by simp)
    | cons q qs =>
      simp only [join, List.mem_append, List.mem_cons, not_or]
      exact ⟨h p (by simp), hc, ih (fun x hx => h x (by simp_all))⟩

theorem mapM_seg_parse (gs : List Seg) : (gs.map Seg.chars).mapM Seg.parse = some gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [List.mapM_cons, Seg.parse_chars, ih]

/-! ## Canonical parsing -/

/-- `rough`'s value, accepted only when it prints back to exactly `cs`. -/
def canon {α : Type} (print : α → List Char) (cs : List Char) (rough : Option α) : Option α :=
  rough.filter fun a => print a == cs

theorem canon_print {α : Type} {print : α → List Char} {cs : List Char} {rough : Option α} {a : α}
    (h : canon print cs rough = some a) : print a = cs := by
  unfold canon at h
  cases rough with
  | none => simp at h
  | some b =>
    simp only [Option.filter_some] at h
    split at h
    · cases h
      simp_all
    · cases h

theorem canon_some {α : Type} (print : α → List Char) (a : α) :
    canon print (print a) (some a) = some a := by simp [canon]

/-! ## I1 module ids -/

/-- `<dep>.<op>`: `dep` one segment, `op` = `op₀ :: ops` joined by `_`. -/
structure ModuleId where
  dep : Seg
  op₀ : Seg
  ops : List Seg
  deriving DecidableEq, Repr

def ModuleId.chars (m : ModuleId) : List Char :=
  m.dep.chars ++ '.' :: join '_' ((m.op₀ :: m.ops).map Seg.chars)

def ModuleId.rough (cs : List Char) : Option ModuleId :=
  match cut '.' cs with
  | [d, o] =>
    match Seg.parse d, (cut '_' o).mapM Seg.parse with
    | some dep, some (op₀ :: ops) => some ⟨dep, op₀, ops⟩
    | _, _ => none
  | _ => none

def ModuleId.parseChars (cs : List Char) : Option ModuleId :=
  canon ModuleId.chars cs (ModuleId.rough cs)

def ModuleId.parse (s : String) : Option ModuleId := ModuleId.parseChars s.toList

instance : ToString ModuleId where
  toString m := String.ofList m.chars

theorem ModuleId.rough_chars (m : ModuleId) : ModuleId.rough m.chars = some m := by
  have hfree :
    ∀ c, (c = '.' ∨ c = '_' ∨ c = '@') → ∀ p ∈ (m.op₀ :: m.ops).map Seg.chars, c ∉ p := by
    intro c hc p hp
    simp only [List.mem_map] at hp
    obtain ⟨g, _, rfl⟩ := hp
    exact Seg.char_free g c hc
  have hcut : cut '.' m.chars = [m.dep.chars, join '_' ((m.op₀ :: m.ops).map Seg.chars)] := by
    unfold ModuleId.chars
    rw [cut_append _ _ _ (Seg.char_free _ _ (.inl rfl))]
    rw [cut_free _ _ (join_free '_' '.' (by decide) _ (hfree '.' (.inl rfl)))]
  unfold ModuleId.rough
  rw [hcut]
  simp only [Seg.parse_chars]
  rw [cut_join '_' _ (by simp) (hfree '_' (.inr (.inl rfl))), mapM_seg_parse]

/-- I1: printing then parsing gives the id back. -/
theorem ModuleId.parse_toString (m : ModuleId) : ModuleId.parse (toString m) = some m := by
  simp only [ModuleId.parse, toString, String.toList_ofList, ModuleId.parseChars,
    ModuleId.rough_chars, canon_some]

/-- I1: a parsed id prints back to exactly the text. -/
theorem ModuleId.toString_parse {s : String} {m : ModuleId} (h : ModuleId.parse s = some m) :
    toString m = s := by
  have := canon_print h
  simp only [toString, this, String.ofList_toList]

/-! ## I2 entry versions -/

def digit (d : Nat) : Char := Char.ofNat (48 + d)

theorem digit_toNat : ∀ d : Fin 10, (digit d.val).toNat = 48 + d.val := by decide

theorem digit_ne : ∀ d : Fin 10, digit d.val ≠ '.' ∧ digit d.val ≠ '_' ∧ digit d.val ≠ '@' := by
  decide

/-- Decimal digits, most significant first, no leading zero. -/
def decimal (n : Nat) : List Char :=
  if n < 10 then [digit n] else decimal (n / 10) ++ [digit (n % 10)]
termination_by n
decreasing_by omega

def value (cs : List Char) : Nat := cs.foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0

theorem value_append (cs : List Char) (c : Char) :
    value (cs ++ [c]) = 10 * value cs + (c.toNat - 48) := by simp [value, List.foldl_append]

theorem value_decimal (n : Nat) : value (decimal n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold decimal
    split
    · rename_i h
      have := digit_toNat ⟨n, h⟩
      simp only [value, List.foldl_cons, List.foldl_nil]
      simp at this
      omega
    · rename_i h
      have hd := digit_toNat ⟨n % 10, Nat.mod_lt _ (by omega)⟩
      simp only at hd
      rw [value_append, ih (n / 10) (by omega), hd]
      omega

theorem decimal_free (n : Nat) (c : Char) (hc : c = '.' ∨ c = '_' ∨ c = '@') : c ∉ decimal n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold decimal
    have hdig : ∀ d, d < 10 → digit d ≠ c := by
      intro d hd
      have := digit_ne ⟨d, hd⟩
      rcases hc with rfl | rfl | rfl <;> simp_all
    split
    · rename_i h
      simp only [List.mem_singleton]
      exact fun e => hdig n h e.symm
    · rename_i h
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨ih (n / 10) (by omega), fun e => hdig (n % 10) (Nat.mod_lt _ (by omega)) e.symm⟩

/-- A canonical decimal: no sign, no leading zero, digits alone. -/
def parseNat (cs : List Char) : Option Nat := canon decimal cs (some (value cs))

theorem parseNat_decimal (n : Nat) : parseNat (decimal n) = some n := by
  simp [parseNat, canon, value_decimal]

/-- `x.y.z` (`docs/library.md`: three decimal numbers without leading zeros). -/
structure EntryVersion where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr

def EntryVersion.chars (v : EntryVersion) : List Char :=
  decimal v.major ++ '.' :: (decimal v.minor ++ '.' :: decimal v.patch)

def EntryVersion.rough (cs : List Char) : Option EntryVersion :=
  match cut '.' cs with
  | [a, b, c] =>
    match parseNat a, parseNat b, parseNat c with
    | some x, some y, some z => some ⟨x, y, z⟩
    | _, _, _ => none
  | _ => none

def EntryVersion.parseChars (cs : List Char) : Option EntryVersion :=
  canon EntryVersion.chars cs (EntryVersion.rough cs)

def EntryVersion.parse (s : String) : Option EntryVersion := EntryVersion.parseChars s.toList

instance : ToString EntryVersion where
  toString v := String.ofList v.chars

theorem EntryVersion.rough_chars (v : EntryVersion) : EntryVersion.rough v.chars = some v := by
  unfold EntryVersion.rough EntryVersion.chars
  rw [cut_append _ _ _ (decimal_free _ _ (.inl rfl)),
    cut_append _ _ _ (decimal_free _ _ (.inl rfl)), cut_free _ _ (decimal_free _ _ (.inl rfl))]
  simp [parseNat_decimal]

/-- I2: printing then parsing gives the version back. -/
theorem EntryVersion.parse_toString (v : EntryVersion) :
    EntryVersion.parse (toString v) = some v := by
  simp only [EntryVersion.parse, toString, String.toList_ofList, EntryVersion.parseChars,
    EntryVersion.rough_chars, canon_some]

/-- I2: a parsed version prints back to exactly the text. -/
theorem EntryVersion.toString_parse {s : String} {v : EntryVersion}
    (h : EntryVersion.parse s = some v) : toString v = s := by
  have := canon_print h
  simp only [toString, this, String.ofList_toList]

/-- Numeric order by field: major, then minor, then patch. -/
def EntryVersion.le (a b : EntryVersion) : Prop :=
  a.major < b.major ∨
    a.major = b.major ∧ (a.minor < b.minor ∨ a.minor = b.minor ∧ a.patch ≤ b.patch)

def cmp3 (a b : Nat) : Ordering := if a < b then .lt else if a = b then .eq else .gt

def EntryVersion.cmp (a b : EntryVersion) : Ordering :=
  match cmp3 a.major b.major with
  | .eq =>
    match cmp3 a.minor b.minor with
    | .eq => cmp3 a.patch b.patch
    | o => o
  | o => o

theorem cmp3_spec (a b : Nat) :
    (cmp3 a b = .lt ↔ a < b) ∧ (cmp3 a b = .eq ↔ a = b) ∧ (cmp3 a b = .gt ↔ b < a) := by
  unfold cmp3
  split
  · simp
    omega
  · split
    · simp
      omega
    · simp
      omega

instance : Ord EntryVersion where
  compare := EntryVersion.cmp

theorem EntryVersion.le_total (a b : EntryVersion) : a.le b ∨ b.le a := by
  unfold EntryVersion.le
  omega

theorem EntryVersion.le_antisymm (a b : EntryVersion) (h₁ : a.le b) (h₂ : b.le a) : a = b := by
  cases a
  cases b
  unfold EntryVersion.le at h₁ h₂
  simp only [EntryVersion.mk.injEq] at h₁ h₂ ⊢
  omega

theorem EntryVersion.le_trans (a b c : EntryVersion) (h₁ : a.le b) (h₂ : b.le c) : a.le c := by
  unfold EntryVersion.le at *
  omega

/-- `compare` agrees with the order: not greater ↔ `le`; equal ↔ equal versions. -/
theorem EntryVersion.cmp_spec (a b : EntryVersion) :
    (EntryVersion.cmp a b ≠ .gt ↔ a.le b) ∧ (EntryVersion.cmp a b = .eq ↔ a = b) := by
  cases a with
  | mk x y z =>
    cases b with
    | mk x' y' z' =>
      have h₁ := cmp3_spec x x'
      have h₂ := cmp3_spec y y'
      have h₃ := cmp3_spec z z'
      simp only [EntryVersion.cmp, EntryVersion.le, EntryVersion.mk.injEq]
      cases hx : cmp3 x x' <;> cases hy : cmp3 y y' <;> cases hz : cmp3 z z' <;> simp_all

/-! ## I3 Lean module names -/

def camelAll (gs : List Seg) : List Char := gs.flatMap Seg.camel

theorem capital_ne_sym (h : Fin 26) (s : Sym) : capital h ≠ s.char := by
  intro e
  have hc := (capital_ne h).2.2
  have hs := (Sym.char_ne s).2.2.2
  rw [e] at hc
  exact hs hc

/-- Tail symbols never run into the next segment: a camel word starts with a capital. -/
theorem tail_inj (t t' : List Sym) (gs gs' : List Seg)
    (h : t.map Sym.char ++ camelAll gs = t'.map Sym.char ++ camelAll gs') :
    t = t' ∧ camelAll gs = camelAll gs' := by
  induction t generalizing t' with
  | nil =>
    cases t' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons s' ts' =>
      cases gs with
      | nil => simp [camelAll] at h
      | cons g
        gs =>
        simp only [camelAll, List.flatMap_cons, Seg.camel, List.map_cons, List.map_nil,
          List.nil_append, List.cons_append, List.cons.injEq] at h
        exact absurd h.1 (capital_ne_sym _ _)
  | cons s ts ih =>
    cases t' with
    | nil =>
      cases gs' with
      | nil => simp [camelAll] at h
      | cons g
        gs' =>
        simp only [camelAll, List.flatMap_cons, Seg.camel, List.map_cons, List.map_nil,
          List.nil_append, List.cons_append, List.cons.injEq] at h
        exact absurd h.1.symm (capital_ne_sym _ _)
    | cons s' ts' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rest⟩ := ih ts' h.2
      exact ⟨by rw [Sym.char_inj _ _ h.1], rest⟩

theorem camelAll_inj (gs gs' : List Seg) (h : camelAll gs = camelAll gs') : gs = gs' := by
  induction gs generalizing gs' with
  | nil =>
    cases gs' with
    | nil => rfl
    | cons g' gs' => simp [camelAll, Seg.camel] at h
  | cons g gs ih =>
    cases gs' with
    | nil => simp [camelAll, Seg.camel] at h
    | cons g'
      gs' =>
      simp only [camelAll, List.flatMap_cons, Seg.camel, List.cons_append, List.cons.injEq] at h
      obtain ⟨ht, hr⟩ := tail_inj g.tail g'.tail gs gs' h.2
      have hh := capital_inj _ _ h.1
      cases g
      cases g'
      simp_all [ih gs' hr]

theorem decimal_inj {a b : Nat} (h : decimal a = decimal b) : a = b := by
  rw [← value_decimal a, ← value_decimal b, h]

/-- The `V<x>_<y>_<z>` part of a Lean module name. -/
def vPart (v : EntryVersion) : List Char :=
  'V' :: (decimal v.major ++ '_' :: (decimal v.minor ++ '_' :: decimal v.patch))

theorem vPart_inj {v v' : EntryVersion} (h : vPart v = vPart v') : v = v' := by
  simp only [vPart, List.cons.injEq, true_and] at h
  have hc := congrArg (cut '_') h
  rw [cut_append _ _ _ (decimal_free _ _ (.inr (.inl rfl))),
    cut_append _ _ _ (decimal_free _ _ (.inr (.inl rfl))),
    cut_free _ _ (decimal_free _ _ (.inr (.inl rfl))),
    cut_append _ _ _ (decimal_free _ _ (.inr (.inl rfl))),
    cut_append _ _ _ (decimal_free _ _ (.inr (.inl rfl))),
    cut_free _ _ (decimal_free _ _ (.inr (.inl rfl)))] at hc
  simp only [List.cons.injEq, and_true] at hc
  cases v
  cases v'
  simp only [EntryVersion.mk.injEq]
  exact ⟨decimal_inj hc.1, decimal_inj hc.2.1, decimal_inj hc.2.2⟩

/-- The Lean module of an entry (`docs/library.md`: `Fvdep.<Dep>.<Op>.V<x>_<y>_<z>`). -/
def leanModule (m : ModuleId) (v : EntryVersion) : Lean.Name :=
  .str
    (.str (.str (.str .anonymous "Fvdep") (String.ofList m.dep.camel))
      (String.ofList (camelAll (m.op₀ :: m.ops))))
    (String.ofList (vPart v))

/-- I3: distinct entries never share a Lean module. -/
theorem leanModule_inj {m m' : ModuleId} {v v' : EntryVersion}
    (h : leanModule m v = leanModule m' v') : m = m' ∧ v = v' := by
  simp only [leanModule, Lean.Name.str.injEq, String.ofList_inj, true_and] at h
  obtain ⟨⟨hd, ho⟩, hv⟩ := h
  have hdep : m.dep = m'.dep := by
    have := camelAll_inj [m.dep] [m'.dep] (by simpa [camelAll] using hd)
    simpa using this
  have hops := camelAll_inj _ _ ho
  simp only [List.cons.injEq] at hops
  cases m
  cases m'
  simp_all [vPart_inj hv]

/-! ## I4 module references -/

/-- `<id>` or `<id>@<x.y.z>` (CLI arguments: `docs/interface.md` §3). -/
structure ModuleRef where
  id : ModuleId
  version : Option EntryVersion
  deriving DecidableEq, Repr

def ModuleRef.chars (r : ModuleRef) : List Char :=
  match r.version with
  | none => r.id.chars
  | some v => r.id.chars ++ '@' :: v.chars

def ModuleRef.rough (cs : List Char) : Option ModuleRef :=
  match cut '@' cs with
  | [a] => (ModuleId.parseChars a).map fun m => ⟨m, none⟩
  | [a, b] =>
    match ModuleId.parseChars a, EntryVersion.parseChars b with
    | some m, some v => some ⟨m, some v⟩
    | _, _ => none
  | _ => none

def ModuleRef.parseChars (cs : List Char) : Option ModuleRef :=
  canon ModuleRef.chars cs (ModuleRef.rough cs)

def ModuleRef.parse (s : String) : Option ModuleRef := ModuleRef.parseChars s.toList

instance : ToString ModuleRef where
  toString r := String.ofList r.chars

theorem ModuleId.at_free (m : ModuleId) : '@' ∉ m.chars := by
  simp only [ModuleId.chars, List.mem_append, List.mem_cons, not_or]
  refine ⟨Seg.char_free _ _ (.inr (.inr rfl)), by decide, join_free '_' '@' (by decide) _ ?_⟩
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨g, _, rfl⟩ := hp
  exact Seg.char_free g _ (.inr (.inr rfl))

theorem EntryVersion.at_free (v : EntryVersion) : '@' ∉ v.chars := by
  simp only [EntryVersion.chars, List.mem_append, List.mem_cons, not_or]
  exact
    ⟨decimal_free _ _ (.inr (.inr rfl)), by decide, decimal_free _ _ (.inr (.inr rfl)), by decide,
      decimal_free _ _ (.inr (.inr rfl))⟩

theorem ModuleRef.rough_chars (r : ModuleRef) : ModuleRef.rough r.chars = some r := by
  cases r with
  | mk m v =>
    cases v with
    | none =>
      simp [ModuleRef.rough, ModuleRef.chars, cut_free _ _ (ModuleId.at_free m),
        ModuleId.parseChars, ModuleId.rough_chars, canon_some]
    | some v =>
      simp [ModuleRef.rough, ModuleRef.chars, cut_append _ _ _ (ModuleId.at_free m),
        cut_free _ _ (EntryVersion.at_free v), ModuleId.parseChars, ModuleId.rough_chars,
        EntryVersion.parseChars, EntryVersion.rough_chars, canon_some]

/-- I4: printing then parsing gives the reference back. -/
theorem ModuleRef.parse_toString (r : ModuleRef) : ModuleRef.parse (toString r) = some r := by
  simp only [ModuleRef.parse, toString, String.toList_ofList, ModuleRef.parseChars,
    ModuleRef.rough_chars, canon_some]

/-- I4: a parsed reference prints back to exactly the text. -/
theorem ModuleRef.toString_parse {s : String} {r : ModuleRef} (h : ModuleRef.parse s = some r) :
    toString r = s := by
  have := canon_print h
  simp only [toString, this, String.ofList_toList]

/-! ## I5 reserved consumer module names -/

/-- The first component of a name. -/
def rootName : Lean.Name → Lean.Name
  | .anonymous => .anonymous
  | .str .anonymous s => .str .anonymous s
  | .num .anonymous n => .num .anonymous n
  | .str p _ => rootName p
  | .num p _ => rootName p

/-- The first component is `Init`, `Std`, `Lean` or `Lake`, or starts with `Fvdep` (fvdep's
libraries + tool; `docs/library.md` Naming). -/
def reserved (n : Lean.Name) : Bool :=
  match rootName n with
  | .str .anonymous s => ["Init", "Std", "Lean", "Lake"].contains s || s.startsWith "Fvdep"
  | _ => false

/-- I5: a one-component name is reserved by its spelling alone. -/
theorem reserved_root (s : String) :
    reserved (.str .anonymous s) =
      (["Init", "Std", "Lean", "Lake"].contains s || s.startsWith "Fvdep") := by
  rfl

/-- I5: a longer name is reserved iff its prefix is (only the first component counts). -/
theorem reserved_str (p : Lean.Name) (s : String) (hp : p ≠ .anonymous) :
    reserved (.str p s) = reserved p := by
  cases p with
  | anonymous => exact absurd rfl hp
  | str q t => rfl
  | num q k => rfl

/-- I5: a numeric component after the first never decides either. -/
theorem reserved_num (p : Lean.Name) (k : Nat) (hp : p ≠ .anonymous) :
    reserved (.num p k) = reserved p := by
  cases p with
  | anonymous => exact absurd rfl hp
  | str q t => rfl
  | num q j => rfl

/-- I5: the empty name is never reserved. -/
theorem reserved_anonymous : reserved .anonymous = false := rfl

/-- I5: a numeric first component is never reserved. -/
theorem reserved_num_root (k : Nat) : reserved (.num .anonymous k) = false := rfl

/-! ## I6 commits -/

def hexChar (d : Fin 16) : Char :=
  if d.val < 10 then Char.ofNat (48 + d.val) else Char.ofNat (87 + d.val)

def hexOf? (c : Char) : Option (Fin 16) :=
  if h : 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some ⟨c.toNat - 48, by omega⟩
  else if h : 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some ⟨c.toNat - 87, by omega⟩ else none

theorem hexOf?_char : ∀ d : Fin 16, hexOf? (hexChar d) = some d := by decide

theorem mapM_hex (ds : List (Fin 16)) : (ds.map hexChar).mapM hexOf? = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [List.mapM_cons, hexOf?_char, ih]

/-- A library commit: 40 lowercase hexadecimal digits. -/
structure Commit where
  digits : List (Fin 16)
  length_eq : digits.length = 40
  deriving DecidableEq

def Commit.chars (c : Commit) : List Char := c.digits.map hexChar

def Commit.rough (cs : List Char) : Option Commit :=
  match cs.mapM hexOf? with
  | some ds => if h : ds.length = 40 then some ⟨ds, h⟩ else none
  | none => none

def Commit.parseChars (cs : List Char) : Option Commit := canon Commit.chars cs (Commit.rough cs)

def Commit.parse (s : String) : Option Commit := Commit.parseChars s.toList

instance : ToString Commit where
  toString c := String.ofList c.chars

theorem Commit.rough_chars (c : Commit) : Commit.rough c.chars = some c := by
  cases c with
  | mk ds hl =>
    simp only [Commit.rough, Commit.chars]
    rw [mapM_hex]
    simp [hl]

/-- I6: printing then parsing gives the commit back. -/
theorem Commit.parse_toString (c : Commit) : Commit.parse (toString c) = some c := by
  simp only [Commit.parse, toString, String.toList_ofList, Commit.parseChars, Commit.rough_chars,
    canon_some]

/-- I6: a parsed commit prints back to exactly the text. -/
theorem Commit.toString_parse {s : String} {c : Commit} (h : Commit.parse s = some c) :
    toString c = s := by
  have := canon_print h
  simp only [toString, this, String.ofList_toList]

end FvdepCore.Ids
