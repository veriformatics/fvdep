import Fvdep.Semver.Version.V1_0_0

/-! Launch example (fvdep's qualification corpus, contract U6 Q; proved against the specs in U7):
SemVer 2.0.0 parsing field by field + precedence through an `Ord` instance on pre-release
identifiers and a lexicographic order. -/

namespace Launch.Semver

open Fvdep.Semver.Version.V1_0_0 (Ident Version)

/-- Lists in the first-difference order of `cmp`, a proper prefix first. -/
def lex {α : Type} (cmp : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmp a b).then (lex cmp as bs)

/-- §11.4.1–§11.4.3: numeric by value, numeric below alphanumeric, alphanumeric by code point. -/
def ident : Ident → Ident → Ordering
  | .num a, .num b => Ord.compare a b
  | .num _, .alnum _ => .lt
  | .alnum _, .num _ => .gt
  | .alnum a, .alnum b => lex (fun x y => Ord.compare x.toNat y.toNat) a b

instance : Ord Ident := ⟨ident⟩

/-- §11: major, minor, patch, then a version without pre-release identifiers above one with them,
then the identifiers left to right (build metadata ignored). -/
def compare (a b : Version) : Ordering :=
  (Ord.compare a.major b.major).then <|
    (Ord.compare a.minor b.minor).then <|
      (Ord.compare a.patch b.patch).then <|
        match a.pre, b.pre with
        | [], [] => .eq
        | [], _ :: _ => .gt
        | _ :: _, [] => .lt
        | p, q => lex Ord.compare p q

/-- `[0-9A-Za-z-]`. -/
def idChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- §2 + §9: a numeric identifier — digits without a leading zero, `0` itself aside. -/
def numeric? (s : List Char) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none
  else
    if 1 < s.length && s.head? == some '0' then none
    else some (s.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-- §9: one pre-release identifier (all digits ⇒ numeric). -/
def preIdent? (s : List Char) : Option Ident :=
  if s.isEmpty || !s.all idChar then none
  else
    if s.all Char.isDigit then (numeric? s).map Ident.num
    else some (.alnum s)

/-- `s` split at every `sep`. -/
def splitAt (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match splitAt sep cs with
    | p :: ps => if c == sep then [] :: p :: ps else (c :: p) :: ps
    | [] => [[c]]

/-- `s` before + after its first `sep`, if any. -/
def splitFirst (sep : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c == sep then ([], some cs)
    else
      let r := splitFirst sep cs
      (c :: r.1, r.2)

/-- §2, §9, §10: `X.Y.Z`, then `-` + dot-separated pre-release identifiers, then `+` + dot-separated
build identifiers (nonempty, `[0-9A-Za-z-]`). -/
def parse (s : List Char) : Option Version := do
  let (main, build) := splitFirst '+' s
  let (core, pre) := splitFirst '-' main
  let [ma, mi, pa] := splitAt '.' core | none
  let major ← numeric? ma
  let minor ← numeric? mi
  let patch ← numeric? pa
  let pre ←
    match pre with
    | none => pure []
    | some p => (splitAt '.' p).mapM preIdent?
  let build ←
    match build with
    | none => pure []
    | some b =>
      let ids := splitAt '.' b
      if ids.all fun i => !i.isEmpty && i.all idChar then pure ids else none
  pure ⟨major, minor, patch, pre, build⟩

end Launch.Semver
