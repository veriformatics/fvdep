import FvdepCore.Ids
import FvdepCore.Json.Decode
import Lean.Expr

/-! The export reader (contract `docs/contracts/U5b-oracle.md` X1–X5): one `leanexport` run's bytes
(lean4export format 3.1.0 as Lean 4.35.0's bundled writer emits it) → the projection the oracle
reads (each declaration's name, kind, level params, type + value), every record validated in full.
Pure. The profile = the pinned writer's output: dense indices per table (names + levels from 1
after the predefined 0, exprs from 0), no `mdata`, J's bounds. Two stages per line: `parseLine`
(the record's exact layout over J's sorted members: keys, JSON types, spellings — no table read)
+ `apply` (density, references, declared names). Lines by offsets (`lineEnd`): an export may
reach T's `exportBytes` (default 128 MiB), so the reader never builds a byte list. -/

namespace FvdepCore.Export

open FvdepCore.Json

/-- X5: a refusal's class — the bytes break the format, or lie outside this reader's profile. -/
inductive Class where
  | malformed
  | profile
  deriving DecidableEq, Repr

/-- X5: the first violation in line order (line 1 = the header). -/
structure Refusal where
  line : Nat
  cls : Class
  reason : String
  deriving DecidableEq, Repr

/-- X4: a declaration's kind. -/
inductive Kind where
  | «axiom»
  | defn
  | thm
  | «opaque»
  | quot
  | induct
  | ctor
  | recursor
  deriving DecidableEq, Repr

/-- X4: one declaration as the oracle reads it. -/
structure Decl where
  name : Lean.Name
  kind : Kind
  levelParams : List Lean.Name
  type : Lean.Expr
  value : Option Lean.Expr

/-! ## Raw records: a line's typed layout, its references still indices -/

inductive NameF where
  | str (pre : Nat) (s : String)
  | num (pre : Nat) (i : Nat)
  deriving DecidableEq, Repr

inductive LevelF where
  | succ (l : Nat)
  | max (a b : Nat)
  | imax (a b : Nat)
  | param (n : Nat)
  deriving DecidableEq, Repr

inductive ExprF where
  | bvar (k : Nat)
  | sort (l : Nat)
  | const (n : Nat) (us : List Nat)
  | app (f a : Nat)
  | lam (n ty body : Nat) (bi : Lean.BinderInfo)
  | forallE (n ty body : Nat) (bi : Lean.BinderInfo)
  | letE (n ty v body : Nat) (nondep : Bool)
  | proj (typeName : Nat) (idx : Nat) (struct : Nat)
  | natVal (v : Nat)
  | strVal (s : String)
  deriving Repr

/-- X3: `def`'s reducibility hints (`regular`'s height = the format's 32-bit number). -/
inductive Hints where
  | «opaque»
  | abbrev
  | regular (k : UInt32)
  deriving DecidableEq, Repr

inductive Safety where
  | safe
  | «unsafe»
  | «partial»
  deriving DecidableEq, Repr

inductive QuotKind where
  | type
  | ctor
  | lift
  | ind
  deriving DecidableEq, Repr

/-- X3: an inductive block's type (fields in key order). -/
structure TypeF where
  all : List Nat
  ctors : List Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe : Bool
  levelParams : List Nat
  name : Nat
  numIndices : Nat
  numNested : Nat
  numParams : Nat
  type : Nat
  deriving DecidableEq, Repr

structure CtorF where
  cidx : Nat
  induct : Nat
  isUnsafe : Bool
  levelParams : List Nat
  name : Nat
  numFields : Nat
  numParams : Nat
  type : Nat
  deriving DecidableEq, Repr

structure RuleF where
  ctor : Nat
  nfields : Nat
  rhs : Nat
  deriving DecidableEq, Repr

structure RecF where
  all : List Nat
  isUnsafe : Bool
  k : Bool
  levelParams : List Nat
  name : Nat
  numIndices : Nat
  numMinors : Nat
  numMotives : Nat
  numParams : Nat
  rules : List RuleF
  type : Nat
  deriving DecidableEq, Repr

/-- X3: a declaration record (arguments in key order). -/
inductive DeclF where
  | «axiom» (isUnsafe : Bool) (levelParams : List Nat) (name type : Nat)
  |
  defn (all : List Nat) (hints : Hints) (levelParams : List Nat) (name : Nat) (safety : Safety)
    (type value : Nat)
  | thm (all levelParams : List Nat) (name type value : Nat)
  | «opaque» (all : List Nat) (isUnsafe : Bool) (levelParams : List Nat) (name type value : Nat)
  | quot (kind : QuotKind) (levelParams : List Nat) (name type : Nat)
  | induct (ctors : List CtorF) (recs : List RecF) (types : List TypeF)
  deriving DecidableEq, Repr

inductive Raw where
  | name (i : Nat) (f : NameF)
  | level (i : Nat) (f : LevelF)
  | expr (i : Nat) (f : ExprF)
  | decl (d : DeclF)
  deriving Repr

/-- A line's violation: its class + reason. -/
abbrev R := Except (Class × String)

def bad {α : Type} (why : String) : R α := .error (.malformed, why)

def outside {α : Type} (why : String) : R α := .error (.profile, why)

def need {α : Type} (what : String) : Option α → R α
  | some x => .ok x
  | none => bad s!"{what} has the wrong shape"

def natR (what : String) : Value → R Nat
  | .int n => if 0 ≤ n then .ok n.toNat else bad s!"{what} is negative"
  | _ => bad s!"{what} is not an integer"

def strR (what : String) : Value → R String
  | .str s => .ok s
  | _ => bad s!"{what} is not a string"

def boolR (what : String) : Value → R Bool
  | .bool b => .ok b
  | _ => bad s!"{what} is not a boolean"

def natsR (what : String) : Value → R (List Nat)
  | .arr xs => xs.mapM (natR what)
  | _ => bad s!"{what} is not an array"

/-! ## Stage 1: a line's layout (J's members ascend by key) -/

def nameF (k : String) (p : Value) : R NameF :=
  match k, p with
  | "str", .obj [("pre", pre), ("str", s)] =>
    return .str (← natR "a name prefix" pre) (← strR "a name" s)
  | "num", .obj [("i", i), ("pre", pre)] =>
    return .num (← natR "a name prefix" pre) (← natR "a number" i)
  | k, _ => bad s!"a name form {k} has the wrong shape"

def levelF (k : String) (p : Value) : R LevelF :=
  match k, p with
  | "succ", l => return .succ (← natR "a level" l)
  | "max", .arr [a, b] => return .max (← natR "a level" a) (← natR "a level" b)
  | "imax", .arr [a, b] => return .imax (← natR "a level" a) (← natR "a level" b)
  | "param", n => return .param (← natR "a level parameter" n)
  | k, _ => bad s!"a level form {k} has the wrong shape"

def binderInfoR : Value → R Lean.BinderInfo
  | .str "default" => .ok .default
  | .str "implicit" => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit" => .ok .instImplicit
  | _ => bad "a binder info has the wrong shape"

/-- X2: an expression form whose key sorts before `ie`. -/
def exprLo (k : String) (p : Value) : R ExprF :=
  match k, p with
  | "app", .obj [("arg", a), ("fn", f)] =>
    return .app (← natR "a function" f) (← natR "an argument" a)
  | "bvar", b => return .bvar (← natR "a bound variable" b)
  | "const", .obj [("name", n), ("us", us)] =>
    return .const (← natR "a constant's name" n) (← natsR "universe levels" us)
  | "forallE", .obj [("binderInfo", bi), ("body", b), ("name", n), ("type", ty)] =>
    return .forallE (← natR "a binder name" n) (← natR "a binder type" ty)
      (← natR "a binder body" b) (← binderInfoR bi)
  | k, _ => bad s!"an expression form {k} has the wrong shape"

/-- X2: an expression form whose key sorts after `ie`; `mdata` = outside the profile. -/
def exprHi (k : String) (p : Value) : R ExprF :=
  match k, p with
  | "lam", .obj [("binderInfo", bi), ("body", b), ("name", n), ("type", ty)] =>
    return .lam (← natR "a binder name" n) (← natR "a binder type" ty) (← natR "a binder body" b)
      (← binderInfoR bi)
  | "letE", .obj [("body", b), ("name", n), ("nondep", nd), ("type", ty), ("value", v)] =>
    return .letE (← natR "a let name" n) (← natR "a let type" ty) (← natR "a let value" v)
      (← natR "a let body" b) (← boolR "nondep" nd)
  | "mdata", _ => outside "metadata (the export step passes no --export-mdata)"
  | "natVal", .str s =>
    return .natVal (← need "a natural literal" (FvdepCore.Ids.parseNat s.toList))
  | "proj", .obj [("idx", i), ("struct", s), ("typeName", tn)] =>
    return .proj (← natR "a type name" tn) (← natR "a projection index" i) (← natR "a struct" s)
  | "sort", l => return .sort (← natR "a sort" l)
  | "strVal", .str s => return .strVal s
  | k, _ => bad s!"an expression form {k} has the wrong shape"

def hintsR : Value → R Hints
  | .str "opaque" => .ok .opaque
  | .str "abbrev" => .ok .abbrev
  | .obj [("regular", k)] => do
    let k ← natR "a def's height" k
    if k ≤ 4294967295 then
      return .regular k.toUInt32
    else
      bad "a def's height exceeds 32 bits"
  | _ => bad "a def's hints have the wrong shape"

def safetyR : Value → R Safety
  | .str "safe" => .ok .safe
  | .str "unsafe" => .ok .unsafe
  | .str "partial" => .ok .partial
  | _ => bad "a def's safety has the wrong shape"

def quotKindR : Value → R QuotKind
  | .str "type" => .ok .type
  | .str "ctor" => .ok .ctor
  | .str "lift" => .ok .lift
  | .str "ind" => .ok .ind
  | _ => bad "a quot kind has the wrong shape"

def typeF : Value → R TypeF
  |
  .obj
      [("all", all), ("ctors", ctors), ("isRec", isRec), ("isReflexive", isReflexive),
        ("isUnsafe", isUnsafe), ("levelParams", lps), ("name", n), ("numIndices", ni),
        ("numNested", nn), ("numParams", np), ("type", ty)] =>
    return {
        all := ← natsR "all" all
        ctors := ← natsR "ctors" ctors
        isRec := ← boolR "isRec" isRec
        isReflexive := ← boolR "isReflexive" isReflexive
        isUnsafe := ← boolR "isUnsafe" isUnsafe
        levelParams := ← natsR "level parameters" lps
        name := ← natR "a declaration name" n
        numIndices := ← natR "numIndices" ni
        numNested := ← natR "numNested" nn
        numParams := ← natR "numParams" np
        type := ← natR "a declaration type" ty }
  | _ => bad "an inductive type has the wrong shape"

def ctorF : Value → R CtorF
  |
  .obj
      [("cidx", cidx), ("induct", ind), ("isUnsafe", isUnsafe), ("levelParams", lps), ("name", n),
        ("numFields", nf), ("numParams", np), ("type", ty)] =>
    return {
        cidx := ← natR "cidx" cidx
        induct := ← natR "induct" ind
        isUnsafe := ← boolR "isUnsafe" isUnsafe
        levelParams := ← natsR "level parameters" lps
        name := ← natR "a declaration name" n
        numFields := ← natR "numFields" nf
        numParams := ← natR "numParams" np
        type := ← natR "a declaration type" ty }
  | _ => bad "a constructor has the wrong shape"

def ruleF : Value → R RuleF
  | .obj [("ctor", c), ("nfields", nf), ("rhs", rhs)] =>
    return {
        ctor := ← natR "a rule's constructor" c
        nfields := ← natR "nfields" nf
        rhs := ← natR "a rule's right side" rhs }
  | _ => bad "a recursor rule has the wrong shape"

def rulesR : Value → R (List RuleF)
  | .arr rs => rs.mapM ruleF
  | _ => bad "recursor rules are not an array"

def recF : Value → R RecF
  |
  .obj
      [("all", all), ("isUnsafe", isUnsafe), ("k", k), ("levelParams", lps), ("name", n),
        ("numIndices", ni), ("numMinors", nmi), ("numMotives", nmo), ("numParams", np),
        ("rules", rules), ("type", ty)] =>
    return {
        all := ← natsR "all" all
        isUnsafe := ← boolR "isUnsafe" isUnsafe
        k := ← boolR "k" k
        levelParams := ← natsR "level parameters" lps
        name := ← natR "a declaration name" n
        numIndices := ← natR "numIndices" ni
        numMinors := ← natR "numMinors" nmi
        numMotives := ← natR "numMotives" nmo
        numParams := ← natR "numParams" np
        rules := ← rulesR rules
        type := ← natR "a declaration type" ty }
  | _ => bad "a recursor has the wrong shape"

def declF (k : String) (p : Value) : R DeclF :=
  match k, p with
  | "axiom", .obj [("isUnsafe", u), ("levelParams", lps), ("name", n), ("type", ty)] =>
    return .axiom (← boolR "isUnsafe" u) (← natsR "level parameters" lps)
      (← natR "a declaration name" n) (← natR "a declaration type" ty)
  | "def",
    .obj
      [("all", all), ("hints", h), ("levelParams", lps), ("name", n), ("safety", s), ("type", ty),
        ("value", v)] =>
    return .defn (← natsR "all" all) (← hintsR h) (← natsR "level parameters" lps)
      (← natR "a declaration name" n) (← safetyR s) (← natR "a declaration type" ty)
      (← natR "a value" v)
  | "thm", .obj [("all", all), ("levelParams", lps), ("name", n), ("type", ty), ("value", v)] =>
    return .thm (← natsR "all" all) (← natsR "level parameters" lps)
      (← natR "a declaration name" n) (← natR "a declaration type" ty) (← natR "a value" v)
  | "opaque",
    .obj
      [("all", all), ("isUnsafe", u), ("levelParams", lps), ("name", n), ("type", ty),
        ("value", v)] =>
    return .opaque (← natsR "all" all) (← boolR "isUnsafe" u) (← natsR "level parameters" lps)
      (← natR "a declaration name" n) (← natR "a declaration type" ty) (← natR "a value" v)
  | "quot", .obj [("kind", q), ("levelParams", lps), ("name", n), ("type", ty)] =>
    return .quot (← quotKindR q) (← natsR "level parameters" lps)
      (← natR "a declaration name" n) (← natR "a declaration type" ty)
  | "inductive", .obj [("ctors", .arr cs), ("recs", .arr rs), ("types", .arr ts)] =>
    return .induct (← cs.mapM ctorF) (← rs.mapM recF) (← ts.mapM typeF)
  | k, _ => bad s!"a declaration kind {k} has the wrong shape"

/-- X2 + X3 stage 1: a record line's layout. -/
def parseLine : Value → R Raw
  | .obj [("in", i), (k, p)] => return .name (← natR "a name index" i) (← nameF k p)
  | .obj [("il", i), (k, p)] => return .level (← natR "a level index" i) (← levelF k p)
  | .obj [(k, p), ("ie", i)] => return .expr (← natR "an expression index" i) (← exprLo k p)
  | .obj [("ie", i), (k, p)] => return .expr (← natR "an expression index" i) (← exprHi k p)
  | .obj [(k, p)] => return .decl (← declF k p)
  | _ => bad "an unknown record"

/-! ## Stage 2: the tables -/

/-- X3 + X4: one declaration of a record: what the projection keeps (kind, name, level params,
type, value) + the other references the record holds (validated, not projected). -/
structure Item where
  kind : Kind
  name : Nat
  levelParams : List Nat
  type : Nat
  value : Option Nat
  names : List Nat
  exprs : List Nat
  deriving DecidableEq, Repr

/-- A record's declarations: one, or an inductive block's types, then constructors, then
recursors. -/
def items : DeclF → List Item
  | .axiom _ lps n ty => [⟨.axiom, n, lps, ty, none, [], []⟩]
  | .defn all _ lps n _ ty v => [⟨.defn, n, lps, ty, some v, all, []⟩]
  | .thm all lps n ty v => [⟨.thm, n, lps, ty, some v, all, []⟩]
  | .opaque all _ lps n ty v => [⟨.opaque, n, lps, ty, some v, all, []⟩]
  | .quot _ lps n ty => [⟨.quot, n, lps, ty, none, [], []⟩]
  | .induct cs rs ts =>
    ts.map (fun x => ⟨.induct, x.name, x.levelParams, x.type, none, x.all ++ x.ctors, []⟩) ++
      cs.map (fun c => ⟨.ctor, c.name, c.levelParams, c.type, none, [c.induct], []⟩) ++
      rs.map fun r =>
        ⟨.recursor, r.name, r.levelParams, r.type, none, r.all ++ r.rules.map (·.ctor),
          r.rules.map (·.rhs)⟩

/-- X2: the three tables (dense: each next index = the table's size) + the declarations so far. -/
structure Tables where
  names : Array Lean.Name := #[.anonymous]
  levels : Array Lean.Level := #[.zero]
  exprs : Array Lean.Expr := #[]
  decls : Array Decl := #[]
  declared : List Lean.Name := []

def nameAt (t : Tables) (i : Nat) : R Lean.Name := need s!"name {i} (unbound)" t.names[i]?

def levelAt (t : Tables) (i : Nat) : R Lean.Level := need s!"level {i} (unbound)" t.levels[i]?

def exprAt (t : Tables) (i : Nat) : R Lean.Expr := need s!"expression {i} (unbound)" t.exprs[i]?

/-- The next index of a table of size `n`: exactly `n` (the profile's density). -/
def fresh (table : String) (n i : Nat) : R Unit :=
  if i == n then pure () else outside s!"{table} index {i} is not the next one ({n})"

def denoteName (t : Tables) : NameF → R Lean.Name
  | .str pre s => return .str (← nameAt t pre) s
  | .num pre i => return .num (← nameAt t pre) i

def denoteLevel (t : Tables) : LevelF → R Lean.Level
  | .succ l => return .succ (← levelAt t l)
  | .max a b => return .max (← levelAt t a) (← levelAt t b)
  | .imax a b => return .imax (← levelAt t a) (← levelAt t b)
  | .param n => return .param (← nameAt t n)

def denoteExpr (t : Tables) : ExprF → R Lean.Expr
  | .bvar k => return .bvar k
  | .sort l => return .sort (← levelAt t l)
  | .const n us => return .const (← nameAt t n) (← us.mapM (levelAt t))
  | .app f a => return .app (← exprAt t f) (← exprAt t a)
  | .lam n ty body bi => return .lam (← nameAt t n) (← exprAt t ty) (← exprAt t body) bi
  | .forallE n ty body bi => return .forallE (← nameAt t n) (← exprAt t ty) (← exprAt t body) bi
  | .letE n ty v body nd =>
    return .letE (← nameAt t n) (← exprAt t ty) (← exprAt t v) (← exprAt t body) nd
  | .proj tn idx s => return .proj (← nameAt t tn) idx (← exprAt t s)
  | .natVal v => return .lit (.natVal v)
  | .strVal s => return .lit (.strVal s)

/-- An optional expression reference's value. -/
def optExpr (t : Tables) : Option Nat → R (Option Lean.Expr)
  | none => pure none
  | some i => return some (← exprAt t i)

def denoteItem (t : Tables) (d : Item) : R Decl := do
  discard <| d.names.mapM (nameAt t)
  discard <| d.exprs.mapM (exprAt t)
  return {
      name := ← nameAt t d.name
      kind := d.kind
      levelParams := ← d.levelParams.mapM (nameAt t)
      type := ← exprAt t d.type
      value := ← optExpr t d.value }

/-- X3: each declaration's name new (newest first in `seen`). -/
def addNames (seen : List Lean.Name) : List Decl → R (List Lean.Name)
  | [] => .ok seen
  | d :: ds =>
    if d.name ∈ seen then bad s!"declaration {d.name} is declared twice"
    else addNames (d.name :: seen) ds

/-- X2 + X3 stage 2: one raw record applied to the tables. -/
def apply (t : Tables) : Raw → R Tables
  | .name i f => do
    fresh "name" t.names.size i
    return { t with names := t.names.push (← denoteName t f) }
  | .level i f => do
    fresh "level" t.levels.size i
    return { t with levels := t.levels.push (← denoteLevel t f) }
  | .expr i f => do
    fresh "expression" t.exprs.size i
    return { t with exprs := t.exprs.push (← denoteExpr t f) }
  | .decl d => do
    let ds ← (items d).mapM (denoteItem t)
    return { t with
        decls := t.decls ++ ds.toArray, declared := ← addNames t.declared ds }

/-! ## Lines -/

/-- X1: the header's decoded value: lean4export 3.1.0 from this fvdep's Lean build. -/
def header (githash version : String) : Value → R Unit
  |
  .obj
      [("meta",
          .obj
            [("exporter", .obj [("name", en), ("version", ev)]), ("format", .obj [("version", fv)]),
              ("lean", .obj [("githash", lg), ("version", lv)])])] =>
    match en, ev, fv, lg, lv with
    | .str "lean4export", .str "3.1.0", .str "3.1.0", .str g, .str v =>
      if g == githash && v == version then pure () else outside "an export from another Lean build"
    | _, _, _, _, _ => outside "an exporter, format or Lean identity other than lean4export 3.1.0"
  | _ => bad "the header has the wrong shape"

/-- X1: the end of the line starting at `i` = its first LF at or after `i`, else the end. -/
def lineEnd (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then if b[i] == 0x0A then i else lineEnd b (i + 1) else b.size
termination_by b.size - i

theorem le_lineEnd (b : ByteArray) (i : Nat) (hi : i ≤ b.size) : i ≤ lineEnd b i := by
  unfold lineEnd
  split
  · rename_i h
    split
    · exact Nat.le_refl i
    · exact Nat.le_trans (Nat.le_succ i) (le_lineEnd b (i + 1) h)
  · exact hi
termination_by b.size - i

/-- X1–X5 on line `k` (line 1 = the header): J's decode (a value beyond its bounds = outside the
profile), then the header or a record (layout, then tables). -/
def lineStep (githash version : String) (k : Nat) (t : Tables) (l : ByteArray) : R Tables :=
  match decode l with
  | .error .tooLarge => outside "a value beyond the JSON bounds"
  | .error _ => bad "not one JSON object"
  | .ok v => if k == 1 then (header githash version v).map fun () => t else parseLine v >>= apply t

/-- X1–X5 from byte `i` (a line's start), line `k`: each LF-ended line (a final LF ends the last
one) through `lineStep`; the end before line 1 = no header. -/
def readFrom (githash version : String) (b : ByteArray) (k : Nat) (t : Tables) (i : Nat) :
    Except Refusal Tables :=
  if h : i < b.size then
    have := le_lineEnd b i (Nat.le_of_lt h)
    match lineStep githash version k t (b.extract i (lineEnd b i)) with
    | .ok t' => readFrom githash version b (k + 1) t' (lineEnd b i + 1)
    | .error (c, why) => .error ⟨k, c, why⟩
  else if k == 1 then .error ⟨1, .malformed, "the export has no header"⟩ else .ok t
termination_by b.size - i
decreasing_by omega

/-- X1–X5: the projection of an export, or its first violation. -/
def read (githash version : String) (b : ByteArray) : Except Refusal (List Decl) :=
  (readFrom githash version b 1 {} 0).map (·.decls.toList)

end FvdepCore.Export
