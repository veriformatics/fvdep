import Fvdep.Registry.Types.V1
import Lean.Expr

/-! Registry reading (contract `docs/contracts/U4-library.md` C2): the elaborated `Expr` values of
the registry constants → their records. One generic walk over closures (an expression, the values of
the `let`s around it, the constants being unfolded) against schema data (`Form`), proven equal to
an independent relation (C8 `RegistryDecodeExact`); `reencode` writes a decoded value back as its
canonical literal (the certificate's input, C8 `ReencodeExact`). -/

namespace FvdepCore.Index.Registry

open Lean

/-- A declaration's kind as the environment reports it. -/
inductive DeclKind where
  | defn
  | thm
  | «axiom»
  | «opaque»
  | quot
  | induct
  | ctor
  | recursor
  deriving DecidableEq, Repr

/-- One declaration `libraryFacts` observed: its module of origin + kind; a definition's value. -/
structure Decl where
  name : Name
  module : Name
  kind : DeclKind
  value : Option Expr

/-- The raw observations the pure index functions read (C8 boundary). -/
structure Facts where
  decls : List Decl

/-- The root registry module: its constants are read through (C2: renamed-constant chains). -/
def rootModule : Name := `Fvdep.Registry

/-- A definition's value, unless the constant is already being unfolded. -/
def valueOf? (F : Facts) (p : List Name) (c : Name) (ok : Decl → Bool) : Option Expr :=
  if c ∈ p then none
  else
    match F.decls.find? (·.name == c) with
    | some d => if d.kind == .defn && ok d then d.value else none
    | none => none

/-- A root registry module definition (read through). -/
def rootDef? (F : Facts) (p : List Name) (c : Name) : Option Expr :=
  valueOf? F p c (·.module == rootModule)

/-- `<M>.entry` declared in module `M`: its entry module + value. -/
def entryDef? (F : Facts) (p : List Name) (c : Name) : Option (Name × Expr) :=
  match c with
  | .str m "entry" => (valueOf? F p c (·.module == m)).map fun v => (m, v)
  | _ => none

/-- The declarations not being unfolded (the walk's first termination measure). -/
def fresh (F : Facts) (p : List Name) : Nat := (F.decls.filter fun d => d.name ∉ p).length

/-- The `let` values' size (the walk's second termination measure, with the expression's). -/
@[simp]
noncomputable def envSize : List Expr → Nat
  | [] => 0
  | e :: es => sizeOf e + envSize es

/-- A string literal, metadata transparent. -/
def strLit? : Expr → Option String
  | .mdata _ e => strLit? e
  | .lit (.strVal s) => some s
  | _ => none

/-- An application spine's head constant + arguments (metadata transparent), else `none`. -/
def headArgs? : Expr → List Expr → Option (Name × List Expr)
  | .mdata _ e, acc => headArgs? e acc
  | .app f a, acc => headArgs? f (a :: acc)
  | .const c _, acc => some (c, acc)
  | _, _ => none

/-- `Name.mkStr1 … mkStr8` (the head of a `k + 1`-component name literal at index `k`). -/
def mkStrN : List Name :=
  [``Name.mkStr1, ``Name.mkStr2, ``Name.mkStr3, ``Name.mkStr4, ``Name.mkStr5, ``Name.mkStr6,
    ``Name.mkStr7, ``Name.mkStr8]

/-- `Name.mkStrN s₁ … sₙ`: the head matching the count of string-literal arguments. -/
def mkStrs? (e : Expr) : Option Name :=
  match headArgs? e [] with
  | some (c, a :: as) =>
    if mkStrN[as.length]? == some c then ((a :: as).mapM strLit?).map (·.foldl Name.str .anonymous)
    else none
  | _ => none

/-- A double-backtick name literal as Lean elaborates it (`Name.mkStr1 … mkStr8` over string
literals; `Name.str`/`Name.mkStr` over a name literal + a string literal; `Name.anonymous`),
metadata transparent. -/
def nameLit? : Expr → Option Name
  | .mdata _ e => nameLit? e
  | .const c _ => if c == ``Name.anonymous then some .anonymous else none
  | e@(.app (.app (.const c _) p) s) =>
    if c == ``Name.str || c == ``Name.mkStr then
      match strLit? s with
      | some t => (nameLit? p).map (·.str t)
      | none => none
    else mkStrs? e
  | e => mkStrs? e

/-- `@instHAppendOfAppend (List _) (@List.instAppend _)`: `++` on lists. -/
def stdAppend : Expr → Bool
  | .app (.app (.const ``instHAppendOfAppend _) _) (.app (.const ``List.instAppend _) _) => true
  | _ => false

/-- What the walk expects at a position (schema data, like D5's `Ty`). -/
inductive Form where
  | str
  | name
  /-- One of these constants (an enumeration's constructors). -/
  | enum (cs : List Name)
  /-- This constant (the head of a constructor application). -/
  | ctor (c : Name)
  /-- An application (a constructor applied to its fields, one at a time). -/
  | app (fn arg : Form)
  | opt (f : Form)
  /-- `List.nil`, `List.cons`, `++` (the standard instance), read as one list. -/
  | list (f : Form)
  /-- `<M>.entry` declared in `M`, its value read as `f`. -/
  | entry (f : Form)
  /-- Unread (a type argument; `profiles`' elements). -/
  | any
  deriving DecidableEq, Repr

/-- A decoded value. -/
inductive Val where
  | str (s : String)
  | name (n : Name)
  | const (c : Name)
  | app (fn arg : Val)
  | none
  | some (v : Val)
  | nil
  | cons (h t : Val)
  | entry (m : Name) (v : Val)
  | unread
  deriving DecidableEq, Repr, Inhabited

/-- The list `acc` reversed onto `t`. -/
def Val.ofRev : List Val → Val → Val
  | [], v => v
  | x :: xs, v => Val.ofRev xs (.cons x v)

/-- Whether the form's own rule reads the bare constant `c` (else a root definition is unfolded). -/
def ownsConst (F : Facts) (p : List Name) (f : Form) (c : Name) : Bool :=
  match f with
  | .name => c == ``Name.anonymous
  | .enum cs => cs.contains c
  | .ctor c' => c == c'
  | .entry _ => (entryDef? F p c).isSome
  | _ => false

theorem filter_le {α : Type} (l : List α) (p q : α → Bool)
    (hpq : ∀ x ∈ l, q x = true → p x = true) : (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy => hpq y (List.mem_cons_of_mem _ hy))
    by_cases hqx : q x = true
    · have hpx := hpq x (by simp) hqx
      simp [hqx, hpx]
      omega
    · by_cases hpx : p x = true
      · simp [hqx, hpx]
        omega
      · simp [hqx, hpx]
        omega

theorem filter_lt {α : Type} (l : List α) (p q : α → Bool) (hpq : ∀ x ∈ l, q x = true → p x = true)
    (a : α) (ha : a ∈ l) (hp : p a = true) (hq : q a = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at ha
  | cons x xs
    ih =>
    have hle := filter_le xs p q (fun y hy => hpq y (List.mem_cons_of_mem _ hy))
    rcases List.mem_cons.mp ha with rfl | ha'
    · simp [hp, hq]
      omega
    · have := ih (fun y hy => hpq y (List.mem_cons_of_mem _ hy)) ha'
      by_cases hqx : q x = true
      · have hpx := hpq x (by simp) hqx
        simp [hqx, hpx]
        omega
      · by_cases hpx : p x = true
        · simp [hqx, hpx]
          omega
        · simp [hqx, hpx]
          omega

theorem valueOf_fresh {F : Facts} {p : List Name} {c : Name} {ok : Decl → Bool} {x : Expr}
    (h : valueOf? F p c ok = some x) : fresh F (c :: p) < fresh F p := by
  unfold valueOf? at h
  split at h
  · cases h
  · rename_i hp
    split at h
    · rename_i d hd
      have hmem := List.mem_of_find?_eq_some hd
      have hname : d.name = c := by simpa using List.find?_some hd
      unfold fresh
      apply filter_lt F.decls _ _ _ d hmem
      · simp [hname, hp]
      · simp [hname]
      · intro y _ hy
        simp only [List.mem_cons, not_or, decide_eq_true_eq] at hy ⊢
        exact hy.2
    · cases h

theorem root_fresh {F : Facts} {p : List Name} {c : Name} {x : Expr} (h : rootDef? F p c = some x) :
    fresh F (c :: p) < fresh F p := valueOf_fresh h

theorem entry_fresh {F : Facts} {p : List Name} {c m : Name} {x : Expr}
    (h : entryDef? F p c = some (m, x)) : fresh F (c :: p) < fresh F p := by
  unfold entryDef? at h
  split at h
  · obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.mp h
    cases hyx
    exact valueOf_fresh hy
  · cases h

theorem env_le {env : List Expr} {i : Nat} {v : Expr} (h : env[i]? = some v) :
    sizeOf v + envSize (env.drop (i + 1)) ≤ envSize env := by
  induction env generalizing i with
  | nil => simp at h
  | cons e es ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [envSize]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h
      simp only [List.drop_succ_cons, envSize]
      omega

mutual
/-- C2: the value `e` denotes as `f` (under `let` values `env`, unfolding `p`), else the constant
whose value holds the unreadable term (`p`'s head). -/
def decode (F : Facts) (f : Form) (e : Expr) (env : List Expr) (p : List Name) : Except Name Val :=
  match f with
  | .any => .ok .unread
  | .list fe =>
    match spine F fe e env p [] with
    | .ok acc => .ok (Val.ofRev acc .nil)
    | .error n => .error n
  | _ =>
    match e with
    | .mdata _ e => decode F f e env p
    | .letE _ _ v b _ => decode F f b (v :: env) p
    | .bvar i =>
      match hv : env[i]? with
      | some v =>
        have := env_le hv
        decode F f v (env.drop (i + 1)) p
      | none => .error (p.headD .anonymous)
    | .lit l =>
      match f, l with
      | .str, .strVal s => .ok (.str s)
      | _, _ => .error (p.headD .anonymous)
    | .const c _ =>
      if ownsConst F p f c then
        match f with
        | .entry fe =>
          match hu : entryDef? F p c with
          | some (m, v) =>
            have := entry_fresh hu
            match decode F fe v [] (c :: p) with
            | .ok x => .ok (.entry m x)
            | .error n => .error n
          | none => .error (p.headD .anonymous)
        | .name => .ok (.name .anonymous)
        | _ => .ok (.const c)
      else
        match hu : rootDef? F p c with
        | some v =>
          have := root_fresh hu
          decode F f v [] (c :: p)
        | none => .error (p.headD .anonymous)
    | .app e₁ e₂ =>
      match f with
      | .name =>
        match nameLit? (.app e₁ e₂) with
        | some n => .ok (.name n)
        | none => .error (p.headD .anonymous)
      | .opt fo =>
        match e₁ with
        | .const ``Option.none _ => .ok .none
        | .app (.const ``Option.some _) _ =>
          match decode F fo e₂ env p with
          | .ok x => .ok (.some x)
          | .error n => .error n
        | _ => .error (p.headD .anonymous)
      | .app ff fa =>
        match decode F ff e₁ env p with
        | .ok v₁ =>
          match decode F fa e₂ env p with
          | .ok v₂ => .ok (.app v₁ v₂)
          | .error n => .error n
        | .error n => .error n
      | _ => .error (p.headD .anonymous)
    | _ => .error (p.headD .anonymous)
termination_by (fresh F p, sizeOf e + envSize env, 1)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left; assumption)
    | (apply Prod.Lex.right; apply Prod.Lex.left; simp; omega)
    | (apply Prod.Lex.left; simp; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right; decide)
/-- C2: a list's elements onto `acc` (reversed): `List.nil`, `List.cons`, `++` with the standard
instance; the tail, `++`'s right operand, `let`s + unfolds loop (no stack per element). -/
def spine (F : Facts) (fe : Form) (e : Expr) (env : List Expr) (p : List Name) (acc : List Val) :
    Except Name (List Val) :=
  match e with
  | .mdata _ e => spine F fe e env p acc
  | .letE _ _ v b _ => spine F fe b (v :: env) p acc
  | .bvar i =>
    match hv : env[i]? with
    | some v =>
      have := env_le hv
      spine F fe v (env.drop (i + 1)) p acc
    | none => .error (p.headD .anonymous)
  | .app (.const ``List.nil _) _ => .ok acc
  | .app (.app (.app (.const ``List.cons _) _) h) t =>
    match decode F fe h env p with
    | .ok x => spine F fe t env p (x :: acc)
    | .error n => .error n
  | .app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend _) _) _) _) i) xs) ys =>
    if stdAppend i then
      match spine F fe xs env p acc with
      | .ok acc' => spine F fe ys env p acc'
      | .error n => .error n
    else .error (p.headD .anonymous)
  | .const c _ =>
    match hu : rootDef? F p c with
    | some v =>
      have := root_fresh hu
      spine F fe v [] (c :: p) acc
    | none => .error (p.headD .anonymous)
  | _ => .error (p.headD .anonymous)
termination_by (fresh F p, sizeOf e + envSize env, 0)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left; assumption)
    | (apply Prod.Lex.right; apply Prod.Lex.left; simp; omega)
end

/-! ## The registry's records (`Fvdep.Registry.Types.V1`, field order) -/

/-- `Module.mk id version spec obligations abi compat`. -/
def moduleForm : Form :=
  .app
    (.app
      (.app (.app (.app (.app (.ctor ``Fvdep.Registry.Types.V1.Module.mk) .str) .str) .name)
        (.list .name))
      (.opt .name))
    (.opt .str)

/-- `Proofs.mk obligations compat` (obligations = `(obligation, theorem)` tuples). -/
def proofsForm : Form :=
  .app
    (.app (.ctor ``Fvdep.Registry.Types.V1.Proofs.mk)
      (.list (.app (.app (.app (.app (.ctor ``Prod.mk) .any) .any) .name) .name)))
    (.opt .name)

/-- `Notice.mk id version reason replacement`. -/
def noticeForm : Form :=
  .app (.app (.app (.app (.ctor ``Fvdep.Registry.Types.V1.Notice.mk) .str) .str) .str) (.opt .str)

def kindForm : Form :=
  .enum [``Fvdep.Registry.Types.V1.Kind.operation, ``Fvdep.Registry.Types.V1.Kind.profile]

/-- `Removed.mk id version kind digest toolchain lastCommit`. -/
def removedForm : Form :=
  .app
    (.app
      (.app (.app (.app (.app (.ctor ``Fvdep.Registry.Types.V1.Removed.mk) .str) .str) kindForm)
        .str)
      .str)
    .str

/-- The field names of each registry structure (C2 certificate: the environment's structure info
must list exactly these, in this order). -/
def moduleFields : List String := ["id", "version", "spec", "obligations", "abi", "compat"]

def noticeFields : List String := ["id", "version", "reason", "replacement"]

def removedFields : List String := ["id", "version", "kind", "digest", "toolchain", "lastCommit"]

/-- An operation entry (`<M>.entry`) + its entry module `M`. -/
structure Entry where
  module : Name
  id : String
  version : String
  spec : Name
  obligations : List Name
  abi : Option Name
  compat : Option String
  deriving BEq, Repr

structure Proofs where
  obligations : List (Name × Name)
  compat : Option Name
  deriving BEq, Repr

structure Notice where
  id : String
  version : String
  reason : String
  replacement : Option String
  deriving BEq, Repr

inductive Kind where
  | operation
  | profile
  deriving DecidableEq, Repr

structure Removed where
  id : String
  version : String
  kind : Kind
  digest : String
  toolchain : String
  lastCommit : String
  deriving BEq, Repr

/-- The registry lists (C2): `profiles` = its length alone (elements unread; C3 V10). -/
structure Lists where
  entries : List Entry
  profiles : Nat
  notices : List Notice
  removed : List Removed
  deriving BEq, Repr

/-! ## Extraction (total: a value the walk accepts never reaches a fallback) -/

/-- A cons chain's elements, in order (a loop). -/
def Val.elems (v : Val) : List Val := go v []
where go : Val → List Val → List Val
    | .cons h t, acc => go t (h :: acc)
    | _, acc => acc.reverse

def Val.strD : Val → String
  | .str s => s
  | _ => ""

def Val.nameD : Val → Name
  | .name n => n
  | _ => .anonymous

def Val.optD {α : Type} (f : Val → α) : Val → Option α
  | .some v => Option.some (f v)
  | _ => Option.none

/-- A constructor application's arguments, in order. -/
def Val.args (v : Val) : List Val := go v []
where go : Val → List Val → List Val
    | .app f a, acc => go f (a :: acc)
    | _, acc => acc

def Val.argD (v : Val) (i : Nat) : Val := v.args.getD i .unread

def entryOf : Val → Entry
  | .entry m v =>
    { module := m
      id := (v.argD 0).strD
      version := (v.argD 1).strD
      spec := (v.argD 2).nameD
      obligations := (v.argD 3).elems.map Val.nameD
      abi := (v.argD 4).optD Val.nameD
      compat := (v.argD 5).optD Val.strD }
  | _ => ⟨.anonymous, "", "", .anonymous, [], none, none⟩

def pairOf (v : Val) : Name × Name := ((v.argD 2).nameD, (v.argD 3).nameD)

def proofsOf (v : Val) : Proofs := ⟨(v.argD 0).elems.map pairOf, (v.argD 1).optD Val.nameD⟩

def noticeOf (v : Val) : Notice :=
  ⟨(v.argD 0).strD, (v.argD 1).strD, (v.argD 2).strD, (v.argD 3).optD Val.strD⟩

def kindOf : Val → Kind
  | .const c => if c == ``Fvdep.Registry.Types.V1.Kind.profile then .profile else .operation
  | _ => .operation

def removedOf (v : Val) : Removed :=
  ⟨(v.argD 0).strD, (v.argD 1).strD, kindOf (v.argD 2), (v.argD 3).strD, (v.argD 4).strD,
    (v.argD 5).strD⟩

/-! ## Reading -/

def modulesName : Name := `Fvdep.Registry.modules

def profilesName : Name := `Fvdep.Registry.profiles

def noticesName : Name := `Fvdep.Registry.notices

def removedName : Name := `Fvdep.Registry.removed

/-- A definition's value (a registry list or proof registry constant). -/
def defValue? (F : Facts) (c : Name) : Option Expr :=
  match F.decls.find? (·.name == c) with
  | some d => if d.kind == .defn then d.value else none
  | none => none

/-- A registry list constant's elements read as `f` (no definition value → refused, naming it). -/
def listOf (F : Facts) (f : Form) (c : Name) : Except Name (List Val) :=
  match defValue? F c with
  | some v =>
    match spine F f v [] [c] [] with
    | .ok acc => .ok acc.reverse
    | .error n => .error n
  | none => .error c

/-- The registry lists as read, before extraction (the certificate re-encodes these values). -/
structure RawLists where
  modules : List Val
  profiles : List Val
  notices : List Val
  removed : List Val

/-- C2: the registry lists, read in the order `modules` → `profiles` → `notices` → `removed`; the
first unreadable term names its constant. -/
def readRaw (F : Facts) : Except Name RawLists := do
  let ms ← listOf F (.entry moduleForm) modulesName
  let ps ← listOf F .any profilesName
  let ns ← listOf F noticeForm noticesName
  let rs ← listOf F removedForm removedName
  pure ⟨ms, ps, ns, rs⟩

def Lists.ofRaw (r : RawLists) : Lists :=
  ⟨r.modules.map entryOf, r.profiles.length, r.notices.map noticeOf, r.removed.map removedOf⟩

/-- C2: the registry lists' records. -/
def readRegistry (F : Facts) : Except Name Lists := (readRaw F).map Lists.ofRaw

/-- C5: a proof registry's map (`<P>.proofs`); unreadable → the caller's warning. -/
def readProofs (F : Facts) (c : Name) : Except Name Proofs :=
  match defValue? F c with
  | some v => (decode F proofsForm v [] [c]).map proofsOf
  | none => .error c

/-! ## Re-encoding (C2 certificate: the canonical literal of a decoded value) -/

/-- A name's canonical literal: `Name.str` from `Name.anonymous`. -/
def nameExpr : Name → Expr
  | .str p s => .app (.app (.const ``Name.str []) (nameExpr p)) (.lit (.strVal s))
  | _ => .const ``Name.anonymous []

/-- The type of the values a form reads (the literal's type arguments). -/
def tyOf : Form → Expr
  | .str => .const ``String []
  | .name => .const ``Lean.Name []
  | .enum cs => .const (cs.headD .anonymous).getPrefix []
  | .ctor c => .const c.getPrefix []
  | .app f _ => tyOf f
  | .opt f => .app (.const ``Option [.zero]) (tyOf f)
  | .list f => .app (.const ``List [.zero]) (tyOf f)
  | .entry f => tyOf f
  | .any => .const ``Unit []

mutual
/-- The canonical literal of `v` read as `f` (constructor applications in field order). -/
def reencode : Form → Val → Expr
  | .str, .str s => .lit (.strVal s)
  | .name, .name n => nameExpr n
  | .enum _, .const c => .const c []
  | .ctor _, .const c => .const c []
  | .app ff fa, .app v₁ v₂ => .app (reencode ff v₁) (reencode fa v₂)
  | .opt f, .none => .app (.const ``Option.none [.zero]) (tyOf f)
  | .opt f, .some v => .app (.app (.const ``Option.some [.zero]) (tyOf f)) (reencode f v)
  | .list f, v => reencodeList f v
  | .entry f, .entry _ v => reencode f v
  | _, _ => .const ``Unit.unit []
def reencodeList (f : Form) : Val → Expr
  | .cons h t =>
    .app (.app (.app (.const ``List.cons [.zero]) (tyOf f)) (reencode f h)) (reencodeList f t)
  | _ => .app (.const ``List.nil [.zero]) (tyOf f)
end

/-- The canonical literal of a list of values read as `f`, built in a loop (no stack per
element). -/
def listLiteral (f : Form) (vs : List Val) : Expr :=
  (vs.map (reencode f)).reverse.foldl
    (fun acc x => .app (.app (.app (.const ``List.cons [.zero]) (tyOf f)) x) acc)
    (.app (.const ``List.nil [.zero]) (tyOf f))

end FvdepCore.Index.Registry
