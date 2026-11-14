import FvdepCore.Index.Registry

/-! Spec for registry reading (contract U4 C2 + C8 `RegistryDecodeExact`, `ReencodeExact`): the
accepted forms as an inductive relation, written apart from the walk; the registry records' value
layouts + canonical literals in `Fvdep.Registry.Types.V1`'s field order. -/

namespace FvdepAudit.Registry.Spec

open Lean FvdepCore.Index.Registry

/-- A string literal (metadata transparent). -/
inductive StrLit : Expr → String → Prop
  | lit {s : String} : StrLit (.lit (.strVal s)) s
  | mdata {m : MData} {e : Expr} {s : String} : StrLit e s → StrLit (.mdata m e) s

/-- `e` = the constant `c` applied to `args` (metadata transparent along the spine). -/
inductive AppOf (c : Name) : Expr → List Expr → Prop
  | const {us : List Level} : AppOf c (.const c us) []
  | app {f a : Expr} {args : List Expr} : AppOf c f args → AppOf c (.app f a) (args ++ [a])
  | mdata {m : MData} {e : Expr} {args : List Expr} : AppOf c e args → AppOf c (.mdata m e) args

/-- `Name.mkStr1 … mkStr8` (the head of a `k + 1`-component name literal). -/
def mkStrNames : List Name :=
  [``Name.mkStr1, ``Name.mkStr2, ``Name.mkStr3, ``Name.mkStr4, ``Name.mkStr5, ``Name.mkStr6,
    ``Name.mkStr7, ``Name.mkStr8]

/-- Each expression a string literal. -/
inductive StrLits : List Expr → List String → Prop
  | nil : StrLits [] []
  |
  cons {e : Expr} {es : List Expr} {s : String} {ss : List String} :
    StrLit e s → StrLits es ss → StrLits (e :: es) (s :: ss)

/-- A double-backtick name literal as Lean 4.35 elaborates it: `Name.mkStr1 … mkStr8` over string
literals, `Name.str`/`Name.mkStr` over a name literal + a string literal, `Name.anonymous`
(metadata transparent). -/
inductive NameLit : Expr → Name → Prop
  | mdata {m : MData} {e : Expr} {n : Name} : NameLit e n → NameLit (.mdata m e) n
  | anonymous {us : List Level} : NameLit (.const ``Name.anonymous us) .anonymous
  |
  str {c : Name} {us : List Level} {p s : Expr} {n : Name} {t : String} :
    (c = ``Name.str ∨ c = ``Name.mkStr) →
      NameLit p n → StrLit s t → NameLit (.app (.app (.const c us) p) s) (n.str t)
  |
  mkStrs {k : Nat} {c : Name} {e : Expr} {args : List Expr} {ts : List String} :
    mkStrNames[k]? = some c →
      AppOf c e args →
      args.length = k + 1 → StrLits args ts → NameLit e (ts.foldl Name.str .anonymous)

/-- The registry module's definition `c` (unless being unfolded): its value. -/
def RootDef (F : Facts) (p : List Name) (c : Name) (x : Expr) : Prop :=
  c ∉ p ∧
    ∃ d,
      F.decls.find? (·.name == c) = some d ∧
        d.kind = .defn ∧ d.module = `Fvdep.Registry ∧ d.value = some x

/-- `<M>.entry` declared in `M` (unless being unfolded): its value. -/
def EntryDef (F : Facts) (p : List Name) (c m : Name) (x : Expr) : Prop :=
  c = .str m "entry" ∧
    c ∉ p ∧
    ∃ d, F.decls.find? (·.name == c) = some d ∧ d.kind = .defn ∧ d.module = m ∧ d.value = some x

/-- The bare constants a form's own rule reads (else a registry-module definition is unfolded). -/
def Owns (F : Facts) (p : List Name) : Form → Name → Prop
  | .name, c => c = ``Name.anonymous
  | .enum cs, c => c ∈ cs
  | .ctor c', c => c = c'
  | .entry _, c => ∃ m x, EntryDef F p c m x
  | _, _ => False

/-- `@instHAppendOfAppend (List _) (@List.instAppend _)`. -/
def StdAppend (i : Expr) : Prop :=
  ∃ u₁ u₂ A T,
    i = .app (.app (.const ``instHAppendOfAppend u₁) A) (.app (.const ``List.instAppend u₂) T)

/-- Two cons chains joined. -/
def vappend : Val → Val → Val
  | .cons h t, b => .cons h (vappend t b)
  | _, b => b

/-- C2: what `e` denotes as `f`, under `let` values `env`, unfolding the constants `p`. -/
inductive Denotes (F : Facts) : Form → Expr → List Expr → List Name → Val → Prop
  | any {e : Expr} {env : List Expr} {p : List Name} : Denotes F .any e env p .unread
  |
  mdata {f : Form} {m : MData} {e : Expr} {env : List Expr} {p : List Name} {v : Val} :
    f ≠ .any → Denotes F f e env p v → Denotes F f (.mdata m e) env p v
  |
  letE {f : Form} {n : Name} {t x b : Expr} {nd : Bool} {env : List Expr} {p : List Name}
    {v : Val} : f ≠ .any → Denotes F f b (x :: env) p v → Denotes F f (.letE n t x b nd) env p v
  |
  bvar {f : Form} {i : Nat} {env : List Expr} {p : List Name} {x : Expr} {v : Val} :
    f ≠ .any →
      env[i]? = some x → Denotes F f x (env.drop (i + 1)) p v → Denotes F f (.bvar i) env p v
  |
  root {f : Form} {c : Name} {us : List Level} {env : List Expr} {p : List Name} {x : Expr}
    {v : Val} :
    f ≠ .any →
      ¬Owns F p f c →
      RootDef F p c x → Denotes F f x [] (c :: p) v → Denotes F f (.const c us) env p v
  |
  str {s : String} {env : List Expr} {p : List Name} :
    Denotes F .str (.lit (.strVal s)) env p (.str s)
  |
  anonymous {us : List Level} {env : List Expr} {p : List Name} :
    Denotes F .name (.const ``Name.anonymous us) env p (.name .anonymous)
  |
  name {e₁ e₂ : Expr} {env : List Expr} {p : List Name} {n : Name} :
    NameLit (.app e₁ e₂) n → Denotes F .name (.app e₁ e₂) env p (.name n)
  |
  enum {cs : List Name} {c : Name} {us : List Level} {env : List Expr} {p : List Name} :
    c ∈ cs → Denotes F (.enum cs) (.const c us) env p (.const c)
  |
  ctor {c : Name} {us : List Level} {env : List Expr} {p : List Name} :
    Denotes F (.ctor c) (.const c us) env p (.const c)
  |
  app {ff fa : Form} {e₁ e₂ : Expr} {env : List Expr} {p : List Name} {v₁ v₂ : Val} :
    Denotes F ff e₁ env p v₁ →
      Denotes F fa e₂ env p v₂ → Denotes F (.app ff fa) (.app e₁ e₂) env p (.app v₁ v₂)
  |
  none {f : Form} {us : List Level} {T : Expr} {env : List Expr} {p : List Name} :
    Denotes F (.opt f) (.app (.const ``Option.none us) T) env p .none
  |
  some {f : Form} {us : List Level} {T x : Expr} {env : List Expr} {p : List Name} {v : Val} :
    Denotes F f x env p v →
      Denotes F (.opt f) (.app (.app (.const ``Option.some us) T) x) env p (.some v)
  |
  entry {f : Form} {c m : Name} {us : List Level} {env : List Expr} {p : List Name} {x : Expr}
    {v : Val} :
    EntryDef F p c m x →
      Denotes F f x [] (c :: p) v → Denotes F (.entry f) (.const c us) env p (.entry m v)
  |
  nil {f : Form} {us : List Level} {T : Expr} {env : List Expr} {p : List Name} :
    Denotes F (.list f) (.app (.const ``List.nil us) T) env p .nil
  |
  cons {f : Form} {us : List Level} {T h t : Expr} {env : List Expr} {p : List Name} {x xs : Val} :
    Denotes F f h env p x →
      Denotes F (.list f) t env p xs →
      Denotes F (.list f) (.app (.app (.app (.const ``List.cons us) T) h) t) env p (.cons x xs)
  |
  append {f : Form} {us : List Level} {A B C i xs ys : Expr} {env : List Expr} {p : List Name}
    {a b : Val} :
    StdAppend i →
      Denotes F (.list f) xs env p a →
      Denotes F (.list f) ys env p b →
      Denotes F (.list f)
        (.app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend us) A) B) C) i) xs) ys) env p
        (vappend a b)

/-! ## Values: shapes, the records' layouts, the registry's denotation -/

/-- A name built by `Name.str` alone (what a name literal reads to). -/
inductive StrOnly : Name → Prop
  | anonymous : StrOnly .anonymous
  | str {p : Name} {s : String} : StrOnly p → StrOnly (p.str s)

/-- The shape of a value read as `f`. -/
inductive Fits : Form → Val → Prop
  | str {s : String} : Fits .str (.str s)
  | name {n : Name} : StrOnly n → Fits .name (.name n)
  | enum {cs : List Name} {c : Name} : c ∈ cs → Fits (.enum cs) (.const c)
  | ctor {c : Name} : Fits (.ctor c) (.const c)
  | app {ff fa : Form} {v₁ v₂ : Val} : Fits ff v₁ → Fits fa v₂ → Fits (.app ff fa) (.app v₁ v₂)
  | none {f : Form} : Fits (.opt f) .none
  | some {f : Form} {v : Val} : Fits f v → Fits (.opt f) (.some v)
  | nil {f : Form} : Fits (.list f) .nil
  | cons {f : Form} {h t : Val} : Fits f h → Fits (.list f) t → Fits (.list f) (.cons h t)
  | entry {f : Form} {m : Name} {v : Val} : Fits f v → Fits (.entry f) (.entry m v)
  | any : Fits .any .unread

/-- A form without `entry` or `any`: its values can be written back as literals. -/
def Plain : Form → Prop
  | .entry _ => False
  | .any => False
  | .app ff fa => Plain ff ∧ Plain fa
  | .opt f => Plain f
  | .list f => Plain f
  | _ => True

def listVal : List Val → Val
  | [] => .nil
  | v :: vs => .cons v (listVal vs)

def optVal {α : Type} (f : α → Val) : Option α → Val
  | .some a => .some (f a)
  | .none => .none

/-- `Fvdep.Registry.Types.V1.Module.mk id version spec obligations abi compat`. -/
def moduleFormSpec : Form :=
  .app
    (.app
      (.app (.app (.app (.app (.ctor ``Fvdep.Registry.Types.V1.Module.mk) .str) .str) .name)
        (.list .name))
      (.opt .name))
    (.opt .str)

/-- `Proofs.mk obligations compat`; an obligation pair = `@Prod.mk _ _ obligation theorem`. -/
def proofsFormSpec : Form :=
  .app
    (.app (.ctor ``Fvdep.Registry.Types.V1.Proofs.mk)
      (.list (.app (.app (.app (.app (.ctor ``Prod.mk) .any) .any) .name) .name)))
    (.opt .name)

/-- `Notice.mk id version reason replacement`. -/
def noticeFormSpec : Form :=
  .app (.app (.app (.app (.ctor ``Fvdep.Registry.Types.V1.Notice.mk) .str) .str) .str) (.opt .str)

/-- `Removed.mk id version kind digest toolchain lastCommit`; `kind` = `operation` | `profile`. -/
def removedFormSpec : Form :=
  .app
    (.app
      (.app
        (.app (.app (.app (.ctor ``Fvdep.Registry.Types.V1.Removed.mk) .str) .str)
          (.enum
            [``Fvdep.Registry.Types.V1.Kind.operation, ``Fvdep.Registry.Types.V1.Kind.profile]))
        .str)
      .str)
    .str

/-- An entry's value: its entry module + its `Module.mk` application. -/
def entryVal (e : Entry) : Val :=
  .entry e.module
    (.app
      (.app
        (.app
          (.app
            (.app (.app (.const ``Fvdep.Registry.Types.V1.Module.mk) (.str e.id)) (.str e.version))
            (.name e.spec))
          (listVal (e.obligations.map .name)))
        (optVal .name e.abi))
      (optVal .str e.compat))

def noticeVal (n : Notice) : Val :=
  .app
    (.app (.app (.app (.const ``Fvdep.Registry.Types.V1.Notice.mk) (.str n.id)) (.str n.version))
      (.str n.reason))
    (optVal .str n.replacement)

def kindVal : Kind → Val
  | .operation => .const ``Fvdep.Registry.Types.V1.Kind.operation
  | .profile => .const ``Fvdep.Registry.Types.V1.Kind.profile

def removedVal (r : Removed) : Val :=
  .app
    (.app
      (.app
        (.app
          (.app (.app (.const ``Fvdep.Registry.Types.V1.Removed.mk) (.str r.id)) (.str r.version))
          (kindVal r.kind))
        (.str r.digest))
      (.str r.toolchain))
    (.str r.lastCommit)

def pairVal (x : Name × Name) : Val :=
  .app (.app (.app (.app (.const ``Prod.mk) .unread) .unread) (.name x.1)) (.name x.2)

def proofsVal (pr : Proofs) : Val :=
  .app (.app (.const ``Fvdep.Registry.Types.V1.Proofs.mk) (listVal (pr.obligations.map pairVal)))
    (optVal .name pr.compat)

/-- The value of the constant `c` (from the observations), read as a list of `f`, = `vs`. -/
def ListAt (F : Facts) (f : Form) (c : Name) (vs : List Val) : Prop :=
  ∃ d e,
    F.decls.find? (·.name == c) = some d ∧
      d.kind = .defn ∧ d.value = some e ∧ Denotes F (.list f) e [] [c] (listVal vs)

/-- C2: the registry's four lists = `r`, each read from its constant (`profiles`: its length). -/
def RegistryDenotes (F : Facts) (r : Lists) : Prop :=
  ListAt F (.entry moduleFormSpec) `Fvdep.Registry.modules (r.entries.map entryVal) ∧
    (∃ ps, ListAt F .any `Fvdep.Registry.profiles ps ∧ ps.length = r.profiles) ∧
    ListAt F noticeFormSpec `Fvdep.Registry.notices (r.notices.map noticeVal) ∧
    ListAt F removedFormSpec `Fvdep.Registry.removed (r.removed.map removedVal)

/-- C5: the proof registry constant `c` denotes `pr`. -/
def ProofsAt (F : Facts) (c : Name) (pr : Proofs) : Prop :=
  ∃ d e,
    F.decls.find? (·.name == c) = some d ∧
      d.kind = .defn ∧ d.value = some e ∧ Denotes F proofsFormSpec e [] [c] (proofsVal pr)

end FvdepAudit.Registry.Spec
