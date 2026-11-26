import FvdepCore.Export

/-! Specs for the export reader (contract `docs/contracts/U5b-oracle.md` X1–X5), written from the
contract apart from `FvdepCore.Export`'s code: each record's JSON layout (stage 1), the tables'
denotation (stage 2), the header, the classes + the whole-export run over X1's lines. -/

namespace FvdepAudit.Export.Spec

open FvdepCore.Json FvdepCore.Export

/-! ## Stage 1: the record layouts (X2 + X3; J's members ascend by key) -/

/-- An index or count = a JSON integer. -/
def nat (n : Nat) : Value := .int n

def nats (ns : List Nat) : Value := .arr (ns.map nat)

/-- X2: a name record's form (its key + value) beside `in`. -/
def nameForm : NameF → String × Value
  | .str pre s => ("str", .obj [("pre", nat pre), ("str", .str s)])
  | .num pre i => ("num", .obj [("i", nat i), ("pre", nat pre)])

/-- X2: a level record's form beside `il`. -/
def levelForm : LevelF → String × Value
  | .succ l => ("succ", nat l)
  | .max a b => ("max", .arr [nat a, nat b])
  | .imax a b => ("imax", .arr [nat a, nat b])
  | .param n => ("param", nat n)

def binderInfoLayout : Lean.BinderInfo → Value
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

def binderLayout (n ty body : Nat) (bi : Lean.BinderInfo) : Value :=
  .obj [("binderInfo", binderInfoLayout bi), ("body", nat body), ("name", nat n), ("type", nat ty)]

/-- X2: an expression record's form beside `ie` (`natVal` = canonical decimal digits). -/
def exprForm : ExprF → String × Value
  | .bvar k => ("bvar", nat k)
  | .sort l => ("sort", nat l)
  | .const n us => ("const", .obj [("name", nat n), ("us", nats us)])
  | .app f a => ("app", .obj [("arg", nat a), ("fn", nat f)])
  | .lam n ty body bi => ("lam", binderLayout n ty body bi)
  | .forallE n ty body bi => ("forallE", binderLayout n ty body bi)
  | .letE n ty v body nd =>
    ("letE",
      .obj
        [("body", nat body), ("name", nat n), ("nondep", .bool nd), ("type", nat ty),
          ("value", nat v)])
  | .proj tn i s => ("proj", .obj [("idx", nat i), ("struct", nat s), ("typeName", nat tn)])
  | .natVal v => ("natVal", .str (String.ofList (FvdepCore.Ids.decimal v)))
  | .strVal s => ("strVal", .str s)

def hintsLayout : Hints → Value
  | .opaque => .str "opaque"
  | .abbrev => .str "abbrev"
  | .regular k => .obj [("regular", nat k.toNat)]

def safetyLayout : Safety → Value
  | .safe => .str "safe"
  | .unsafe => .str "unsafe"
  | .partial => .str "partial"

def quotKindLayout : QuotKind → Value
  | .type => .str "type"
  | .ctor => .str "ctor"
  | .lift => .str "lift"
  | .ind => .str "ind"

def typeLayout (x : TypeF) : Value :=
  .obj
    [("all", nats x.all), ("ctors", nats x.ctors), ("isRec", .bool x.isRec),
      ("isReflexive", .bool x.isReflexive), ("isUnsafe", .bool x.isUnsafe),
      ("levelParams", nats x.levelParams), ("name", nat x.name), ("numIndices", nat x.numIndices),
      ("numNested", nat x.numNested), ("numParams", nat x.numParams), ("type", nat x.type)]

def ctorLayout (c : CtorF) : Value :=
  .obj
    [("cidx", nat c.cidx), ("induct", nat c.induct), ("isUnsafe", .bool c.isUnsafe),
      ("levelParams", nats c.levelParams), ("name", nat c.name), ("numFields", nat c.numFields),
      ("numParams", nat c.numParams), ("type", nat c.type)]

def ruleLayout (r : RuleF) : Value :=
  .obj [("ctor", nat r.ctor), ("nfields", nat r.nfields), ("rhs", nat r.rhs)]

def recLayout (r : RecF) : Value :=
  .obj
    [("all", nats r.all), ("isUnsafe", .bool r.isUnsafe), ("k", .bool r.k),
      ("levelParams", nats r.levelParams), ("name", nat r.name), ("numIndices", nat r.numIndices),
      ("numMinors", nat r.numMinors), ("numMotives", nat r.numMotives),
      ("numParams", nat r.numParams), ("rules", .arr (r.rules.map ruleLayout)),
      ("type", nat r.type)]

/-- X3: a declaration record's one member. -/
def declForm : DeclF → String × Value
  | .axiom u lps n ty =>
    ("axiom",
      .obj [("isUnsafe", .bool u), ("levelParams", nats lps), ("name", nat n), ("type", nat ty)])
  | .defn all h lps n s ty v =>
    ("def",
      .obj
        [("all", nats all), ("hints", hintsLayout h), ("levelParams", nats lps), ("name", nat n),
          ("safety", safetyLayout s), ("type", nat ty), ("value", nat v)])
  | .thm all lps n ty v =>
    ("thm",
      .obj
        [("all", nats all), ("levelParams", nats lps), ("name", nat n), ("type", nat ty),
          ("value", nat v)])
  | .opaque all u lps n ty v =>
    ("opaque",
      .obj
        [("all", nats all), ("isUnsafe", .bool u), ("levelParams", nats lps), ("name", nat n),
          ("type", nat ty), ("value", nat v)])
  | .quot q lps n ty =>
    ("quot",
      .obj
        [("kind", quotKindLayout q), ("levelParams", nats lps), ("name", nat n), ("type", nat ty)])
  | .induct cs rs ts =>
    ("inductive",
      .obj
        [("ctors", .arr (cs.map ctorLayout)), ("recs", .arr (rs.map recLayout)),
          ("types", .arr (ts.map typeLayout))])

/-- J's member order for two members: ascending by key. -/
def ascending (a b : String × Value) : List (String × Value) := if b.1 < a.1 then [b, a] else [a, b]

/-- X2 + X3: a record's JSON value. -/
def rawLayout : Raw → Value
  | .name i f => .obj (ascending ("in", nat i) (nameForm f))
  | .level i f => .obj (ascending ("il", nat i) (levelForm f))
  | .expr i f => .obj (ascending ("ie", nat i) (exprForm f))
  | .decl d => .obj [declForm d]

/-- X2: an `mdata` expression record (any payload) = the one record form outside the profile. -/
def IsMData (v : Value) : Prop := ∃ (i : Nat) (p : Value), v = .obj [("ie", nat i), ("mdata", p)]

/-- X1: the header of an export by lean4export 3.1.0 from Lean `version` at commit `githash`. -/
def headerLayout (githash version : String) : Value :=
  .obj
    [("meta",
        .obj
          [("exporter", .obj [("name", .str "lean4export"), ("version", .str "3.1.0")]),
            ("format", .obj [("version", .str "3.1.0")]),
            ("lean", .obj [("githash", .str githash), ("version", .str version)])])]

/-- X1: the header's members, any values (another exporter, format or Lean = outside the
profile). -/
def HeaderShape (v : Value) : Prop :=
  ∃ a b c d e : Value,
    v =
      .obj
        [("meta",
            .obj
              [("exporter", .obj [("name", a), ("version", b)]), ("format", .obj [("version", c)]),
                ("lean", .obj [("githash", d), ("version", e)])])]

/-! ## Stage 2: the tables (X2 + X3 + X4) -/

/-- X2: the tables before line 2: name 0 = anonymous, level 0 = zero, no expressions. -/
def initial : Tables :=
  { names := #[.anonymous]
    levels := #[.zero]
    exprs := #[]
    decls := #[]
    declared := {}
    rawNames := #[none]
    rawLevels := #[none]
    rawExprs := #[]
    rawDecls := #[] }

/-- X2: a record's index = its table's next one. -/
def Dense (t : Tables) : Raw → Prop
  | .name i _ => i = t.names.size
  | .level i _ => i = t.levels.size
  | .expr i _ => i = t.exprs.size
  | .decl _ => True

/-- X3 + X4: a record's declarations (an inductive block: its types, then constructors, then
recursors), each with what the projection keeps + the other references the record holds (`all`,
`ctors`, `induct`, a rule's `ctor` + `rhs`). -/
def itemsOf : DeclF → List Item
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

/-- X2: a name form's value under the names bound so far (index i = `names[i]`). -/
def NameDenotes (names : Array Lean.Name) : NameF → Lean.Name → Prop
  | .str pre s, n => ∃ p, names[pre]? = some p ∧ .str p s = n
  | .num pre i, n => ∃ p, names[pre]? = some p ∧ .num p i = n

/-- X2: a level form's value under the names + levels bound so far. -/
def LevelDenotes (names : Array Lean.Name) (levels : Array Lean.Level) : LevelF → Lean.Level → Prop
  | .succ l, v => ∃ a, levels[l]? = some a ∧ .succ a = v
  | .max a b, v => ∃ x y, levels[a]? = some x ∧ levels[b]? = some y ∧ .max x y = v
  | .imax a b, v => ∃ x y, levels[a]? = some x ∧ levels[b]? = some y ∧ .imax x y = v
  | .param n, v => ∃ x, names[n]? = some x ∧ .param x = v

/-- X2: an expression form's value under the names, levels + expressions bound so far. -/
def ExprDenotes (names : Array Lean.Name) (levels : Array Lean.Level) (exprs : Array Lean.Expr) :
    ExprF → Lean.Expr → Prop
  | .bvar k, e => .bvar k = e
  | .sort l, e => ∃ x, levels[l]? = some x ∧ .sort x = e
  | .const n us, e =>
    ∃ x xs, names[n]? = some x ∧ us.mapM (fun i => levels[i]?) = some xs ∧ .const x xs = e
  | .app f a, e => ∃ x y, exprs[f]? = some x ∧ exprs[a]? = some y ∧ .app x y = e
  | .lam n ty body bi, e =>
    ∃ x u b, names[n]? = some x ∧ exprs[ty]? = some u ∧ exprs[body]? = some b ∧ .lam x u b bi = e
  | .forallE n ty body bi, e =>
    ∃ x u b,
      names[n]? = some x ∧ exprs[ty]? = some u ∧ exprs[body]? = some b ∧ .forallE x u b bi = e
  | .letE n ty v body nd, e =>
    ∃ x u w b,
      names[n]? = some x ∧
        exprs[ty]? = some u ∧ exprs[v]? = some w ∧ exprs[body]? = some b ∧ .letE x u w b nd = e
  | .proj tn idx s, e => ∃ x y, names[tn]? = some x ∧ exprs[s]? = some y ∧ .proj x idx y = e
  | .natVal v, e => .lit (.natVal v) = e
  | .strVal s, e => .lit (.strVal s) = e

/-- X3 + X4: a declaration's projection under the tables: every reference it holds bound, its
name, level params, type + value their values, its kind kept. -/
def DeclDenotes (t : Tables) (d : Item) (o : Decl) : Prop :=
  (∀ n ∈ d.names, (t.names[n]?).isSome) ∧
    (∀ e ∈ d.exprs, (t.exprs[e]?).isSome) ∧
    t.names[d.name]? = some o.name ∧
    o.kind = d.kind ∧
    d.levelParams.mapM (fun i => t.names[i]?) = some o.levelParams ∧
    t.exprs[d.type]? = some o.type ∧
    (match d.value with
    | none => o.value = none
    | some v => ∃ y, t.exprs[v]? = some y ∧ o.value = some y)

/-- X2 + X3 stage 2: a raw record applied to the tables — dense (its index = the table's size),
every reference bound, declared names new (to the earlier declarations + to each other); the
record itself kept beside its denotation (U7 X6), the declared names indexed (U7 X8). -/
def ApplySpec (t : Tables) : Raw → Tables → Prop
  | .name i f, t' =>
    i = t.names.size ∧
      ∃ n,
        NameDenotes t.names f n ∧
          t' =
            { t with
              names := t.names.push n
              rawNames := t.rawNames.push (some f) }
  | .level i f, t' =>
    i = t.levels.size ∧
      ∃ v,
        LevelDenotes t.names t.levels f v ∧
          t' =
            { t with
              levels := t.levels.push v
              rawLevels := t.rawLevels.push (some f) }
  | .expr i f, t' =>
    i = t.exprs.size ∧
      ∃ e,
        ExprDenotes t.names t.levels t.exprs f e ∧
          t' =
            { t with
              exprs := t.exprs.push e
              rawExprs := t.rawExprs.push f }
  | .decl d, t' =>
    ∃ os : List Decl,
      (itemsOf d).length = os.length ∧
        (∀ p ∈ (itemsOf d).zip os, DeclDenotes t p.1 p.2) ∧
        (os.map (·.name)).Nodup ∧
        (∀ o ∈ os, o.name ∉ t.decls.toList.map (·.name)) ∧
        t' =
          { t with
            decls := t.decls ++ os.toArray
            declared := (os.map (·.name)).foldl (fun s n => s.insert n) t.declared
            rawDecls := t.rawDecls.push d }

/-! ## Classes + the run (X1 + X5) -/

/-- X1: J's verdict on a line: its value, or its class (beyond J's string or depth bound =
outside the profile; every other J refusal — an integer beyond ±(2^53 − 1) included = malformed).
-/
def jsonStep (l : List UInt8) : Except Class Value :=
  match decode ⟨l.toArray⟩ with
  | .ok v => .ok v
  | .error .tooLarge => .error .profile
  | .error _ => .error .malformed

/-- X1 + X5: line 1's verdict. -/
inductive HeaderStep (githash version : String) (v : Value) : Except Class Unit → Prop
  | ok : v = headerLayout githash version → HeaderStep githash version v (.ok ())
  |
  other :
    HeaderShape v →
      v ≠ headerLayout githash version → HeaderStep githash version v (.error .profile)
  | shape : ¬HeaderShape v → HeaderStep githash version v (.error .malformed)

/-- X2–X5: a record line's verdict under the tables `t`: shape first, then density, then the
references + declared names. -/
inductive RecordStep (t : Tables) (v : Value) : Except Class Tables → Prop
  | ok (r : Raw) (t' : Tables) : v = rawLayout r → ApplySpec t r t' → RecordStep t v (.ok t')
  | mdata : IsMData v → RecordStep t v (.error .profile)
  | shape : (∀ r, v ≠ rawLayout r) → ¬IsMData v → RecordStep t v (.error .malformed)
  | sparse (r : Raw) : v = rawLayout r → ¬Dense t r → RecordStep t v (.error .profile)
  |
  unbound (r : Raw) :
    v = rawLayout r → Dense t r → (∀ t', ¬ApplySpec t r t') → RecordStep t v (.error .malformed)

/-- X1–X5 over the lines from line `k` (line 1 = the header) under the tables `t`: `.ok t'` = every
line in the profile, `t'` = the final tables; `.error (j, c)` = line `j` = the first violation, of
class `c`; no line at all = no header. -/
inductive Run (githash version : String) :
    Nat → Tables → List (List UInt8) → Except (Nat × Class) Tables → Prop
  | noHeader (t : Tables) : Run githash version 1 t [] (.error (1, .malformed))
  | done (k : Nat) (t : Tables) : 2 ≤ k → Run githash version k t [] (.ok t)
  |
  json (k : Nat) (t : Tables) (l : List UInt8) (ls : List (List UInt8)) (c : Class) :
    jsonStep l = .error c → Run githash version k t (l :: ls) (.error (k, c))
  |
  headerBad (t : Tables) (l : List UInt8) (ls : List (List UInt8)) (v : Value) (c : Class) :
    jsonStep l = .ok v →
      HeaderStep githash version v (.error c) → Run githash version 1 t (l :: ls) (.error (1, c))
  |
  header (t : Tables) (l : List UInt8) (ls : List (List UInt8)) (v : Value)
    (o : Except (Nat × Class) Tables) :
    jsonStep l = .ok v →
      HeaderStep githash version v (.ok ()) →
      Run githash version 2 t ls o → Run githash version 1 t (l :: ls) o
  |
  recordBad (k : Nat) (t : Tables) (l : List UInt8) (ls : List (List UInt8)) (v : Value)
    (c : Class) :
    2 ≤ k →
      jsonStep l = .ok v →
      RecordStep t v (.error c) → Run githash version k t (l :: ls) (.error (k, c))
  |
  record (k : Nat) (t t' : Tables) (l : List UInt8) (ls : List (List UInt8)) (v : Value)
    (o : Except (Nat × Class) Tables) :
    2 ≤ k →
      jsonStep l = .ok v →
      RecordStep t v (.ok t') →
      Run githash version (k + 1) t' ls o → Run githash version k t (l :: ls) o

end FvdepAudit.Export.Spec
