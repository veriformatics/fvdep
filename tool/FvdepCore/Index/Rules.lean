import FvdepCore.Doc
import FvdepCore.Index.Registry
import FvdepCore.Protocol.Sig

/-! Entry rules (contract `docs/contracts/U4-library.md` C3 V1–V10 + C4's file check, in C9's
order): every check of the registry lists as one row (`none` = it passes, else its violation);
`validate` = the first violation. Pure over `Facts` (C8 boundary); C8 `ValidateExact` +
`ClosureExact` state it against the order + relations written apart (`FvdepAudit.Index.Rules`). -/

namespace FvdepCore.Index.Rules

open Lean FvdepCore.Ids FvdepCore.Index.Registry

/-! ## Printed-name order (C9: offenders by the UTF-8 bytes of the printed name) -/

/-- Strict lexicographic order on code points (= the UTF-8 byte order of the texts). -/
def lexLt : List Char → List Char → Bool
  | [], _ :: _ => true
  | a :: as, b :: bs => a.toNat < b.toNat || (a.toNat == b.toNat && lexLt as bs)
  | _, _ => false

/-- A name as fvdep prints it. -/
def key (n : Name) : List Char := n.toString.toList

/-- The first of `xs` with no strictly smaller printed name. -/
def least : List Name → Option Name
  | [] => none
  | x :: xs => some (xs.foldl (fun m y => if lexLt (key y) (key m) then y else m) x)

/-! ## V3: compiled-code marks, reached through definition values -/

/-- The constants a term's `.const` nodes name, onto `acc` (repeats kept). -/
def constsOnto : Expr → List Name → List Name
  | .const c _, acc => c :: acc
  | .app f a, acc => constsOnto f (constsOnto a acc)
  | .lam _ t b _, acc => constsOnto t (constsOnto b acc)
  | .forallE _ t b _, acc => constsOnto t (constsOnto b acc)
  | .letE _ t v b _, acc => constsOnto t (constsOnto v (constsOnto b acc))
  | .mdata _ e, acc => constsOnto e acc
  | .proj _ _ e, acc => constsOnto e acc
  | _, acc => acc

/-- The library declaration named `c` (module first component exactly `Fvdep`). -/
def libDecl? (F : Facts) (c : Name) : Option Decl :=
  F.decls.find? fun d => d.name == c && d.module.getRoot == `Fvdep

/-- The constants a declaration's code names: a definition's value (a theorem's or an opaque
constant's value is never walked). -/
def bodyConsts (d : Decl) : List Name :=
  match d.kind, d.value with
  | .defn, some v => constsOnto v []
  | _, _ => []

theorem libDecl_fresh {F : Facts} {seen : List Name} {c : Name} {d : Decl}
    (h : libDecl? F c = some d) (hc : c ∉ seen) : fresh F (c :: seen) < fresh F seen := by
  have hmem := List.mem_of_find?_eq_some h
  have hname : d.name = c := by
    have := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  unfold fresh
  apply filter_lt F.decls _ _ _ d hmem
  · simp [hname, hc]
  · simp [hname]
  · intro y _ hy
    simp only [List.mem_cons, not_or, decide_eq_true_eq] at hy ⊢
    exact hy.2

/-- The library constants reachable from `todo` through definition values, each once, onto `seen`
(a worklist: each declaration enters `seen` once). -/
def reachGo (F : Facts) (todo seen : List Name) : List Name :=
  match todo with
  | [] => seen
  | c :: rest =>
    if hc : c ∈ seen then reachGo F rest seen
    else
      match h : libDecl? F c with
      | none => reachGo F rest seen
      | some d =>
        have := libDecl_fresh h hc
        reachGo F (bodyConsts d ++ rest) (c :: seen)
termination_by (fresh F seen, todo.length)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left; assumption)
    | (apply Prod.Lex.right; simp)

/-- C3 V3: the library constants checked for an entry — its roots + every library constant their
definition values reach. -/
def reach (F : Facts) (roots : List Name) : List Name := reachGo F roots []

/-- The declaration Lean compiles callers of `c` from, when present (`<c>._unsafe_rec`). -/
def companion? (F : Facts) (c : Name) : Option Decl :=
  F.decls.find? fun d => d.name == .str c "_unsafe_rec"

/-- Lean's own compiled form: a definition of partial safety. -/
def leanForm (d : Decl) : Bool := d.kind == .defn && d.safety == .partial

/-- C3 V3's flags, in C9's order. -/
inductive Flag where
  | «partial»
  | «unsafe»
  | implementedBy
  | «extern»
  | «opaque»
  | «noncomputable»
  deriving DecidableEq, Repr

def Flag.all : List Flag := [.partial, .unsafe, .implementedBy, .extern, .opaque, .noncomputable]

def Flag.text : Flag → String
  | .partial => "partial"
  | .unsafe => "unsafe"
  | .implementedBy => "implemented_by"
  | .extern => "extern"
  | .opaque => "opaque"
  | .noncomputable => "noncomputable"

/-- Whether a declaration carries a flag (contract C3 V3: Lean stores a recursive `partial def` as
an opaque constant + a partial `_unsafe_rec`; a hand-written `_unsafe_rec` replaces the code). -/
def hasFlag (F : Facts) (d : Decl) : Flag → Bool
  | .partial => d.safety == .partial || (d.kind == .opaque && (companion? F d.name).any leanForm)
  | .unsafe => d.safety == .unsafe
  | .implementedBy => d.implementedBy || (companion? F d.name).any fun x => !leanForm x
  | .extern => d.isExtern
  | .opaque => d.kind == .opaque
  | .noncomputable => d.isNoncomputable

/-- A library constant carrying `fl`. -/
def carries (F : Facts) (fl : Flag) (c : Name) : Bool :=
  match libDecl? F c with
  | some d => hasFlag F d fl
  | none => false

/-! ## Alpha-equivalence (V4, V5; C5) -/

/-- Alpha-equivalence's representative: binder names + annotations erased, metadata dropped,
levels + everything else kept. -/
def erase : Expr → Expr
  | .app f a => .app (erase f) (erase a)
  | .lam _ t b _ => .lam .anonymous (erase t) (erase b) .default
  | .forallE _ t b _ => .forallE .anonymous (erase t) (erase b) .default
  | .letE _ t v b _ => .letE .anonymous (erase t) (erase v) (erase b) false
  | .mdata _ e => erase e
  | .proj s i e => .proj s i (erase e)
  | e => e

def levelEq : Level → Level → Bool
  | .zero, .zero => true
  | .succ a, .succ b => levelEq a b
  | .max a b, .max c d => levelEq a c && levelEq b d
  | .imax a b, .imax c d => levelEq a c && levelEq b d
  | .param a, .param b => a == b
  | .mvar a, .mvar b => a.name == b.name
  | _, _ => false

def levelsEq : List Level → List Level → Bool
  | [], [] => true
  | a :: as, b :: bs => levelEq a b && levelsEq as bs
  | _, _ => false

def litEq : Literal → Literal → Bool
  | .natVal a, .natVal b => a == b
  | .strVal a, .strVal b => a == b
  | _, _ => false

/-- Structural equality of erased terms (binder names + annotations are erased: not compared;
metadata never occurs). -/
def erasedEq : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar a, .fvar b => a.name == b.name
  | .mvar a, .mvar b => a.name == b.name
  | .sort u, .sort v => levelEq u v
  | .const c us, .const d vs => c == d && levelsEq us vs
  | .app f a, .app g b => erasedEq f g && erasedEq a b
  | .lam _ t b _, .lam _ t' b' _ => erasedEq t t' && erasedEq b b'
  | .forallE _ t b _, .forallE _ t' b' _ => erasedEq t t' && erasedEq b b'
  | .letE _ t v b _, .letE _ t' v' b' _ => erasedEq t t' && erasedEq v v' && erasedEq b b'
  | .lit l, .lit l' => litEq l l'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && erasedEq e e'
  | _, _ => false

/-- Alpha-equivalence (contract C5: binder names + annotations ignored, metadata transparent,
levels as written). -/
def alphaEq (a b : Expr) : Bool := erasedEq (erase a) (erase b)

/-! ## Modules: closure (C4), paths, versioned names (V7) -/

/-- The observation of module `m`. -/
def modFacts? (F : Facts) (m : Name) : Option ModFacts := F.modules.find? (·.name == m)

/-- The observed modules not yet in `seen` (the closure walk's measure). -/
def freshMods (F : Facts) (seen : List Name) : Nat :=
  (F.modules.filter fun x => x.name ∉ seen).length

theorem modFacts_fresh {F : Facts} {seen : List Name} {m : Name} {x : ModFacts}
    (h : modFacts? F m = some x) (hm : m ∉ seen) : freshMods F (m :: seen) < freshMods F seen := by
  have hmem := List.mem_of_find?_eq_some h
  have hname : x.name = m := by simpa using List.find?_some h
  unfold freshMods
  apply filter_lt F.modules _ _ _ x hmem
  · simp [hname, hm]
  · simp [hname]
  · intro y _ hy
    simp only [List.mem_cons, not_or, decide_eq_true_eq] at hy ⊢
    exact hy.2

theorem modFacts_none {F : Facts} {seen : List Name} {m : Name} (h : modFacts? F m = none) :
    freshMods F (m :: seen) = freshMods F seen := by
  unfold freshMods
  congr 1
  apply List.filter_congr
  intro y hy
  have hne : y.name ≠ m := by
    intro e
    have := List.find?_eq_none.mp h y hy
    simp [e] at this
  simp [hne]

/-- The modules reachable from `todo` through the import edges of the modules it reaches (imports
whose first name component is exactly `Fvdep`), each once, onto `seen`; a module without an
observation joins with no edge. -/
def closureGo (F : Facts) (todo seen : List Name) : List Name :=
  match todo with
  | [] => seen
  | m :: rest =>
    if hm : m ∈ seen then closureGo F rest seen
    else
      match h : modFacts? F m with
      | none =>
        have := modFacts_none (seen := seen) h
        closureGo F rest (m :: seen)
      | some x =>
        have := modFacts_fresh h hm
        closureGo F (x.imports.filter (·.getRoot == `Fvdep) ++ rest) (m :: seen)
termination_by (freshMods F seen, todo.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · rw [this]
    exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ this

/-- C4: closure(M) = M + every `Fvdep` module reachable from it. -/
def closure (F : Facts) (M : Name) : List Name := closureGo F [M] []

/-- A name's components as path segments. -/
def pathParts : Name → List String
  | .anonymous => []
  | .str p s => pathParts p ++ [s]
  | .num p n => pathParts p ++ [toString n]

/-- A module's canonical source path (C4: `<module name, . → />.lean`). -/
def modulePath (m : Name) : String := "/".intercalate (pathParts m) ++ ".lean"

/-- `V<x>_<y>_<z>` with canonical decimals (entry versions' spelling). -/
def versionedPart (s : String) : Bool :=
  match s.toList with
  | 'V' :: rest =>
    !rest.contains '.' &&
      (EntryVersion.parseChars (rest.map fun c => if c == '_' then '.' else c)).isSome
  | _ => false

/-- A versioned module: last component `V<x>_<y>_<z>`. -/
def versionedName : Name → Bool
  | .str _ s => versionedPart s
  | _ => false

/-- V7: a module entry `M`'s closure may hold (M, versioned library modules outside
`Fvdep.Registry.ProfileTypes`, `Fvdep.Registry.Types.V1`). -/
def holdsOk (M m : Name) : Bool :=
  m == M || m == `Fvdep.Registry.Types.V1 ||
    (versionedName m && !(`Fvdep.Registry.ProfileTypes).isPrefixOf m)

/-- V7: an import inside Init, Std + the library (first name component exactly one of them). -/
def importOk (i : Name) : Bool :=
  let r := i.getRoot
  r == `Init || r == `Std || r == `Fvdep

/-- V7: a closure module's imports outside Init, Std + the library. -/
def badImports (F : Facts) (m : Name) : List Name :=
  match modFacts? F m with
  | some x => x.imports.filter fun i => !importOk i
  | none => []

/-- C4: an observed regular file at the module's canonical path. -/
def regularFile (F : Facts) (m : Name) : Bool :=
  match modFacts? F m with
  | some x => x.file.isSome
  | none => false

/-! ## Entries: canonical names (V1), the spec module, observations (V5, V6) -/

/-- The entry module of an id + version (`Fvdep.Registry.<Dep>.<Op>.V<x>_<y>_<z>`). -/
def entryModule (m : ModuleId) (v : EntryVersion) : Name :=
  .str
    (.str (.str (.str (.str .anonymous "Fvdep") "Registry") (String.ofList m.dep.camel))
      (String.ofList (camelAll (m.op₀ :: m.ops))))
    (String.ofList (vPart v))

/-- An entry's id + version, when both are canonical. -/
def canonical? (e : Entry) : Option (ModuleId × EntryVersion) :=
  match ModuleId.parse e.id, EntryVersion.parse e.version with
  | some m, some v => some (m, v)
  | _, _ => none

/-- The spec module `S` of an entry (`.anonymous` when its id or version is not canonical). -/
def specModule (e : Entry) : Name :=
  match canonical? e with
  | some (m, v) => leanModule m v
  | none => .anonymous

/-- V3: `c = S.<fn>`, a definition declared in `S`. -/
def specIn (F : Facts) (c S : Name) : Bool :=
  (match c with
    | .str p _ => p == S
    | _ => false) &&
    (match libDecl? F c with
    | some d => d.kind == .defn && d.module == S
    | none => false)

/-- V3: the spec type is encodable (`sigOf`). -/
def encodable (F : Facts) (c : Name) : Bool :=
  match libDecl? F c with
  | some d => (FvdepCore.Protocol.sigOf d.type).isSome
  | none => false

/-- V4: a definition declared in `S` of type exactly `Prop`. -/
def propIn (F : Facts) (o S : Name) : Bool :=
  match libDecl? F o with
  | some d => d.kind == .defn && d.module == S && alphaEq d.type (.sort .zero)
  | none => false

/-- The first element repeating an earlier one. -/
def firstRepeat (xs : List Name) : Option Name := go xs []
where go : List Name → List Name → Option Name
    | [], _ => none
    | x :: xs, seen => if x ∈ seen then some x else go xs (x :: seen)

/-- V5: a definition of a module `Fvdep.Abi.V<x>_<y>_<z>`. -/
def abiShape (F : Facts) (a : Name) : Bool :=
  match libDecl? F a with
  | some d =>
    d.kind == .defn &&
      (match d.module with
      | .str (.str (.str .anonymous "Fvdep") "Abi") s => versionedPart s
      | _ => false)
  | none => false

/-- `ByteArray → ByteArray`. -/
def bytesFn : Expr := .forallE .anonymous (.const ``ByteArray []) (.const ``ByteArray []) .default

/-- `ByteArray → Option ByteArray`. -/
def bytesOptFn : Expr :=
  .forallE .anonymous (.const ``ByteArray [])
    (.app (.const ``Option [.zero]) (.const ``ByteArray [])) .default

/-- The observed type of `abi spec` (`some none` = ill-typed; `none` = not observed). -/
def abiTypeOf? (F : Facts) (abi spec : Name) : Option (Option Expr) :=
  (F.abiType.find? fun x => x.1.1 == abi && x.1.2 == spec).map (·.2)

/-- The kernel's verdict on two spec types (`none` = not observed). -/
def defeqOf? (F : Facts) (spec old : Name) : Option Bool :=
  (F.specDefeq.find? fun x => x.1.1 == spec && x.1.2 == old).map (·.2)

/-- V6: the listed entry an id + version names (the first). -/
def listedAt? (l : Lists) (id version : String) : Option Entry :=
  l.entries.find? fun x => x.id == id && x.version == version

/-! ## Violations (C9 reasons) -/

inductive Violation where
  | idNotCanonical
  | versionNotCanonical
  | declaredIn (actual expected : Name)
  | listedTwice
  | unlisted (path : String)
  | specNotDefinition (spec specModule : Name)
  | specNotEncodable (spec : Name)
  | flagged (c : Name) (fl : Flag)
  | obligationNotProp (o specModule : Name)
  | obligationTwice (o : Name)
  | abiNotDefinition (abi : Name)
  | abiNotBytes (abi : Name)
  | compatNotEarlier (v : String)
  | compatOtherType (v : String)
  | closureHolds (m : Name)
  | closureImports (m : Name)
  | notRegularFile (m : Name) (path : String)
  | noticeNamesNothing
  | noticeReplacement (v id : String)
  | noticeReason
  | removedListed
  | removedTwice
  | removedKind
  | removedDigest
  | removedLastCommit
  | removedToolchain
  | removedUnnamed
  | profiles
  /-- An observation the facts lack (C9: refused as load, never a pass). -/
  | unobserved (what : String)
  deriving DecidableEq, Repr

/-- C9's reason text (tested presentation). -/
def Violation.reason : Violation → String
  | .idNotCanonical => "the id is not canonical"
  | .versionNotCanonical => "the version is not canonical"
  | .declaredIn a b => s!"the entry is declared in {a}, not {b}"
  | .listedTwice => "listed twice"
  | .unlisted p => s!"its entry module {p} is not listed in Fvdep.Registry.modules"
  | .specNotDefinition n s => s!"the spec {n} is not a definition in {s}"
  | .specNotEncodable n => s!"the spec type of {n} is not encodable"
  | .flagged c fl => s!"{c} is {fl.text}"
  | .obligationNotProp o s => s!"the obligation {o} is not a Prop definition in {s}"
  | .obligationTwice o => s!"the obligation {o} is listed twice"
  | .abiNotDefinition a =>
    s!"the ABI shape {a} is not a definition in a Fvdep.Abi.V<x>_<y>_<z> module"
  | .abiNotBytes a =>
    s!"the ABI shape {a} does not take the spec to ByteArray → ByteArray or " ++
      "ByteArray → Option ByteArray"
  | .compatNotEarlier v => s!"compat {v} is not an earlier listed version"
  | .compatOtherType v => s!"compat {v} has another spec type"
  | .closureHolds m => s!"its closure holds {m}"
  | .closureImports m => s!"its closure imports {m}"
  | .notRegularFile m p => s!"the closure module {m} is not a regular file at {p}"
  | .noticeNamesNothing => "the notice names no listed or removed entry"
  | .noticeReplacement v i =>
    s!"the notice replacement {v} is not a listed or removed version of {i}"
  | .noticeReason => "the notice reason must be 1 to 65536 UTF-8 bytes without control characters"
  | .removedListed => "the removed record is still listed"
  | .removedTwice => "the removed record is recorded twice"
  | .removedKind => "the removed record must have kind operation"
  | .removedDigest => "the removed digest must be 64 lowercase hex digits"
  | .removedLastCommit => "the removed lastCommit must be 40 lowercase hex digits"
  | .removedToolchain => "the removed toolchain must not be empty"
  | .removedUnnamed => "no notice names the removed record"
  | .profiles => "profiles are not indexed yet"
  | .unobserved w => s!"no {w} observed"

/-- A refusal: its subject (C9) + violation. -/
abbrev Found := String × Violation

/-- C9's line (before the line rule, applied at the output seam). -/
def render (f : Found) : String :=
  match f.2 with
  | .unobserved w => s!"Could not load the built library: no {w} observed for {f.1}."
  | v => s!"Library error: {f.1}: {v.reason}."

def subject (id version : String) : String := id ++ "@" ++ version

/-- A check: `none` when `ok`, else the violation. -/
def fail (ok : Bool) (v : Violation) : Option Violation := if ok then none else some v

/-! ## The rows, in C9 order -/

/-- C9: a listed entry in its canonical module whose file the facts do not show (load). -/
def observedFile (F : Facts) (e : Entry) : Option Violation :=
  match canonical? e with
  | some (m, v) =>
    fail (e.module != entryModule m v || F.entryFiles.contains (modulePath e.module))
      (.unobserved "entry file")
  | none => none

/-- V5's second reason: the observed application type is one of the byte shapes. -/
def abiTypeCheck (F : Facts) (a spec : Name) : Option Violation :=
  match abiTypeOf? F a spec with
  | none => some (.unobserved "ABI application type")
  | some none => some (.abiNotBytes a)
  | some (some t) => fail (alphaEq t bytesFn || alphaEq t bytesOptFn) (.abiNotBytes a)

/-- V6's first reason: an earlier (`Ids` order) listed version of the same id. -/
def compatEarlier (l : Lists) (e : Entry) (c : String) : Bool :=
  match EntryVersion.parse c, canonical? e with
  | some cv, some (_, v) => EntryVersion.cmp cv v == .lt && (listedAt? l e.id c).isSome
  | _, _ => false

/-- V6's second reason: the kernel finds the spec types defeq. -/
def compatTypeCheck (F : Facts) (l : Lists) (e : Entry) (c : String) : Option Violation :=
  match listedAt? l e.id c with
  | none => none
  | some old =>
    match defeqOf? F e.spec old.spec with
    | none => some (.unobserved "spec type comparison")
    | some b => fail b (.compatOtherType c)

/-- An entry's rows (index `i` in `modules`): V1 → V2 → V3 (reasons, then the flags in order) →
V4 → V5 → V6 → V7 → C4. -/
def entryChecks (F : Facts) (l : Lists) (i : Nat) (e : Entry) : List (Option Violation) :=
  let S := specModule e
  let r := reach F (e.spec :: e.abi.toList)
  let cl := closure F e.module
  [fail (ModuleId.parse e.id).isSome .idNotCanonical,
      fail (EntryVersion.parse e.version).isSome .versionNotCanonical,
      (match canonical? e with
      | some (m, v) => fail (e.module == entryModule m v) (.declaredIn e.module (entryModule m v))
      | none => none),
      fail (!(l.entries.take i).any fun x => x.id == e.id && x.version == e.version) .listedTwice,
      fail ((canonical? e).isSome && specIn F e.spec S) (.specNotDefinition e.spec S),
      fail (encodable F e.spec) (.specNotEncodable e.spec)] ++
    Flag.all.map (fun fl => (least (r.filter (carries F fl))).map (.flagged · fl)) ++
    [(e.obligations.find? fun o => !((canonical? e).isSome && propIn F o S)).map
        (.obligationNotProp · S),
      (firstRepeat e.obligations).map .obligationTwice,
      (match e.abi with
      | some a => fail (abiShape F a) (.abiNotDefinition a)
      | none => none),
      (match e.abi with
      | some a => abiTypeCheck F a e.spec
      | none => none),
      (match e.compat with
      | some c => fail (compatEarlier l e c) (.compatNotEarlier c)
      | none => none),
      (match e.compat with
      | some c => compatTypeCheck F l e c
      | none => none),
      (least (cl.filter fun m => !holdsOk e.module m)).map .closureHolds,
      (least (cl.flatMap (badImports F))).map .closureImports,
      (least (cl.filter fun m => !regularFile F m)).map fun m => .notRegularFile m (modulePath m)]

/-- V8: a listed or removed (id, version). -/
def known (l : Lists) (id version : String) : Bool :=
  l.entries.any (fun e => e.id == id && e.version == version) ||
    l.removed.any fun r => r.id == id && r.version == version

def noticeChecks (l : Lists) (n : Notice) : List (Option Violation) :=
  [fail (known l n.id n.version) .noticeNamesNothing,
    (match n.replacement with
    | some r => fail (r != n.version && known l n.id r) (.noticeReplacement r n.id)
    | none => none),
    fail (FvdepCore.Doc.isText 65536 n.reason) .noticeReason]

/-- V9 (record `k` of `removed`). -/
def removedChecks (l : Lists) (k : Nat) (r : Removed) : List (Option Violation) :=
  [fail (!l.entries.any fun e => e.id == r.id && e.version == r.version) .removedListed,
    fail (!(l.removed.take k).any fun x => x.id == r.id && x.version == r.version) .removedTwice,
    fail (r.kind == .operation) .removedKind, fail (FvdepCore.Doc.isDigest r.digest) .removedDigest,
    fail (Commit.parse r.lastCommit).isSome .removedLastCommit,
    fail (!r.toolchain.isEmpty) .removedToolchain,
    fail (l.notices.any fun n => n.id == r.id && n.version == r.version) .removedUnnamed]

/-- `Dep` → `dep`, `EncodeUrl` → `encode_url` (an id segment from its Lean module part). -/
def decamel (s : String) : String :=
  String.ofList <|
    (s.toList.foldl
        (fun (acc : List Char × Bool) c =>
          if c.isUpper then (c.toLower :: (if acc.2 then acc.1 else '_' :: acc.1), false)
          else (c :: acc.1, false))
        ([], true)).1.reverse

/-- The id + version an entry file's path spells (`Fvdep/Registry/<Dep>/<Op>/V<x>_<y>_<z>.lean`),
else the path itself. -/
def spelled (p : String) : String :=
  match p.splitOn "/" with
  | ["Fvdep", "Registry", dep, op, file] =>
    match file.toList with
    | 'V' :: rest =>
      let v := (rest.take (rest.length - 5)).map fun c => if c == '_' then '.' else c
      subject (decamel dep ++ "." ++ decamel op) (String.ofList v)
    | _ => p
  | _ => p

/-- Paths in UTF-8 byte order. -/
def sortPaths (ps : List String) : List String := ps.mergeSort fun a b => !lexLt b.toList a.toList

/-- Every row of the registry lists, in C9 order: the entries' observed files; each entry's rows
(`modules` order); the unlisted entry files (path order); `notices`; `removed`; `profiles`. -/
def checks (F : Facts) (l : Lists) : List (Option Found) :=
  l.entries.map (fun e => (observedFile F e).map (subject e.id e.version, ·)) ++
    (l.entries.zipIdx.flatMap fun p =>
      (entryChecks F l p.2 p.1).map (·.map (subject p.1.id p.1.version, ·))) ++
    (sortPaths F.entryFiles).map
      (fun p =>
        if l.entries.any (modulePath ·.module == p) then none else some (spelled p, .unlisted p)) ++
    l.notices.flatMap (fun n => (noticeChecks l n).map (·.map (subject n.id n.version, ·))) ++
    (l.removed.zipIdx.flatMap fun p =>
      (removedChecks l p.2 p.1).map (·.map (subject p.1.id p.1.version, ·))) ++
    [(fail (l.profiles == 0) .profiles).map ("Fvdep.Registry.profiles", ·)]

/-- C3 + C9: the first violation of the registry lists, `none` when every rule holds. -/
def validate (F : Facts) (l : Lists) : Option Found := ((checks F l).filterMap id).head?

end FvdepCore.Index.Rules
