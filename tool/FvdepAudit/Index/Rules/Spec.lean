import FvdepCore.Index.Rules

/-! C3 V1–V10 + C4's file check in C9's order, written apart (contract
`docs/contracts/U4-library.md` C3, C4, C9): each row = the condition that passes it + what a
refusal there reports; the relations the checks decide — `ConstReach` (V3: through library
definition values), `ImportReach` (C4's closure), `HasFlag`, `IsLeast` (the least printed name),
alpha-equivalence = equality after `erase`.
Shared with the shipped code: lookups (`libDecl?`, `companion?`, `modFacts?`, `abiTypeOf?`,
`defeqOf?`, `listedAt?`) + naming data (`canonical?`, `entryModule`, `specModule`, `modulePath`,
`versionedPart`, `spelled`, `sortPaths`, `subject`, `key`/`lexLt`, `erase`). -/

namespace FvdepAudit.Index.Rules.Spec

open Lean FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules

/-- The constant `n` occurs as a `.const` node of `e`. -/
def Mentions : Expr → Name → Prop
  | .const c _, n => c = n
  | .app f a, n => Mentions f n ∨ Mentions a n
  | .lam _ t b _, n => Mentions t n ∨ Mentions b n
  | .forallE _ t b _, n => Mentions t n ∨ Mentions b n
  | .letE _ t v b _, n => Mentions t n ∨ Mentions v n ∨ Mentions b n
  | .mdata _ e, n => Mentions e n
  | .proj _ _ e, n => Mentions e n
  | _, _ => False

/-- C3 V3: `c` is reached from `roots` (roots included) through library definition values (a
theorem's or an opaque constant's value is never walked). -/
inductive ConstReach (F : Facts) (roots : List Name) : Name → Prop
  | root {c : Name} : c ∈ roots → ConstReach F roots c
  |
  step {c n : Name} {d : Decl} {v : Expr} :
    ConstReach F roots c →
      libDecl? F c = some d →
      d.kind = .defn → d.value = some v → Mentions v n → ConstReach F roots n

/-- C4: `m` is in `M`'s closure — `M`, or an `Fvdep` module a closure module imports. -/
inductive ImportReach (F : Facts) (M : Name) : Name → Prop
  | self : ImportReach F M M
  |
  step {a b : Name} {x : ModFacts} :
    ImportReach F M a →
      modFacts? F a = some x → b ∈ x.imports → b.getRoot = `Fvdep → ImportReach F M b

/-- Lean's own compiled form of `c` (`<c>._unsafe_rec`, a definition of partial safety). -/
def LeanForm (x : Decl) : Prop := x.kind = .defn ∧ x.safety = .partial

/-- C3 V3: the flags as the contract defines them. -/
def HasFlag (F : Facts) (d : Decl) : Flag → Prop
  | .partial =>
    d.safety = .partial ∨ d.kind = .opaque ∧ ∃ x, companion? F d.name = some x ∧ LeanForm x
  | .unsafe => d.safety = .unsafe
  | .implementedBy => d.implementedBy = true ∨ ∃ x, companion? F d.name = some x ∧ ¬LeanForm x
  | .extern => d.isExtern = true
  | .opaque => d.kind = .opaque
  | .noncomputable => d.isNoncomputable = true

/-- C9: `c` has `P`, and no `c'` with `P` has a strictly smaller printed name. -/
def IsLeast (P : Name → Prop) (c : Name) : Prop := P c ∧ ∀ c', P c' → lexLt (key c') (key c) = false

/-- A row of C9's order: the condition that passes it + the refusals it may report. -/
abbrev Row := Prop × (Found → Prop)

/-- Passes when `P`; a refusal there reports exactly `f`. -/
def row (P : Prop) (f : Found) : Row := (P, (· = f))

/-- Passes when nothing has `P`; a refusal there reports its least carrier. -/
def leastRow (P : Name → Prop) (report : Name → Found) : Row :=
  (∀ c, ¬P c, fun f => ∃ c, IsLeast P c ∧ f = report c)

/-- V3: checked — an entry's roots + the library constants their definition values reach. -/
def Checked (F : Facts) (e : Entry) (c : Name) : Prop :=
  ConstReach F (e.spec :: e.abi.toList) c ∧ libDecl? F c ≠ none

/-- V4: `S.<name>` for the entry's spec module `S`, a definition declared in `S` of type exactly
`Prop`. -/
def PropObligation (F : Facts) (e : Entry) (o : Name) : Prop :=
  canonical? e ≠ none ∧
    (∃ name, o = .str (specModule e) name) ∧
    ∃ d,
      libDecl? F o = some d ∧ d.kind = .defn ∧ d.module = specModule e ∧ erase d.type = .sort .zero

/-- V5: a definition of a module `Fvdep.Abi.V<x>_<y>_<z>`. -/
def AbiShape (F : Facts) (a : Name) : Prop :=
  ∃ d s,
    libDecl? F a = some d ∧ d.kind = .defn ∧ d.module = .str `Fvdep.Abi s ∧ versionedPart s = true

/-- V6: an earlier (`Ids` order) listed version of the same id. -/
def CompatEarlier (l : Lists) (e : Entry) (c : String) : Prop :=
  ∃ cv m v,
    EntryVersion.parse c = some cv ∧
      canonical? e = some (m, v) ∧ EntryVersion.cmp cv v = .lt ∧ listedAt? l e.id c ≠ none

/-- V7: what a closure may hold. -/
def HoldsOk (M m : Name) : Prop :=
  m = M ∨
    m = `Fvdep.Registry.Types.V1 ∨
    versionedName m = true ∧ (`Fvdep.Registry.ProfileTypes).isPrefixOf m = false

/-- V7: an import inside Init, Std + the library. -/
def ImportOk (i : Name) : Prop := i.getRoot = `Init ∨ i.getRoot = `Std ∨ i.getRoot = `Fvdep

/-- C9 (load): a listed entry in its canonical module has its file among the entry files. -/
def observedRow (F : Facts) (e : Entry) : Row :=
  row
    (∀ m v,
      canonical? e = some (m, v) → e.module = entryModule m v → modulePath e.module ∈ F.entryFiles)
    (subject e.id e.version, .unobserved "entry file")

/-- An entry's rows: V1 → V2 → V3 (reasons, then each flag in order) → V4 → V5 → V6 → V7 → C4. -/
def entryRows (F : Facts) (l : Lists) (i : Nat) (e : Entry) : List Row :=
  let s := subject e.id e.version
  let S := specModule e
  [row (ModuleId.parse e.id ≠ none) (s, .idNotCanonical),
      row (EntryVersion.parse e.version ≠ none) (s, .versionNotCanonical),
      (∀ m v, canonical? e = some (m, v) → e.module = entryModule m v, fun f =>
        ∃ m v, canonical? e = some (m, v) ∧ f = (s, .declaredIn e.module (entryModule m v))),
      row (∀ x ∈ l.entries.take i, ¬(x.id = e.id ∧ x.version = e.version)) (s, .listedTwice),
      row
        (canonical? e ≠ none ∧
          (∃ fn, e.spec = .str S fn) ∧
          ∃ d, libDecl? F e.spec = some d ∧ d.kind = .defn ∧ d.module = S)
        (s, .specNotDefinition e.spec S),
      row (∃ d sig, libDecl? F e.spec = some d ∧ FvdepCore.Protocol.sigOf d.type = some sig)
        (s, .specNotEncodable e.spec)] ++
    Flag.all.map
      (fun fl =>
        leastRow (fun c => Checked F e c ∧ ∃ d, libDecl? F c = some d ∧ HasFlag F d fl) fun c =>
          (s, .flagged c fl)) ++
    [(∀ o ∈ e.obligations, PropObligation F e o, fun f =>
        ∃ pre o post,
          e.obligations = pre ++ o :: post ∧
            (∀ o' ∈ pre, PropObligation F e o') ∧
            ¬PropObligation F e o ∧ f = (s, .obligationNotProp o S)),
      (e.obligations.Nodup, fun f =>
        ∃ pre o post,
          e.obligations = pre ++ o :: post ∧ pre.Nodup ∧ o ∈ pre ∧ f = (s, .obligationTwice o)),
      (∀ a, e.abi = some a → AbiShape F a, fun f =>
        ∃ a, e.abi = some a ∧ f = (s, .abiNotDefinition a)),
      (∀ a,
          e.abi = some a →
            ∃ t,
              abiTypeOf? F a e.spec = some (some t) ∧
                (erase t = erase bytesFn ∨ erase t = erase bytesOptFn),
        fun f =>
        ∃ a,
          e.abi = some a ∧
            (abiTypeOf? F a e.spec = none ∧ f = (s, .unobserved "ABI application type") ∨
              abiTypeOf? F a e.spec ≠ none ∧ f = (s, .abiNotBytes a))),
      (∀ c, e.compat = some c → CompatEarlier l e c, fun f =>
        ∃ c, e.compat = some c ∧ f = (s, .compatNotEarlier c)),
      (∀ c,
          e.compat = some c →
            ∀ old, listedAt? l e.id c = some old → defeqOf? F e.spec old.spec = some true,
        fun f =>
        ∃ c,
          e.compat = some c ∧
            ∃ old,
              listedAt? l e.id c = some old ∧
                (defeqOf? F e.spec old.spec = none ∧ f = (s, .unobserved "spec type comparison") ∨
                  defeqOf? F e.spec old.spec = some false ∧ f = (s, .compatOtherType c))),
      leastRow (fun m => ImportReach F e.module m ∧ ¬HoldsOk e.module m) fun m =>
        (s, .closureHolds m),
      leastRow
        (fun i =>
          ∃ m x, ImportReach F e.module m ∧ modFacts? F m = some x ∧ i ∈ x.imports ∧ ¬ImportOk i)
        fun i => (s, .closureImports i),
      leastRow (fun m => ImportReach F e.module m ∧ ∀ x, modFacts? F m = some x → x.file = none)
        fun m => (s, .notRegularFile m (modulePath m))]

/-- V8: a listed or removed (id, version). -/
def Known (l : Lists) (id version : String) : Prop :=
  (∃ e ∈ l.entries, e.id = id ∧ e.version = version) ∨
    ∃ r ∈ l.removed, r.id = id ∧ r.version = version

/-- V8: 1 to 65,536 UTF-8 bytes without a Unicode `Cc` character. -/
def ReasonText (s : String) : Prop :=
  1 ≤ s.utf8ByteSize ∧
    s.utf8ByteSize ≤ 65536 ∧ ∀ c ∈ s.toList, ¬(c.toNat < 32 ∨ 127 ≤ c.toNat ∧ c.toNat ≤ 159)

def noticeRows (l : Lists) (n : Notice) : List Row :=
  let s := subject n.id n.version
  [row (Known l n.id n.version) (s, .noticeNamesNothing),
    (∀ r, n.replacement = some r → r ≠ n.version ∧ Known l n.id r, fun f =>
      ∃ r, n.replacement = some r ∧ f = (s, .noticeReplacement r n.id)),
    row (ReasonText n.reason) (s, .noticeReason)]

/-- V9: `n` lowercase hex digits. -/
def LowerHex (s : String) (n : Nat) : Prop :=
  s.length = n ∧ ∀ c ∈ s.toList, '0' ≤ c ∧ c ≤ '9' ∨ 'a' ≤ c ∧ c ≤ 'f'

def removedRows (l : Lists) (k : Nat) (r : Removed) : List Row :=
  let s := subject r.id r.version
  [row (¬∃ e ∈ l.entries, e.id = r.id ∧ e.version = r.version) (s, .removedListed),
    row (∀ x ∈ l.removed.take k, ¬(x.id = r.id ∧ x.version = r.version)) (s, .removedTwice),
    row (r.kind = .operation) (s, .removedKind), row (LowerHex r.digest 64) (s, .removedDigest),
    row (Commit.parse r.lastCommit ≠ none) (s, .removedLastCommit),
    row (r.toolchain ≠ "") (s, .removedToolchain),
    row (∃ n ∈ l.notices, n.id = r.id ∧ n.version = r.version) (s, .removedUnnamed)]

/-- C9's order: the entries' observed files; each entry's rows (`modules` order); the unlisted
entry files (path byte order); `notices`; `removed`; `profiles` (V10). -/
def specChecks (F : Facts) (l : Lists) : List Row :=
  l.entries.map (observedRow F) ++ (l.entries.zipIdx.flatMap fun p => entryRows F l p.2 p.1) ++
    (sortPaths F.entryFiles).map
      (fun p => row (∃ e ∈ l.entries, modulePath e.module = p) (spelled p, .unlisted p)) ++
    l.notices.flatMap (noticeRows l) ++
    (l.removed.zipIdx.flatMap fun p => removedRows l p.2 p.1) ++
    [row (l.profiles = 0) ("Fvdep.Registry.profiles", .profiles)]

/-- C3: every rule holds. -/
def RegistryValid (F : Facts) (l : Lists) : Prop := ∀ r ∈ specChecks F l, r.1

/-- C9: `f` = what the first failing row reports. -/
def FirstFail (rs : List Row) (f : Found) : Prop :=
  ∃ pre r post, rs = pre ++ r :: post ∧ (∀ x ∈ pre, x.1) ∧ ¬r.1 ∧ r.2 f

end FvdepAudit.Index.Rules.Spec
