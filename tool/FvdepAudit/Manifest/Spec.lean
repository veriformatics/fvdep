import FvdepAudit.Doc.Spec
import FvdepIO.Toml

/-! Specs for `fvdep.toml` (contract `docs/contracts/U3-codecs.md` T1–T5), written from the contract
apart from `FvdepCore.Manifest` + `FvdepIO.Toml`'s code: valid UTF-8 + the text stage (T1), Lake's
table ↔ `Tree` (T1), field syntax + `WellFormed` (T2, T3), acceptance = the trees that spell a
well-formed manifest (T3), the refusal order as the list of EVERY violation (T3 + D5; the first is
reported), the canonical bytes (T4) + the TOML 1.0 subset they belong to (T5 `TomlText`). Shared
with the code: the types, D2's argv syntax (`Argv`, `ArgText`) + module id + version spellings
(U2's canonical parsers). `String` order = UTF-8 byte order, so "key byte order" = ascending
`String`s. -/

namespace FvdepAudit.Manifest.Spec

noncomputable section

open Classical
open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Manifest
open FvdepAudit.Doc.Spec

/-! ## T1 text stage -/

/-- T1: bytes core's UTF-8 decoder accepts. -/
def ValidUtf8 (b : ByteArray) : Prop := (String.fromUTF8? b).isSome = true

/-- T1: `b` begins with the byte order mark EF BB BF. -/
def Bom (b : ByteArray) : Prop := b.data.toList.take 3 = [0xEF, 0xBB, 0xBF]

/-- T1 + T5 `TextStage`: size first (> 65,536 bytes), then a BOM, then the first UTF-8 offset, else
the text whose UTF-8 bytes are `b`. -/
def TextSpec (b : ByteArray) (r : Except TextError String) : Prop :=
  if 65536 < b.size then r = .error .tooLarge
  else
    if Bom b then r = .error .bom
    else
      match utf8ErrorOffset b with
      | some k => r = .error (.utf8 k)
      | none => ∃ s, r = .ok s ∧ s.toUTF8 = b

/-! ## T1 Lake's table ↔ `Tree` -/

mutual
/-- T1 + T5: `t` rebuilds Lake's value `v`: the same constructor + scalar payload, elements in
order, members in order with each key = its name's one string component; floats + date-times as
their tags. -/
def LakeRel : Lake.Toml.Value → Tree → Prop
  | .string _ s, t => t = .str s
  | .integer _ n, t => t = .int n
  | .float .., t => t = .other .float
  | .boolean _ b, t => t = .bool b
  | .dateTime .., t => t = .other .dateTime
  | .array _ xs, t => ∃ ts, t = .arr ts ∧ LakeRels xs.toList ts
  | .table' _ d, t => ∃ ms, t = .tbl ms ∧ LakeMembers d.items.toList ms
def LakeRels : List Lake.Toml.Value → List Tree → Prop
  | [], ts => ts = []
  | x :: xs, ts => ∃ t ts', ts = t :: ts' ∧ LakeRel x t ∧ LakeRels xs ts'
  def LakeMembers : List (Lean.Name × Lake.Toml.Value) → List (String × Tree) → Prop
    | [], ms => ms = []
    | (n, x) :: xs, ms =>
      ∃ s t ms', ms = (s, t) :: ms' ∧ n = .str .anonymous s ∧ LakeRel x t ∧ LakeMembers xs ms'
end

mutual
/-- Every key inside `v`, pre-order. -/
def keysIn : Lake.Toml.Value → List Lean.Name
  | .array _ xs => keysInList xs.toList
  | .table' _ d => keysInMembers d.items.toList
  | _ => []
def keysInList : List Lake.Toml.Value → List Lean.Name
  | [] => []
  | x :: xs => keysIn x ++ keysInList xs
def keysInMembers : List (Lean.Name × Lake.Toml.Value) → List Lean.Name
  | [] => []
  | (n, x) :: xs => n :: keysIn x ++ keysInMembers xs
end

/-- T1: a key `ofLake` cannot turn into a string: any name but one string component. -/
def BadKey (d : Lake.Toml.Table) (n : Lean.Name) : Prop :=
  n ∈ keysInMembers d.items.toList ∧ ∀ s, n ≠ .str .anonymous s

/-! ## T3 field syntax -/

def Letter (c : Char) : Prop := 'A' ≤ c ∧ c ≤ 'Z' ∨ 'a' ≤ c ∧ c ≤ 'z'

/-- T3: one name component `[A-Za-z_][A-Za-z0-9_']*`. -/
def Component (cs : List Char) : Prop :=
  ∃ c rest,
    cs = c :: rest ∧ (Letter c ∨ c = '_') ∧ ∀ x ∈ rest, Letter x ∨ Digit x ∨ x = '_' ∨ x = '\''

/-- `docs/library.md` Naming: a reserved first component (`Init`, `Std`, `Lean`, `Lake`, or a name
starting with `Fvdep`). -/
def ReservedHead (h : String) : Prop := h ∈ ["Init", "Std", "Lean", "Lake"] ∨ h.startsWith "Fvdep"

/-- T3: a module name: components joined by `.`, ≤ 256 UTF-8 bytes, first component not reserved. -/
def ModuleName (s : String) : Prop :=
  s.utf8ByteSize ≤ 256 ∧
    ∃ h rest,
      s.toList = ['.'].intercalate (h :: rest) ∧
        Component h ∧ (∀ c ∈ rest, Component c) ∧ ¬ReservedHead (String.ofList h)

/-- T3: a constant name: components joined by `.`, ≤ 1,024 UTF-8 bytes. -/
def ConstName (s : String) : Prop :=
  s.utf8ByteSize ≤ 1024 ∧ ∃ cs, cs ≠ [] ∧ s.toList = ['.'].intercalate cs ∧ ∀ c ∈ cs, Component c

/-- T3: an entry version's canonical spelling within D2's bound. -/
def VersionText (s : String) : Prop := ∃ x : EntryVersion, s = toString x ∧ SpellingFits s

/-- T3: a module id's canonical spelling within D2's bound. -/
def IdText (s : String) : Prop := ∃ m : ModuleId, s = toString m ∧ SpellingFits s

/-- T3: a module list: nonempty, no repeats, every element a module name. -/
def ModuleList (xs : List String) : Prop := xs ≠ [] ∧ xs.Nodup ∧ ∀ x ∈ xs, ModuleName x

/-! ## T2 + T3 well-formed manifests -/

def entryId (e : Entry) : String := toString e.decl.module

/-- T2 + T3: a proof entry has a shape, both constants + both module lists (disjoint), no adapter;
a differential entry has the adapter argv (D2) alone. -/
def EntryWF (e : Entry) : Prop :=
  let d := e.decl
  SpellingFits (toString d.module) ∧
    SpellingFits (toString d.version) ∧
    match d.kind with
    | .proof =>
      d.shape ≠ none ∧
        (∃ i, d.impl = some i ∧ ConstName i) ∧
        (∃ x, d.proof = some x ∧ ConstName x) ∧
        d.adapter = none ∧
        ModuleList e.implModules ∧
        ModuleList e.proofModules ∧ ∀ x ∈ e.implModules, x ∉ e.proofModules
    | .differential =>
      d.shape = none ∧
        d.impl = none ∧
        d.proof = none ∧
        (∃ argv, d.adapter = some argv ∧ Argv argv) ∧ e.implModules = [] ∧ e.proofModules = []

/-- T2: every entry well-formed; module ids strictly ascending in byte order. -/
def WellFormed (m : ManifestFile) : Prop :=
  (∀ e ∈ m.modules, EntryWF e) ∧ (m.modules.map entryId).Pairwise (· < ·)

/-! ## T3 acceptance: the trees that spell a manifest (member order free) -/

def shapeWord : Option Shape → String
  | some .fn => "fn"
  | some .abi => "abi"
  | none => ""

def policyWord : Policy → String
  | .required => "required"
  | .development => "development"

/-- T3: an entry's members (interface §7), in byte order. -/
def entryLayout (e : Entry) : List (String × Tree) :=
  let d := e.decl
  match d.kind with
  | .proof =>
    [("impl", .str (d.impl.getD "")), ("impl_modules", .arr (e.implModules.map .str)),
      ("proof", .str (d.proof.getD "")), ("proof_modules", .arr (e.proofModules.map .str)),
      ("shape", .str (shapeWord d.shape)), ("version", .str (toString d.version))]
  | .differential =>
    [("adapter", .arr ((d.adapter.getD []).map .str)), ("evidence", .str "differential"),
      ("version", .str (toString d.version))]

/-- T3: the root's `[policy]` member spells `p`: absent, empty, or `proof = "<p>"`. -/
def PolicySpells (o : Option Tree) (p : Policy) : Prop :=
  o = none ∧ p = .required ∨
    o = some (.tbl []) ∧ p = .required ∨ o = some (.tbl [("proof", .str (policyWord p))])

/-- T3: the root's `[modules]` member spells `es`: absent with no entries, or a table holding
exactly one member per entry, keyed by its id, holding exactly the entry's members in any order. -/
def ModulesSpell (o : Option Tree) (es : List Entry) : Prop :=
  o = none ∧ es = [] ∨
    ∃ ms,
      o = some (.tbl ms) ∧
        (ms.map (·.1)).Perm (es.map entryId) ∧
        ∀ e ∈ es, ∃ fs, ms.lookup (entryId e) = some (.tbl fs) ∧ fs.Perm (entryLayout e)

/-- T3: `t` spells `m`: a table with distinct keys ⊆ {schema, library, policy, modules},
`schema = 1`, `[library]` = exactly `commit = "<m.library>"`, + the policy + modules members. -/
def Spells (t : Tree) (m : ManifestFile) : Prop :=
  ∃ ms,
    t = .tbl ms ∧
      (ms.map (·.1)).Nodup ∧
      (∀ k ∈ ms.map (·.1), k ∈ ["library", "modules", "policy", "schema"]) ∧
      ms.lookup "schema" = some (.int 1) ∧
      ms.lookup "library" = some (.tbl [("commit", .str (toString m.library))]) ∧
      PolicySpells (ms.lookup "policy") m.policy ∧ ModulesSpell (ms.lookup "modules") m.modules

/-- T3's acceptance: `t` spells the well-formed manifest `m`. -/
def ManifestSpec (t : Tree) (m : ManifestFile) : Prop := WellFormed m ∧ Spells t m

/-! ## T3 + D5 refusals: every violation, in order -/

/-- Members in key byte order (equal keys stable). -/
def sorted (ms : List (String × Tree)) : List (String × Tree) :=
  ms.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- The keys that occur more than once. -/
def repeated (ks : List String) : List String := ks.filter fun k => 2 ≤ ks.count k

/-- T3, before a table's other rules: its least repeated key, alone. -/
def dupSpec (p : List PathSeg) (ms : List (String × Tree)) : Option ManifestError :=
  match repeated (ms.map (·.1)) with
  | k :: ks => some ⟨p, .duplicateKey (FvdepAudit.Json.Spec.least k ks)⟩
  | [] => none

/-- D5 (b): every member whose key the table does not define, in key byte order. -/
def unknownMembers (known : List String) (p : List PathSeg) (ms : List (String × Tree)) :
    List ManifestError :=
  ((sorted ms).filter fun m => m.1 ∉ known).map fun m => ⟨p ++ [.key m.1], .unknownField⟩

/-- D5 (c): every member whose key only the other entry kind defines, in key byte order. -/
def forbiddenSpec (forbidden : List String) (p : List PathSeg) (ms : List (String × Tree)) :
    List ManifestError :=
  ((sorted ms).filter fun m => m.1 ∈ forbidden).map fun m => ⟨p ++ [.key m.1], .forbiddenField⟩

/-- D5 (d): every required key (listed in byte order) the table lacks. -/
def missingMembers (req : List String) (p : List PathSeg) (ms : List (String × Tree)) :
    List ManifestError :=
  (req.filter fun k => ms.lookup k = none).map fun k => ⟨p ++ [.key k], .missingField⟩

/-- T3: a string field: a non-string → `wrong_type` (string), a string breaking `rule` →
`bad_value`. -/
def strSpec (rule : String → Prop) (p : List PathSeg) : Tree → List ManifestError
  | .str s => if rule s then [] else [⟨p, .badValue⟩]
  | _ => [⟨p, .wrongType .string⟩]

/-- T3: each element from index `i` on, by index: a non-string → `wrong_type`, a string breaking
`rule` at its index → `bad_value`. -/
def elemsSpec (rule : Nat → String → Prop) (p : List PathSeg) : Nat → List Tree → List ManifestError
  | _, [] => []
  | i, x :: xs =>
    (match x with
      | .str s => if rule i s then [] else [⟨p ++ [.index i], .badValue⟩]
      | _ => [⟨p ++ [.index i], .wrongType .string⟩]) ++
      elemsSpec rule p (i + 1) xs

/-- T3: every string element equal to an earlier element (`seen` = the elements before index `i`),
by index. -/
def repeatsSpec (p : List PathSeg) (seen : List Tree) : Nat → List Tree → List ManifestError
  | _, [] => []
  | i, x :: xs =>
    (match x with
      | .str _ => if x ∈ seen then [⟨p ++ [.index i], .badValue⟩] else []
      | _ => []) ++
      repeatsSpec p (seen ++ [x]) (i + 1) xs

/-- T3: an array field, judged kind → nonempty → elements → repeats (`unique` lists alone). -/
def arraySpec (rule : Nat → String → Prop) (unique : Bool) (p : List PathSeg) :
    Tree → List ManifestError
  | .arr [] => [⟨p, .badValue⟩]
  | .arr xs => elemsSpec rule p 0 xs ++ if unique then repeatsSpec p [] 0 xs else []
  | _ => [⟨p, .wrongType .array⟩]

/-- T3: a member's string elements. -/
def stringsSpec : Option Tree → List String
  | some (.arr xs) =>
    xs.filterMap fun x =>
      match x with
      | .str s => some s
      | _ => none
  | _ => []

/-- T3 (e): an entry member's value. -/
def entryValueSpec (p : List PathSeg) (k : String) (v : Tree) : List ManifestError :=
  if k = "adapter" then arraySpec (fun i s => ArgText (decide (i = 0)) s) false (p ++ [.key k]) v
  else
    if k = "impl" ∨ k = "proof" then strSpec ConstName (p ++ [.key k]) v
    else
      if k = "impl_modules" ∨ k = "proof_modules" then
        arraySpec (fun _ => ModuleName) true (p ++ [.key k]) v
      else
        if k = "shape" then strSpec (· ∈ ["fn", "abi"]) (p ++ [.key k]) v
        else if k = "version" then strSpec VersionText (p ++ [.key k]) v else []

/-- T3 (a): an entry's discriminator `evidence`: absent = proof, "differential" = differential, a
non-string → `wrong_type` (string), another string → `bad_value`. -/
def evidenceSpec (p : List PathSeg) (ms : List (String × Tree)) : Except ManifestError Kind :=
  match ms.lookup "evidence" with
  | none => .ok .proof
  | some (.str s) =>
    if s = "differential" then .ok .differential else .error ⟨p ++ [.key "evidence"], .badValue⟩
  | some _ => .error ⟨p ++ [.key "evidence"], .wrongType .string⟩

/-- T3: every key an entry may hold. -/
def entryKeySet : List String :=
  ["adapter", "evidence", "impl", "impl_modules", "proof", "proof_modules", "shape", "version"]

/-- T3: an entry kind's required keys (byte order). -/
def requiredFor : Kind → List String
  | .proof => ["impl", "impl_modules", "proof", "proof_modules", "shape", "version"]
  | .differential => ["adapter", "evidence", "version"]

/-- T3: an entry kind's forbidden keys (those only the other kind defines). -/
def forbiddenFor : Kind → List String
  | .proof => ["adapter"]
  | .differential => ["impl", "impl_modules", "proof", "proof_modules", "shape"]

/-- T3 (f): every `impl_modules` element (index order) `proof_modules` also lists. -/
def overlapSpec (p : List PathSeg) (ms : List (String × Tree)) : List ManifestError :=
  ((stringsSpec (ms.lookup "impl_modules")).filter fun x =>
        x ∈ stringsSpec (ms.lookup "proof_modules")).map
    fun x => ⟨p, .inBothLists x⟩

/-- T3: one `[modules."<id>"]` entry: a table (else `wrong_type`); its repeat alone; its
discriminator alone; else unknown, forbidden, missing members, member values in key byte order
(`evidence` judged in (a)), the list overlap. -/
def entrySpec (p : List PathSeg) : Tree → List ManifestError
  | .tbl ms =>
    match dupSpec p ms with
    | some e => [e]
    | none =>
      match evidenceSpec p ms with
      | .error e => [e]
      | .ok kind =>
        unknownMembers entryKeySet p ms ++ forbiddenSpec (forbiddenFor kind) p ms ++
          missingMembers (requiredFor kind) p ms ++
          ((sorted ms).flatMap fun m => entryValueSpec p m.1 m.2) ++
          overlapSpec p ms
  | _ => [⟨p, .wrongType .table⟩]

/-- T3: `[modules]`: a table (else `wrong_type`); its repeat alone; else per member in key byte
order: a key that is no module id → `bad_value` at the key, else the entry's violations. -/
def modulesSpec (p : List PathSeg) : Tree → List ManifestError
  | .tbl ms =>
    match dupSpec p ms with
    | some e => [e]
    | none =>
      (sorted ms).flatMap fun m =>
        if IdText m.1 then entrySpec (p ++ [.key m.1]) m.2 else [⟨p ++ [.key m.1], .badValue⟩]
  | _ => [⟨p, .wrongType .table⟩]

/-- T3: `[library]` / `[policy]`: a table (else `wrong_type`); its repeat alone; else unknown keys,
missing keys, then `key`'s value by `rule`. -/
def plainSpec (key : String) (required : Bool) (rule : String → Prop) (p : List PathSeg) :
    Tree → List ManifestError
  | .tbl ms =>
    match dupSpec p ms with
    | some e => [e]
    | none =>
      unknownMembers [key] p ms ++ missingMembers (if required then [key] else []) p ms ++
        (sorted ms).flatMap fun m => if m.1 = key then strSpec rule (p ++ [.key m.1]) m.2 else []
  | _ => [⟨p, .wrongType .table⟩]

/-- T3 (e): a root member's value. -/
def rootValueSpec (k : String) (v : Tree) : List ManifestError :=
  if k = "library" then plainSpec "commit" true (fun s => ∃ c : Commit, s = toString c) [.key k] v
  else
    if k = "modules" then modulesSpec [.key k] v
    else
      if k = "policy" then plainSpec "proof" false (· ∈ ["required", "development"]) [.key k] v
      else []

/-- T3 + D5: every violation of `t` in order: the root's kind; its repeat alone; its discriminator
`schema` alone (absent → `missing_field`, a non-integer → `wrong_type`, ≠ 1 → `bad_value`); else
unknown keys, `library` missing, then each member's value in key byte order. -/
def allViolations : Tree → List ManifestError
  | .tbl ms =>
    match dupSpec [] ms with
    | some e => [e]
    | none =>
      match ms.lookup "schema" with
      | none => [⟨[.key "schema"], .missingField⟩]
      | some (.int n) =>
        if n = 1 then
          unknownMembers ["library", "modules", "policy", "schema"] [] ms ++
            missingMembers ["library"] [] ms ++
            (sorted ms).flatMap fun m => rootValueSpec m.1 m.2
        else [⟨[.key "schema"], .badValue⟩]
      | some _ => [⟨[.key "schema"], .wrongType .integer⟩]
  | _ => [⟨[], .wrongType .table⟩]

/-- T3 + D5: the reported refusal = the first violation. -/
def firstViolation (t : Tree) : Option ManifestError := (allViolations t).head?

/-! ## T4 canonical bytes -/

/-- An uppercase hex digit. -/
def hexDigitU (n : Nat) : Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'].getD n '0'

/-- T4: a scalar inside a basic string: `"` + `\` escaped, U+0008/0009/000A/000C/000D as `\b` `\t`
`\n` `\f` `\r`, every other U+0000–U+001F + U+007F as `\u00XX`, every other scalar itself. -/
def escSpec (c : Char) : List Char :=
  match c.toNat with
  | 0x22 => ['\\', '"']
  | 0x5C => ['\\', '\\']
  | 0x08 => ['\\', 'b']
  | 0x09 => ['\\', 't']
  | 0x0A => ['\\', 'n']
  | 0x0C => ['\\', 'f']
  | 0x0D => ['\\', 'r']
  | n =>
    if n < 0x20 ∨ n = 0x7F then ['\\', 'u', '0', '0', hexDigitU (n / 16), hexDigitU (n % 16)]
    else [c]

/-- T4: a basic string. -/
def quoted (s : String) : List Char := '"' :: s.toList.flatMap escSpec ++ ['"']

/-- T4: `key = value` + LF. -/
def lineSpec (k : String) (v : List Char) : List Char := k.toList ++ " = ".toList ++ v ++ ['\n']

/-- T4: an array of strings, `["a", "b"]`. -/
def arraySpecText (xs : List String) : List Char :=
  '[' :: [',', ' '].intercalate (xs.map quoted) ++ [']']

/-- T4: an entry's lines in the order version, evidence (differential), shape, impl_modules,
proof_modules, impl, proof, adapter (present ones). -/
def entryLines (e : Entry) : List Char :=
  let d := e.decl
  lineSpec "version" (quoted (toString d.version)) ++
    (if d.kind = .differential then lineSpec "evidence" (quoted "differential") else []) ++
    (if d.shape = none then [] else lineSpec "shape" (quoted (shapeWord d.shape))) ++
    (if d.kind = .proof then
      lineSpec "impl_modules" (arraySpecText e.implModules) ++
        lineSpec "proof_modules" (arraySpecText e.proofModules)
    else []) ++
    (match d.impl with
    | some i => lineSpec "impl" (quoted i)
    | none => []) ++
    (match d.proof with
    | some x => lineSpec "proof" (quoted x)
    | none => []) ++
    match d.adapter with
    | some a => lineSpec "adapter" (arraySpecText a)
    | none => []

/-- T4: `schema = 1`, blank, `[library]`, `commit`, blank, `[policy]`, `proof`, then per entry a
blank line, `[modules."<id>"]` + its lines; LF line ends. -/
def canonicalText (m : ManifestFile) : List Char :=
  "schema = 1\n\n[library]\ncommit = ".toList ++ quoted (toString m.library) ++
    "\n\n[policy]\nproof = ".toList ++
    quoted (policyWord m.policy) ++
    "\n".toList ++
    m.modules.flatMap fun e =>
      "\n[modules.".toList ++ quoted (entryId e) ++ "]\n".toList ++ entryLines e

/-- T4: the canonical bytes = the canonical text's UTF-8. -/
def canonicalManifest (m : ManifestFile) : List UInt8 :=
  (String.ofList (canonicalText m)).toUTF8.data.toList

/-! ## T5 `TomlText`: the TOML 1.0 subset T4 emits (names = toml.abnf v1.0.0 rules) -/

/-- Two lists related element by element. -/
inductive Forall2 {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 r [] []
  |
  cons {a : α} {b : β} {as : List α} {bs : List β} :
    r a b → Forall2 r as bs → Forall2 r (a :: as) (b :: bs)

/-- `basic-unescaped` = wschar / %x21 / %x23-5B / %x5D-7E / non-ascii. -/
def BasicUnescaped (c : Char) : Prop :=
  c.toNat = 0x20 ∨
    c.toNat = 0x09 ∨
    c.toNat = 0x21 ∨
    0x23 ≤ c.toNat ∧ c.toNat ≤ 0x5B ∨ 0x5D ≤ c.toNat ∧ c.toNat ≤ 0x7E ∨ 0x80 ≤ c.toNat

/-- ABNF `HEXDIG` (case-insensitive) + its value. -/
def HexDig (c : Char) (v : Nat) : Prop :=
  '0' ≤ c ∧ c ≤ '9' ∧ v = c.toNat - 48 ∨
    'A' ≤ c ∧ c ≤ 'F' ∧ v = c.toNat - 55 ∨ 'a' ≤ c ∧ c ≤ 'f' ∧ v = c.toNat - 87

/-- `escaped` (this subset: no `\U` + 8 hex digits) + the scalar it denotes. -/
inductive Escaped : List Char → Char → Prop
  | quote : Escaped ['\\', '"'] '"'
  | backslash : Escaped ['\\', '\\'] '\\'
  | backspace : Escaped ['\\', 'b'] '\x08'
  | formFeed : Escaped ['\\', 'f'] '\x0c'
  | lineFeed : Escaped ['\\', 'n'] '\n'
  | carriageReturn : Escaped ['\\', 'r'] '\r'
  | tab : Escaped ['\\', 't'] '\t'
  |
  u4 {a b c d x : Char} {va vb vc vd : Nat} :
    HexDig a va →
      HexDig b vb →
      HexDig c vc →
      HexDig d vd →
      x.toNat = 4096 * va + 256 * vb + 16 * vc + vd → Escaped ['\\', 'u', a, b, c, d] x

/-- `basic-char` = basic-unescaped / escaped, + the scalar it denotes. -/
def BasicChar (t : List Char) (x : Char) : Prop := t = [x] ∧ BasicUnescaped x ∨ Escaped t x

/-- `basic-string` = quotation-mark *basic-char quotation-mark, denoting its scalars. -/
def BasicString (t : List Char) (s : String) : Prop :=
  ∃ parts : List (List Char), t = '"' :: parts.flatten ++ ['"'] ∧ Forall2 BasicChar parts s.toList

/-- `unquoted-key` = 1*( ALPHA / DIGIT / %x2D / %x5F ). -/
def UnquotedKey (t : List Char) (k : String) : Prop :=
  t ≠ [] ∧ t = k.toList ∧ ∀ c ∈ t, Letter c ∨ Digit c ∨ c = '-' ∨ c = '_'

/-- `simple-key` = quoted-key (basic strings in this subset) / unquoted-key. -/
def SimpleKey (t : List Char) (k : String) : Prop := UnquotedKey t k ∨ BasicString t k

/-- `dec-int` (this subset: unsigned, no `_`): `DIGIT` / `digit1-9 1*DIGIT`. -/
def DecInt (t : List Char) (n : Int) : Prop :=
  t ≠ [] ∧
    (∀ c ∈ t, Digit c) ∧
    (t.length = 1 ∨ t.head? ≠ some '0') ∧
    n = ((t.foldl (fun a c => 10 * a + (c.toNat - 48)) 0 : Nat) : Int)

/-- `array` of basic strings (this subset: `[`, elements joined by `, `, `]`). -/
def StringArray (t : List Char) (xs : List String) : Prop :=
  ∃ parts : List (List Char),
    t = '[' :: [',', ' '].intercalate parts ++ [']'] ∧ Forall2 BasicString parts xs

/-- `val` (this subset) + the tree it denotes. -/
def Val (t : List Char) (v : Tree) : Prop :=
  (∃ s, v = .str s ∧ BasicString t s) ∨
    (∃ n, v = .int n ∧ DecInt t n) ∨ ∃ xs, v = .arr (xs.map .str) ∧ StringArray t xs

/-- `keyval` + newline (this subset: one space either side of `=`; the key = one simple-key). -/
def KeyvalLine (t : List Char) (m : String × Tree) : Prop :=
  ∃ kt vt, t = kt ++ " = ".toList ++ vt ++ ['\n'] ∧ SimpleKey kt m.1 ∧ Val vt m.2

/-- Consecutive keyval lines. -/
def Keyvals (t : List Char) (ms : List (String × Tree)) : Prop :=
  ∃ lines : List (List Char), t = lines.flatten ∧ Forall2 KeyvalLine lines ms

/-- `std-table` + newline (this subset: a key of one or two simple-keys). -/
def Header (t : List Char) (path : List String) : Prop :=
  (∃ kt a, path = [a] ∧ t = '[' :: kt ++ [']', '\n'] ∧ SimpleKey kt a) ∨
    ∃ kt₁ kt₂ a b,
      path = [a, b] ∧
        t = '[' :: kt₁ ++ '.' :: kt₂ ++ [']', '\n'] ∧ SimpleKey kt₁ a ∧ SimpleKey kt₂ b

/-- A table section: a blank line, its header, its keyvals. -/
def SectionText (t : List Char) (sec : List String × List (String × Tree)) : Prop :=
  ∃ ht kt, t = '\n' :: ht ++ kt ∧ Header ht sec.1 ∧ Keyvals kt sec.2

/-- TOML 1.0 tables: `[a]` defines root member `a`; `[a.b]` defines member `b` of the table at `a`,
which its first use creates (implicitly) as a root member; members in definition order. -/
def denote (root : List (String × Tree)) :
    List (List String × List (String × Tree)) → List (String × Tree)
  | [] => root
  | (path, ms) :: secs =>
    match path with
    | [a] => denote (root ++ [(a, .tbl ms)]) secs
    | [a, b] =>
      match root.lookup a with
      | some (.tbl xs) =>
        denote (root.map fun m => if m.1 = a then (a, .tbl (xs ++ [(b, .tbl ms)])) else m) secs
      | _ => denote (root ++ [(a, .tbl [(b, .tbl ms)])]) secs
    | _ => denote root secs

/-- TOML 1.0's no-redefinition rules for this subset: keys distinct within every keyval group;
header paths distinct; a one-key header names neither a root key nor a two-key header's first key;
a two-key header's first key is no root key. -/
def DocWF (root : List (String × Tree)) (secs : List (List String × List (String × Tree))) : Prop :=
  (root.map (·.1)).Nodup ∧
    (∀ sec ∈ secs, (sec.2.map (·.1)).Nodup ∧ (sec.1.length = 1 ∨ sec.1.length = 2)) ∧
    (secs.map (·.1)).Nodup ∧
    (∀ sec ∈ secs, ∀ a, sec.1 = [a] → a ∉ root.map (·.1) ∧ ∀ sec' ∈ secs, ∀ b, sec'.1 ≠ [a, b]) ∧
    ∀ sec ∈ secs, ∀ a b, sec.1 = [a, b] → a ∉ root.map (·.1)

/-- T5 `TomlText`: the bytes are the UTF-8 of a document of this subset — root keyvals, then table
sections — obeying `DocWF`, which denotes `t`. -/
def TomlText (bytes : List UInt8) (t : Tree) : Prop :=
  ∃ (rootText : List Char) (root : List (String × Tree)) (secTexts : List (List Char)) (secs :
    List (List String × List (String × Tree))),
    bytes = (String.ofList (rootText ++ secTexts.flatten)).toUTF8.data.toList ∧
      Keyvals rootText root ∧
      Forall2 SectionText secTexts secs ∧ DocWF root secs ∧ t = .tbl (denote root secs)

end

end FvdepAudit.Manifest.Spec
