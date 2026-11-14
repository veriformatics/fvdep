import FvdepCore.Doc

/-! `fvdep.toml` (contract `docs/contracts/U3-codecs.md` T1–T4): the text stage, the TOML tree,
T3's validation into the typed manifest, the canonical printer. Pure: Lake's parser runs in
`FvdepIO.Toml`. A table is judged in key byte order (`String` order = UTF-8 byte order), never in
Lake's member order. -/

namespace FvdepCore.Manifest

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc

/-- T1: a TOML value kind no manifest field takes. -/
inductive Other where
  | float
  | dateTime
  deriving DecidableEq, Repr, Inhabited

/-- T1: a TOML value, keys as strings (`FvdepIO.Toml.ofLake` builds it from Lake's table; a table's
members in Lake's order, which T3 never relies on). -/
inductive Tree where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  | arr (xs : List Tree)
  | tbl (ms : List (String × Tree))
  | other (k : Other)
  deriving Repr, Inhabited, BEq

/-- T2: one `[modules."<id>"]` entry: its U2 declaration + its module lists (both empty for a
differential entry). -/
structure Entry where
  decl : Decl
  implModules : List String
  proofModules : List String
  deriving DecidableEq, Repr

/-- T2: `fvdep.toml`, typed (entries in ascending id byte order, ids unique). -/
structure ManifestFile where
  library : Commit
  policy : Policy
  modules : List Entry
  deriving DecidableEq

/-- T2: U2's manifest = the library + the declarations. -/
def ManifestFile.manifest (m : ManifestFile) : Manifest := ⟨m.library, m.modules.map (·.decl)⟩

/-- T3: the field type a `wrong_type` refusal names. -/
inductive FieldType where
  | string
  | integer
  | array
  | table
  deriving DecidableEq, Repr

/-- T3: why a tree is not a manifest (public code `schema`). -/
inductive ErrorKind where
  | missingField
  | unknownField
  | forbiddenField
  | wrongType (expected : FieldType)
  | badValue
  | duplicateKey (key : String)
  | inBothLists (module : String)
  deriving DecidableEq, Repr

/-- T3: the first violation in D5's order: the judged member's path (keys + array indices) + kind.
-/
structure ManifestError where
  path : List PathSeg
  kind : ErrorKind
  deriving DecidableEq, Repr

/-- T1: why the text stage refuses (public code `schema`). -/
inductive TextError where
  | tooLarge
  | bom
  | utf8 (offset : Nat)
  deriving DecidableEq, Repr

/-! ## T1 text stage -/

/-- T1: the size cap in bytes (Lake's parser recurses per nesting level: the cap bounds the depth;
contract T1). -/
def maxBytes : Nat := 65536

/-- The offset where a left-to-right scan of well-formed UTF-8 sequences from `i` fails. -/
def scanUtf8 (b : ByteArray) (i : Nat) : Option Nat :=
  if _h : i < b.size then
    match b.utf8DecodeChar? i with
    | some c => scanUtf8 b (i + c.utf8Size)
    | none => some i
  else none
termination_by b.size - i
decreasing_by have := c.utf8Size_pos; omega

/-- T1 + T5: `none` when `b` is valid UTF-8, else the length of its longest valid UTF-8 prefix. -/
def utf8ErrorOffset (b : ByteArray) : Option Nat := scanUtf8 b 0

/-- T1: `b` begins with the UTF-8 byte order mark EF BB BF. -/
def hasBom (b : ByteArray) : Bool := (b.data.extract 0 3).toList == [0xEF, 0xBB, 0xBF]

/-- T1: more than `maxBytes` bytes → `tooLarge`; else a leading EF BB BF → `bom`; else invalid UTF-8
→ `utf8 (utf8ErrorOffset b)`; else the text. -/
def textStage (b : ByteArray) : Except TextError String :=
  if maxBytes < b.size then .error .tooLarge
  else
    if hasBom b then .error .bom
    else
      match String.fromUTF8? b with
      | some s => .ok s
      | none => .error (.utf8 ((utf8ErrorOffset b).getD 0))

/-! ## T3 field syntax -/

/-- `[A-Za-z_]`. -/
def headChar (c : Char) : Bool := c.isAlpha || c == '_'

/-- `[A-Za-z0-9_']`. -/
def tailChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- T3: one name component `[A-Za-z_][A-Za-z0-9_']*`. -/
def isComponent : List Char → Bool
  | c :: cs => headChar c && cs.all tailChar
  | [] => false

/-- T3: a module name: dot-separated components, ≤ 256 bytes, its first component not reserved
(`docs/library.md` Naming = U2 I5's `reserved`). -/
def isModuleName (s : String) : Bool :=
  s.utf8ByteSize ≤ 256 &&
    match cut '.' s.toList with
    | first :: rest =>
      isComponent first && rest.all isComponent && !reserved (.str .anonymous (String.ofList first))
    | [] => false

/-- T3: a constant name: dot-separated components, ≤ 1,024 bytes. -/
def isConstName (s : String) : Bool := s.utf8ByteSize ≤ 1024 && (cut '.' s.toList).all isComponent

/-- D2: a module id's canonical spelling within 65,536 bytes. -/
def isModuleId (s : String) : Bool := (ModuleId.parse s).isSome && s.utf8ByteSize ≤ 65536

/-- D2: an entry version's canonical spelling within 65,536 bytes. -/
def isVersion (s : String) : Bool := (EntryVersion.parse s).isSome && s.utf8ByteSize ≤ 65536

def isCommit (s : String) : Bool := (Commit.parse s).isSome

def isShape (s : String) : Bool := s == "fn" || s == "abi"

def isPolicy (s : String) : Bool := s == "required" || s == "development"

/-! ## T3 validation (D5 order) -/

/-- T3, every table before its other rules: its least repeated key. -/
def repeatedKey (ms : List (String × Tree)) : Option String :=
  firstRepeat ((ms.map (·.1)).mergeSort (· ≤ ·))

/-- Members in key byte order (stable). -/
def byKey (ms : List (String × Tree)) : List (String × Tree) :=
  ms.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- D5 (b) + (c): the first member (in `ms`'s order) whose key meets `bad`, as `kind` at that
key. -/
def firstKey (bad : String → Bool) (kind : ErrorKind) (p : List PathSeg)
    (ms : List (String × Tree)) : Option ManifestError :=
  (ms.find? fun m => bad m.1).map fun m => ⟨p ++ [.key m.1], kind⟩

/-- D5 (d): the first required key (listed in byte order) the members lack. -/
def missingKey (ms : List (String × Tree)) (p : List PathSeg) (req : List String) :
    Option ManifestError :=
  (req.find? fun k => !ms.any (·.1 == k)).map fun k => ⟨p ++ [.key k], .missingField⟩

/-- D5 (e): member values in `ms`'s order. -/
def valuesCheck (f : String → Tree → Option ManifestError) :
    List (String × Tree) → Option ManifestError
  | [] => none
  | (k, v) :: ms => (f k v).orElse fun _ => valuesCheck f ms

/-- A string field: its kind, then its rule. -/
def strField (ok : String → Bool) (p : List PathSeg) : Tree → Option ManifestError
  | .str s => if ok s then none else some ⟨p, .badValue⟩
  | _ => some ⟨p, .wrongType .string⟩

/-- Array elements (index `i` onward): each a string meeting `ok` at its index. -/
def elemsCheck (ok : Nat → String → Bool) (p : List PathSeg) :
    Nat → List Tree → Option ManifestError
  | _, [] => none
  | i, .str s :: xs =>
    if ok i s then elemsCheck ok p (i + 1) xs else some ⟨p ++ [.index i], .badValue⟩
  | i, _ :: _ => some ⟨p ++ [.index i], .wrongType .string⟩

/-- The string elements of an array. -/
def strings (xs : List Tree) :
    List String := xs.filterMap fun
    | .str s => some s
    | _ => none

/-- The index of the first element equal to an earlier one (`seen` = the earlier ones). -/
def firstRepeatIndex (seen : List String) (i : Nat) : List String → Option Nat
  | [] => none
  | x :: xs => if seen.contains x then some i else firstRepeatIndex (x :: seen) (i + 1) xs

/-- T3 array order: kind → nonempty → elements by index → repeats (`unique` lists alone). -/
def arrayCheck (ok : Nat → String → Bool) (unique : Bool) (p : List PathSeg) :
    Tree → Option ManifestError
  | .arr xs =>
    if xs.isEmpty then some ⟨p, .badValue⟩
    else
      (elemsCheck ok p 0 xs).orElse fun _ =>
        if unique then
          (firstRepeatIndex [] 0 (strings xs)).map fun i => ⟨p ++ [.index i], .badValue⟩
        else none
  | _ => some ⟨p, .wrongType .array⟩

/-- A one-key table (`[library]`, `[policy]`): repeats, keys ⊆ {`key`}, `key` present when
`required`, then `key`'s value by `ok`. -/
def tableCheck (key : String) (required : Bool) (ok : String → Bool) (p : List PathSeg) :
    Tree → Option ManifestError
  | .tbl ms =>
    match repeatedKey ms with
    | some k => some ⟨p, .duplicateKey k⟩
    | none =>
      let ss := byKey ms
      (firstKey (· != key) .unknownField p ss).orElse fun _ =>
        (missingKey ss p (if required then [key] else [])).orElse fun _ =>
          valuesCheck (fun k v => if k == key then strField ok (p ++ [.key k]) v else none) ss
  | _ => some ⟨p, .wrongType .table⟩

/-- T3: every key an entry may hold, in byte order. -/
def entryKeys : List String :=
  ["adapter", "evidence", "impl", "impl_modules", "proof", "proof_modules", "shape", "version"]

/-- T3: an entry kind's required keys, in byte order. -/
def requiredKeys : Kind → List String
  | .proof => ["impl", "impl_modules", "proof", "proof_modules", "shape", "version"]
  | .differential => ["adapter", "evidence", "version"]

/-- T3: the keys only the other entry kind defines. -/
def forbiddenKeys : Kind → List String
  | .proof => ["adapter"]
  | .differential => ["impl", "impl_modules", "proof", "proof_modules", "shape"]

/-- T3 (a): the entry's discriminator `evidence` (absent = proof). -/
def entryKind (p : List PathSeg) (ms : List (String × Tree)) : Except ManifestError Kind :=
  match ms.lookup "evidence" with
  | none => .ok .proof
  | some (.str s) =>
    if s == "differential" then .ok .differential else .error ⟨p ++ [.key "evidence"], .badValue⟩
  | some _ => .error ⟨p ++ [.key "evidence"], .wrongType .string⟩

/-- T3 (e): one entry member's value (`evidence` judged in (a)). -/
def entryValue (p : List PathSeg) (k : String) (v : Tree) : Option ManifestError :=
  match k with
  | "adapter" => arrayCheck (fun i s => isArg (i == 0) s) false (p ++ [.key k]) v
  | "impl" => strField isConstName (p ++ [.key k]) v
  | "impl_modules" => arrayCheck (fun _ => isModuleName) true (p ++ [.key k]) v
  | "proof" => strField isConstName (p ++ [.key k]) v
  | "proof_modules" => arrayCheck (fun _ => isModuleName) true (p ++ [.key k]) v
  | "shape" => strField isShape (p ++ [.key k]) v
  | "version" => strField isVersion (p ++ [.key k]) v
  | _ => none

/-- A list field's strings ([] otherwise). -/
def listOf : Option Tree → List String
  | some (.arr xs) => strings xs
  | _ => []

/-- T3 (f): the first `impl_modules` element that `proof_modules` also lists. -/
def overlap (p : List PathSeg) (ms : List (String × Tree)) : Option ManifestError :=
  let proofs := listOf (ms.lookup "proof_modules")
  ((listOf (ms.lookup "impl_modules")).find? proofs.contains).map fun m => ⟨p, .inBothLists m⟩

/-- T3: one `[modules."<id>"]` entry. -/
def entryCheck (p : List PathSeg) : Tree → Option ManifestError
  | .tbl ms =>
    match repeatedKey ms with
    | some k => some ⟨p, .duplicateKey k⟩
    | none =>
      match entryKind p ms with
      | .error e => some e
      | .ok kind =>
        let ss := byKey ms
        (firstKey (!entryKeys.contains ·) .unknownField p ss).orElse fun _ =>
          (firstKey (forbiddenKeys kind).contains .forbiddenField p ss).orElse fun _ =>
            (missingKey ss p (requiredKeys kind)).orElse fun _ =>
              (valuesCheck (entryValue p) ss).orElse fun _ => overlap p ms
  | _ => some ⟨p, .wrongType .table⟩

/-- T3: `[modules]` = a map from module ids to entries, judged in key byte order. -/
def modulesCheck (p : List PathSeg) : Tree → Option ManifestError
  | .tbl ms =>
    match repeatedKey ms with
    | some k => some ⟨p, .duplicateKey k⟩
    | none =>
      valuesCheck
        (fun k v =>
          if isModuleId k then entryCheck (p ++ [.key k]) v else some ⟨p ++ [.key k], .badValue⟩)
        (byKey ms)
  | _ => some ⟨p, .wrongType .table⟩

/-- T3 (e): one root member's value (`schema` judged in (a)). -/
def rootValue (k : String) (v : Tree) : Option ManifestError :=
  match k with
  | "library" => tableCheck "commit" true isCommit [.key k] v
  | "modules" => modulesCheck [.key k] v
  | "policy" => tableCheck "proof" false isPolicy [.key k] v
  | _ => none

/-- T3: every key the root may hold, in byte order. -/
def rootKeys : List String := ["library", "modules", "policy", "schema"]

/-- T3 + D5: the first violation of `t` (`none` = a manifest). -/
def check : Tree → Option ManifestError
  | .tbl ms =>
    match repeatedKey ms with
    | some k => some ⟨[], .duplicateKey k⟩
    | none =>
      match ms.lookup "schema" with
      | none => some ⟨[.key "schema"], .missingField⟩
      | some (.int n) =>
        if n == 1 then
          let ss := byKey ms
          (firstKey (!rootKeys.contains ·) .unknownField [] ss).orElse fun _ =>
            (missingKey ss [] ["library"]).orElse fun _ => valuesCheck rootValue ss
        else some ⟨[.key "schema"], .badValue⟩
      | some _ => some ⟨[.key "schema"], .wrongType .integer⟩
  | _ => some ⟨[], .wrongType .table⟩

/-! ## T2 extraction (total: a tree `check` accepts never reaches a fallback) -/

/-- A member's string payload, `none` otherwise. -/
def strOpt : Option Tree → Option String
  | some (.str s) => some s
  | _ => none

/-- A member's table members ([] otherwise). -/
def tableOf : Option Tree → List (String × Tree)
  | some (.tbl ms) => ms
  | _ => []

/-- T2: the entry an accepted `[modules."<k>"]` table denotes. -/
def entryOf (k : String) (v : Tree) : Entry :=
  let ms := tableOf (some v)
  let kind : Kind :=
    if strOpt (ms.lookup "evidence") = some "differential" then .differential else .proof
  { decl :=
      { module := (ModuleId.parse k).getD defaultModule
        version := (EntryVersion.parse ((strOpt (ms.lookup "version")).getD "")).getD ⟨0, 0, 0⟩
        shape :=
          match strOpt (ms.lookup "shape") with
          | some "fn" => some .fn
          | some "abi" => some .abi
          | _ => none
        kind
        impl := strOpt (ms.lookup "impl")
        proof := strOpt (ms.lookup "proof")
        adapter :=
          match ms.lookup "adapter" with
          | some (.arr xs) => some (strings xs)
          | _ => none }
    implModules := listOf (ms.lookup "impl_modules")
    proofModules := listOf (ms.lookup "proof_modules") }

/-- T2: the manifest an accepted tree denotes. -/
def extract (t : Tree) : ManifestFile :=
  let ms := tableOf (some t)
  { library :=
      (Commit.parse ((strOpt ((tableOf (ms.lookup "library")).lookup "commit")).getD "")).getD
        defaultCommit
    policy :=
      if strOpt ((tableOf (ms.lookup "policy")).lookup "proof") = some "development" then
        .development
      else .required
    modules := (byKey (tableOf (ms.lookup "modules"))).map fun e => entryOf e.1 e.2 }

/-- T3: the typed manifest, or the first violation (D5's order). -/
def validate (t : Tree) : Except ManifestError ManifestFile :=
  match check t with
  | some e => .error e
  | none => .ok (extract t)

/-! ## T4 canonical printer -/

/-- T4: an entry's members in printed order (version, evidence, shape, impl_modules,
proof_modules, impl, proof, adapter; present ones). -/
def entryMembers (e : Entry) : List (String × Tree) :=
  let d := e.decl
  let strs (xs : List String) : Tree := .arr (xs.map .str)
  [("version", .str (toString d.version))] ++
    (match d.kind with
    | .differential => [("evidence", .str "differential")]
    | .proof => []) ++
    (match d.shape with
    | some s => [("shape", .str (shapeText s))]
    | none => []) ++
    (match d.kind with
    | .proof => [("impl_modules", strs e.implModules), ("proof_modules", strs e.proofModules)]
    | .differential => []) ++
    (match d.impl with
    | some s => [("impl", .str s)]
    | none => []) ++
    (match d.proof with
    | some s => [("proof", .str s)]
    | none => []) ++
    match d.adapter with
    | some xs => [("adapter", strs xs)]
    | none => []

/-- T5: the tree `printManifest m` denotes (T4's tables + keys in printed order; `modules` present
iff `m.modules` is nonempty). -/
def toTree (m : ManifestFile) : Tree :=
  .tbl <|
    [("schema", .int 1), ("library", .tbl [("commit", .str (toString m.library))]),
        ("policy", .tbl [("proof", .str (policyText m.policy))])] ++
      if m.modules.isEmpty then []
      else
        [("modules", .tbl (m.modules.map fun e => (toString e.decl.module, .tbl (entryMembers e))))]

/-- T4: `c` inside a basic string. -/
def escapeChar (c : Char) : List Char :=
  match c.toNat with
  | 0x22 => ['\\', '"']
  | 0x5C => ['\\', '\\']
  | 0x08 => ['\\', 'b']
  | 0x09 => ['\\', 't']
  | 0x0A => ['\\', 'n']
  | 0x0C => ['\\', 'f']
  | 0x0D => ['\\', 'r']
  | n =>
    if n < 0x20 || n == 0x7F then ['\\', 'u', '0', '0', hexUpper (n / 16), hexUpper (n % 16)]
    else [c]

/-- T4: a TOML basic string. -/
def basic (s : String) : String := "\"" ++ String.ofList (s.toList.flatMap escapeChar) ++ "\""

/-- T4: a printed value (strings, the schema integer, arrays of strings). -/
def tomlValue : Tree → String
  | .str s => basic s
  | .int n => toString n
  | .arr xs =>
    "[" ++
      ", ".intercalate
        (xs.map fun
          | .str s => basic s
          | _ => "") ++
      "]"
  | _ => ""

/-- T4: `key = value` lines. -/
def membersText (ms : List (String × Tree)) : String :=
  String.join (ms.map fun m => m.1 ++ " = " ++ tomlValue m.2 ++ "\n")

/-- T4: the canonical text. -/
def printText (m : ManifestFile) : String :=
  "schema = 1\n\n[library]\ncommit = " ++ basic (toString m.library) ++ "\n\n[policy]\nproof = " ++
    basic (policyText m.policy) ++
    "\n" ++
    String.join
      (m.modules.map fun e =>
        "\n[modules." ++ basic (toString e.decl.module) ++ "]\n" ++ membersText (entryMembers e))

/-- T4: the canonical `fvdep.toml` bytes (written by `init` + `upgrade` alone). -/
def printManifest (m : ManifestFile) : ByteArray := (printText m).toUTF8

/-! ## Presentation (tested, outside the claims) -/

/-- A bare key character `[A-Za-z0-9_-]`. -/
def bareChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-'

/-- One key segment: bare when it is `[A-Za-z0-9_-]+`, else a basic string. -/
def keyText (s : String) : String := if !s.isEmpty && s.all bareChar then s else basic s

/-- T3: a path as TOML dotted keys + `[i]` indices: `modules."base64.encode".impl_modules[1]`. -/
def keyPath (p : List PathSeg) : String :=
  String.join <|
    (p.zipIdx.map fun (seg, i) =>
      match seg with
      | .key s => (if i == 0 then "" else ".") ++ keyText s
      | .index n => "[" ++ toString n ++ "]")

def FieldType.spelling : FieldType → String
  | .string => "string"
  | .integer => "integer"
  | .array => "array"
  | .table => "table"

/-- The refusal text: the path (the root's empty path omitted) + the kind + the key or module it
names. -/
def ManifestError.detail (e : ManifestError) : String :=
  let what :=
    match e.kind with
    | .missingField => "missing_field"
    | .unknownField => "unknown_field"
    | .forbiddenField => "forbidden_field"
    | .wrongType t => "wrong_type (expected " ++ t.spelling ++ ")"
    | .badValue => "bad_value"
    | .duplicateKey k => "duplicate_key " ++ keyText k
    | .inBothLists m => "in_both_lists " ++ basic m
  if e.path.isEmpty then what else keyPath e.path ++ " " ++ what

/-- The refusal text for a text-stage failure. -/
def TextError.detail : TextError → String
  | .tooLarge => "too_large (more than " ++ toString maxBytes ++ " bytes)"
  | .bom => "bom at offset 0"
  | .utf8 k => "utf8 at offset " ++ toString k

end FvdepCore.Manifest
