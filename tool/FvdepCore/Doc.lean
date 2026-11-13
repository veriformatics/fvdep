import FvdepCore.Json
import FvdepCore.Status

/-! Documents fvdep reads + writes, schema 1 (contract `docs/contracts/U3-codecs.md` D1–D8): the
text bound, the refusal walk over a schema (D5), receipts + `fvdep.lock` (D3, D4), the `--json`
envelope (D6). Receipt + lock functions extend `FvdepCore.Status` (dot notation). -/

namespace FvdepCore.Doc

open Json Ids Evidence Status

/-! ## D1 text bound -/

/-- The longest prefix of `cs` whose UTF-8 bytes fit `budget`. -/
def fitPrefix (budget : Nat) : List Char → List Char
  | [] => []
  | c :: cs => if c.utf8Size ≤ budget then c :: fitPrefix (budget - c.utf8Size) cs else []

/-- D1: `s` within 65,536 UTF-8 bytes, else its longest scalar-boundary prefix of ≤ 65,520 bytes +
` [truncated]`. The fitting prefix holds ≤ 65,520 scalars, so only that many are copied out. -/
def clip (s : String) : String :=
  if s.utf8ByteSize ≤ 65536 then s
  else String.ofList (fitPrefix 65520 (s.take 65520).copy.toList) ++ " [truncated]"

/-! ## D5 refusals -/

/-- D5: the kind of a document refusal. -/
inductive DocKind where
  | missingField
  | unknownField
  | wrongType
  | badValue
  deriving DecidableEq, Repr

/-- D5: the first violation in walk order: the judged member's path, kind + value (`none` for a
missing member). -/
structure DocError where
  path : List PathSeg
  kind : DocKind
  value : Option Value
  deriving Repr, BEq

/-- D5: why `fvdep.lock`'s bytes are refused: the text (step 0 = J3) or the document. -/
inductive LockError where
  | text (e : DecodeError)
  | doc (e : DocError)
  deriving Repr, BEq

/-- An RFC 6901 reference token: `~` → `~0`, `/` → `~1`. -/
def escapeToken (s : String) : String :=
  String.ofList
    (s.toList.flatMap fun c => if c = '~' then ['~', '0'] else if c = '/' then ['~', '1'] else [c])

/-- D5: the RFC 6901 JSON Pointer of a path; the root = "". -/
def pointer (path : List PathSeg) : String :=
  String.join <|
    path.map fun
      | .key s => "/" ++ escapeToken s
      | .index n => "/" ++ toString n

def DocKind.spelling : DocKind → String
  | .missingField => "missing_field"
  | .unknownField => "unknown_field"
  | .wrongType => "wrong_type"
  | .badValue => "bad_value"

/-- A value's JSON kind, as rendered when its text is long. -/
def kindWord : Value → String
  | .null => "null"
  | .bool _ => "bool"
  | .int _ => "int"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

/-- A judged value: its canonical text when ≤ 64 bytes, else its JSON kind. -/
def valueText (v : Value) : String :=
  let b := print v
  if b.size ≤ 64 then (String.fromUTF8? b).getD (kindWord v) else kindWord v

/-- D5: `<pointer> <kind> <value>`; the root's empty pointer is omitted with its separator; no
value for a missing member. -/
def DocError.render (e : DocError) : String :=
  let words :=
    [pointer e.path, e.kind.spelling] ++
      match e.kind, e.value with
      | .missingField, _ => []
      | _, some v => [valueText v]
      | _, none => []
  " ".intercalate (words.filter (!·.isEmpty))

/-- D5: the text failure's spelling (a duplicate key as one pointer: site path + key), else the
document error's rendering. -/
def LockError.render : LockError → String
  | .text .malformed => "malformed"
  | .text .tooLarge => "too_large"
  | .text (.duplicateKey (p, k)) => "duplicate_key " ++ pointer (p ++ [.key k])
  | .doc e => e.render

/-! ## D2 field syntax -/

def isLowerHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- 64 lowercase hex digits (a SHA-256 digest). -/
def isDigest (s : String) : Bool := s.length == 64 && s.toList.all isLowerHex

/-- Two decimal digits as a number. -/
def twoDigits (a b : Char) : Nat := 10 * (a.toNat - 48) + (b.toNat - 48)

/-- `YYYY-MM-DDTHH:MM:SSZ`: month 01–12, day 01–31, hour 00–23, minute 00–59, second 00–60. -/
def isUtc (s : String) : Bool :=
  match s.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, 'T', h1, h2, ':', n1, n2, ':', s1, s2, 'Z'] =>
    [y1, y2, y3, y4, m1, m2, d1, d2, h1, h2, n1, n2, s1, s2].all Char.isDigit &&
      1 ≤ twoDigits m1 m2 &&
      twoDigits m1 m2 ≤ 12 &&
      1 ≤ twoDigits d1 d2 &&
      twoDigits d1 d2 ≤ 31 &&
      twoDigits h1 h2 ≤ 23 &&
      twoDigits n1 n2 ≤ 59 &&
      twoDigits s1 s2 ≤ 60
  | _ => false

/-- 1–1,024 UTF-8 bytes, no control character (U+0000–U+001F, U+007F). -/
def isConstant (s : String) : Bool :=
  1 ≤ s.utf8ByteSize && s.utf8ByteSize ≤ 1024 &&
    s.toList.all fun c => !(c.toNat < 32 || c.toNat == 127)

/-- 1–256 bytes of `[A-Za-z0-9._@+-]`. -/
def isProfileId (s : String) : Bool :=
  1 ≤ s.utf8ByteSize && s.utf8ByteSize ≤ 256 &&
    s.toList.all fun c => c.isAlphanum || ['.', '_', '@', '+', '-'].contains c

/-- An adapter argument: ≤ 65,536 UTF-8 bytes (`argv[0]`: ≥ 1), no U+0000. -/
def isArg (first : Bool) (s : String) : Bool :=
  (!first || 1 ≤ s.utf8ByteSize) && s.utf8ByteSize ≤ 65536 && !s.toList.contains '\x00'

/-! ## D5 schema syntax + walk -/

/-- A JSON value's kind (D5: a field's general type = a list of kinds). -/
inductive JKind where
  | null
  | bool
  | int
  | str
  | arr
  | obj
  deriving DecidableEq, Repr

def kindOf : Value → JKind
  | .null => .null
  | .bool _ => .bool
  | .int _ => .int
  | .str _ => .str
  | .arr _ => .arr
  | .obj _ => .obj

/-- A scalar's rule, judged once its kind lies inside the general type (D2 syntax, enumerations,
the evidence kind's nullness). -/
inductive Rule where
  | null
  | commit
  | digest
  | utc
  | moduleId
  | version
  | constant
  | profile
  | oneOf (xs : List String)
  | arg (first : Bool)
  deriving DecidableEq, Repr

def Rule.check : Rule → Value → Bool
  | .null, .null => true
  | .commit, .str s => (Commit.parse s).isSome
  | .digest, .str s => isDigest s
  | .utc, .str s => isUtc s
  | .moduleId, .str s => (ModuleId.parse s).isSome && s.utf8ByteSize ≤ 65536
  | .version, .str s => (EntryVersion.parse s).isSome && s.utf8ByteSize ≤ 65536
  | .constant, .str s => isConstant s
  | .profile, .str s => isProfileId s
  | .oneOf xs, .str s => xs.contains s
  | .arg first, .str s => isArg first s
  | _, _ => false

/-- An object's discriminator (D5 (a)): its key + the values it accepts; a string discriminator
also selects the variant its nested `byTag` types follow. -/
inductive Disc where
  | int (key : String) (n : Int)
  | str (key : String) (accepted : List String)
  deriving DecidableEq, Repr

/-- An array's constraint, judged after its elements (D5 (e)). -/
inductive Order where
  | nonempty
  /-- Strictly ascending strings at this key path inside each element. -/
  | ascending (path : List String)
  deriving DecidableEq, Repr

/-- A member's type. Object fields are listed in ascending key order (D5 judges keys in byte
order). -/
inductive Ty where
  | scalar (kinds : List JKind) (rule : Rule)
  | obj (disc : Option Disc) (fields : List (String × Ty))
  /-- Element 0 has type `head`, every later element `tail`. -/
  | arr (kinds : List JKind) (head tail : Ty) (order : Order)
  /-- The type under the nearest enclosing string discriminator's value. -/
  | byTag (cases : List (String × Ty))

/-- `t` under the discriminator value `tag`. -/
def resolve (tag : String) : Ty → Ty
  | .byTag cs => ((cs.find? (·.1 == tag)).map (·.2)).getD (.byTag [])
  | t => t

/-- The first member's value for `k`. -/
def member? (ms : List (String × Value)) (k : String) : Option Value :=
  (ms.find? (·.1 == k)).map (·.2)

/-- D5 (a): the discriminator's verdict: the tag nested types follow + the extra known key, or the
refusal (nothing else in the object is judged). -/
def discCheck (tag : String) (p : List PathSeg) (ms : List (String × Value)) :
    Option Disc → Except DocError (String × List String)
  | none => .ok (tag, [])
  | some (.int k n) =>
    match member? ms k with
    | none => .error ⟨p ++ [.key k], .missingField, none⟩
    | some (.int m) =>
      if m = n then .ok (tag, [k]) else .error ⟨p ++ [.key k], .badValue, some (.int m)⟩
    | some x => .error ⟨p ++ [.key k], .wrongType, some x⟩
  | some (.str k xs) =>
    match member? ms k with
    | none => .error ⟨p ++ [.key k], .missingField, none⟩
    | some (.str s) =>
      if xs.contains s then .ok (s, [k]) else .error ⟨p ++ [.key k], .badValue, some (.str s)⟩
    | some x => .error ⟨p ++ [.key k], .wrongType, some x⟩

/-- D5 (b): the first member whose key the object does not define. -/
def firstUnknown (known : List String) (p : List PathSeg) : List (String × Value) → Option DocError
  | [] => none
  | (k, x) :: ms =>
    if known.contains k then firstUnknown known p ms
    else some ⟨p ++ [.key k], .unknownField, some x⟩

/-- D5 (d): the first field the object lacks. -/
def firstMissing (ms : List (String × Value)) (p : List PathSeg) : List String → Option DocError
  | [] => none
  | k :: ks =>
    if ms.any (·.1 == k) then firstMissing ms p ks else some ⟨p ++ [.key k], .missingField, none⟩

/-- The value at a key path inside an object value. -/
def valueAt : List String → Value → Option Value
  | [], v => some v
  | k :: ks, .obj ms => (member? ms k).bind (valueAt ks)
  | _ :: _, _ => none

/-- D5 (e): an array's constraint, after its elements. -/
def Order.check (p : List PathSeg) (xs : List Value) : Order → Option DocError
  | .nonempty => if xs.isEmpty then some ⟨p, .badValue, some (.arr [])⟩ else none
  | .ascending path => ascendingFrom p path 1 xs
where
  /-- The first element (index `i` onward) whose string at `path` is ≤ its predecessor's. -/
  ascendingFrom (p : List PathSeg) (path : List String) (i : Nat) : List Value → Option DocError
    | a :: b :: rest =>
      match valueAt path a, valueAt path b with
      | some (.str x), some (.str y) =>
        if x < y then ascendingFrom p path (i + 1) (b :: rest)
        else some ⟨p ++ [.index i] ++ path.map .key, .badValue, some (.str y)⟩
      | _, _ => ascendingFrom p path (i + 1) (b :: rest)
    | _ => none

/-- A scalar type: kind inside the general type, then the rule. -/
def leaf (ks : List JKind) (r : Rule) (p : List PathSeg) (v : Value) : Option DocError :=
  if ks.contains (kindOf v) then if r.check v then none else some ⟨p, .badValue, some v⟩
  else some ⟨p, .wrongType, some v⟩

/-- An array type met by a non-array: inside the general type (e.g. `null`) = a rule failure. -/
def kindMiss (ks : List JKind) (p : List PathSeg) (v : Value) : Option DocError :=
  if ks.contains (kindOf v) then some ⟨p, .badValue, some v⟩ else some ⟨p, .wrongType, some v⟩

mutual
/-- D5: the first violation of `v` against `t` (path `p`, discriminator value `tag` in scope), in
walk order: kind, discriminator, unknown members, missing members, member values in member order
(= key order on a decoded value), array elements, the array's constraint. -/
def walk (tag : String) (t : Ty) (p : List PathSeg) : Value → Option DocError
  | .obj ms =>
    match resolve tag t with
    | .obj d fs =>
      match discCheck tag p ms d with
      | .error e => some e
      | .ok (tag', extra) =>
        (firstUnknown (extra ++ fs.map (·.1)) p ms).orElse fun _ =>
          (firstMissing ms p (fs.map (·.1))).orElse fun _ => walkMembers tag' fs p ms
    | .scalar ks r => leaf ks r p (.obj ms)
    | .arr ks .. => kindMiss ks p (.obj ms)
    | .byTag _ => some ⟨p, .wrongType, some (.obj ms)⟩
  | .arr xs =>
    match resolve tag t with
    | .arr _ h tl o => (walkElems tag h tl p 0 xs).orElse fun _ => o.check p xs
    | .scalar ks r => leaf ks r p (.arr xs)
    | .obj .. => some ⟨p, .wrongType, some (.arr xs)⟩
    | .byTag _ => some ⟨p, .wrongType, some (.arr xs)⟩
  | v =>
    match resolve tag t with
    | .scalar ks r => leaf ks r p v
    | .arr ks .. => kindMiss ks p v
    | .obj .. => some ⟨p, .wrongType, some v⟩
    | .byTag _ => some ⟨p, .wrongType, some v⟩
/-- D5 (e): member values in member order; a member without a field (an unknown key, already
refused by (b)) is skipped. -/
def walkMembers (tag : String) (fs : List (String × Ty)) (p : List PathSeg) :
    List (String × Value) → Option DocError
  | [] => none
  | (k, x) :: ms =>
    match (fs.find? (·.1 == k)).map (·.2) with
    | some t => (walk tag t (p ++ [.key k]) x).orElse fun _ => walkMembers tag fs p ms
    | none => walkMembers tag fs p ms
/-- D5 (e): array elements in index order. -/
def walkElems (tag : String) (h tl : Ty) (p : List PathSeg) (i : Nat) : List Value → Option DocError
  | [] => none
  | x :: xs =>
    (walk tag (if i = 0 then h else tl) (p ++ [.index i]) x).orElse fun _ =>
      walkElems tag h tl p (i + 1) xs
end

/-! ## D3 + D4 schemas -/

/-- Set (meeting `rule`) under proof evidence, null under differential (D3 nullness). -/
def proofOnly (rule : Rule) : Ty :=
  .byTag [("differential", .scalar [.null, .str] .null), ("proof", .scalar [.null, .str] rule)]

/-- Set (meeting `rule`) under differential evidence, null under proof (D3 nullness). -/
def differentialOnly (rule : Rule) : Ty :=
  .byTag [("differential", .scalar [.null, .str] rule), ("proof", .scalar [.null, .str] .null)]

/-- D3: a receipt's `digests` object. -/
def digestsTy : Ty :=
  .obj none
    [("adapter", differentialOnly .digest), ("impl_sources", proofOnly .digest),
      ("phase1_export", proofOnly .digest), ("proof_sources", proofOnly .digest),
      ("solution_export", proofOnly .digest), ("spec_closure", .scalar [.str] .digest)]

/-- D2: adapter argv = a nonempty array of arguments (`argv[0]` nonempty). -/
def argvTy : Ty :=
  .arr [.arr, .null] (.scalar [.str] (.arg true)) (.scalar [.str] (.arg false)) .nonempty

/-- D3: a receipt's `request` object. -/
def requestTy : Ty :=
  .obj none
    [("adapter", .byTag [("differential", argvTy), ("proof", .scalar [.arr, .null] .null)]),
      ("impl", proofOnly .constant), ("module", .scalar [.str] .moduleId),
      ("proof", proofOnly .constant), ("shape", proofOnly (.oneOf ["abi", "fn"])),
      ("version", .scalar [.str] .version)]

/-- D3: a receipt object; its `evidence` member selects the variant. -/
def receiptTy : Ty :=
  .obj (some (.str "evidence" ["differential", "proof"]))
    [("checked", .scalar [.str] .utc), ("digests", digestsTy), ("library", .scalar [.str] .commit),
      ("policy", .scalar [.str] (.oneOf ["development", "required"])), ("request", requestTy),
      ("verification_profile", .scalar [.str] .profile)]

/-- D4: the lock root; `schema` = 1 is its discriminator. -/
def lockTy : Ty :=
  .obj (some (.int "schema" 1))
    [("library", .scalar [.str] .commit),
      ("modules", .arr [.arr] receiptTy receiptTy (.ascending ["request", "module"]))]

/-! ## D3 + D4 encoding + extraction -/

def optStr : Option String → Value
  | some s => .str s
  | none => .null

def shapeText : Shape → String
  | .fn => "fn"
  | .abi => "abi"

def policyText : Policy → String
  | .required => "required"
  | .development => "development"

/-- A member's string payload ("" otherwise). -/
def textOf : Option Value → String
  | some (.str s) => s
  | _ => ""

/-- A member's string payload, `none` otherwise (JSON null included). -/
def textOpt : Option Value → Option String
  | some (.str s) => some s
  | _ => none

def membersOf : Option Value → List (String × Value)
  | some (.obj ms) => ms
  | _ => []

/-- Fallbacks for extraction; a value the walk accepts never uses them. -/
def defaultSeg : Seg := ⟨⟨0, by decide⟩, []⟩

def defaultModule : ModuleId := ⟨defaultSeg, defaultSeg, []⟩

def defaultCommit : Commit := ⟨List.replicate 40 ⟨0, by decide⟩, by decide⟩

/-- D3: the receipt a value accepted by `receiptTy` denotes; total, so decoding fails only
through the walk. -/
def receiptOfValue (v : Value) : Receipt :=
  let ms := membersOf (some v)
  let dg := membersOf (member? ms "digests")
  let rq := membersOf (member? ms "request")
  let kind : Kind := if textOf (member? ms "evidence") = "proof" then .proof else .differential
  let decl : Decl :=
    { module := (ModuleId.parse (textOf (member? rq "module"))).getD defaultModule
      version := (EntryVersion.parse (textOf (member? rq "version"))).getD ⟨0, 0, 0⟩
      shape :=
        match member? rq "shape" with
        | some (.str "fn") => some .fn
        | some (.str "abi") => some .abi
        | _ => none
      kind
      impl := textOpt (member? rq "impl")
      proof := textOpt (member? rq "proof")
      adapter :=
        match member? rq "adapter" with
        | some (.arr xs) => some (xs.map fun x => textOf (some x))
        | _ => none }
  let common : Common :=
    { request :=
        { decl
          specClosure := textOf (member? dg "spec_closure")
          implSources := textOpt (member? dg "impl_sources")
          proofSources := textOpt (member? dg "proof_sources")
          adapter := textOpt (member? dg "adapter") }
      library := (Commit.parse (textOf (member? ms "library"))).getD defaultCommit
      profile := textOf (member? ms "verification_profile")
      policy := if textOf (member? ms "policy") = "development" then .development else .required
      checked := textOf (member? ms "checked") }
  match kind with
  | .proof =>
    .proof common (textOf (member? dg "phase1_export")) (textOf (member? dg "solution_export"))
  | .differential => .differential common

/-- D4: the lock a value accepted by `lockTy` denotes (total). -/
def lockOfValue (v : Value) : Lock :=
  let ms := membersOf (some v)
  ⟨(Commit.parse (textOf (member? ms "library"))).getD defaultCommit,
    match member? ms "modules" with
    | some (.arr xs) => xs.map receiptOfValue
    | _ => []⟩

/-- The module id a lock sorts by (its printed spelling: byte order = `String` order). -/
def moduleKey (r : Receipt) : String := toString r.common.request.decl.module

/-- The receipt constructor matches its declaration's evidence kind (the layout's one `evidence`
member stands for both). -/
def kindAgrees : Receipt → Bool
  | .proof c .. => c.request.decl.kind == .proof
  | .differential c => c.request.decl.kind == .differential

end FvdepCore.Doc

namespace FvdepCore.Status

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Doc

/-- D3: the receipt's JSON object (`evidence` = the constructor's kind). -/
def Receipt.toJson (r : Receipt) : Value :=
  let c := r.common
  let q := c.request
  let d := q.decl
  let (kind, phase1, solution) : String × Option String × Option String :=
    match r with
    | .proof _ e1 e2 => ("proof", some e1, some e2)
    | .differential _ => ("differential", none, none)
  .obj
    [("checked", .str c.checked),
      ("digests",
        .obj
          [("adapter", optStr q.adapter), ("impl_sources", optStr q.implSources),
            ("phase1_export", optStr phase1), ("proof_sources", optStr q.proofSources),
            ("solution_export", optStr solution), ("spec_closure", .str q.specClosure)]),
      ("evidence", .str kind), ("library", .str (toString c.library)),
      ("policy", .str (policyText c.policy)),
      ("request",
        .obj
          [("adapter",
              match d.adapter with
              | some xs => .arr (xs.map .str)
              | none => .null),
            ("impl", optStr d.impl), ("module", .str (toString d.module)),
            ("proof", optStr d.proof), ("shape", optStr (d.shape.map shapeText)),
            ("version", .str (toString d.version))]),
      ("verification_profile", .str c.profile)]

/-- D3 + D5: the receipt a value denotes, else the first violation. -/
def Receipt.ofJson (v : Value) : Except DocError Receipt :=
  match walk "" receiptTy [] v with
  | some e => .error e
  | none => .ok (receiptOfValue v)

/-- D2 + D3: `WellFormed` as a check. -/
def Receipt.wellFormed (r : Receipt) : Bool :=
  kindAgrees r && (walk "" receiptTy [] r.toJson).isNone

/-- D4: the lock's JSON object. -/
def Lock.toJson (l : Lock) : Value :=
  .obj
    [("library", .str (toString l.library)), ("modules", .arr (l.entries.map Receipt.toJson)),
      ("schema", .int 1)]

/-- D4 + D5: the lock a value denotes, else the first violation. -/
def Lock.ofJson (v : Value) : Except DocError Lock :=
  match walk "" lockTy [] v with
  | some e => .error e
  | none => .ok (lockOfValue v)

/-- D2 + D4: `WellFormed` as a check. -/
def Lock.wellFormed (l : Lock) : Bool :=
  l.entries.all kindAgrees && (walk "" lockTy [] l.toJson).isNone

/-- D4: receipts stably sorted by module id. -/
def Lock.normalize (l : Lock) : Lock :=
  ⟨l.library, l.entries.mergeSort fun a b => decide (moduleKey a ≤ moduleKey b)⟩

end FvdepCore.Status

namespace FvdepCore.Doc

open Json Ids Evidence Status

/-- D4: `fvdep.lock`'s canonical bytes. -/
def encodeLock (l : Lock) : ByteArray := print l.toJson

/-- D4 + D5: the lock the bytes denote, else the first refusal. -/
def decodeLock (b : ByteArray) : Except LockError Lock :=
  match decode b with
  | .error j => .error (.text j)
  | .ok v =>
    match Lock.ofJson v with
    | .ok l => .ok l
    | .error d => .error (.doc d)

/-! ## D6 envelope -/

/-- D6: the `--json` commands (interface §3). -/
inductive Command where
  | check
  | list
  | lock
  | outdated
  | scan
  | status
  | upgrade
  deriving DecidableEq, Repr

def Command.spelling : Command → String
  | .check => "check"
  | .list => "list"
  | .lock => "lock"
  | .outdated => "outdated"
  | .scan => "scan"
  | .status => "status"
  | .upgrade => "upgrade"

/-- D6: interface §6's codes, in its order, + `busy`. -/
inductive PublicCode where
  | profileConstruct
  | importNotAllowed
  | reservedModule
  | buildFailed
  | statementMismatch
  | graphMismatch
  | axiom
  | kernelReject
  | kernelCrash
  | kernelTimeout
  | kernelDecline
  | sandboxSetup
  | toolMissing
  | staleReceipt
  | retracted
  | policyProofRequired
  | mismatch
  | notDelivered
  | usage
  | noProject
  | schema
  | toolchain
  | adapter
  | fetchFailed
  | io
  | commitIo
  | internal
  | busy
  deriving DecidableEq, Repr

def PublicCode.spelling : PublicCode → String
  | .profileConstruct => "profile_construct"
  | .importNotAllowed => "import_not_allowed"
  | .reservedModule => "reserved_module"
  | .buildFailed => "build_failed"
  | .statementMismatch => "statement_mismatch"
  | .graphMismatch => "graph_mismatch"
  | .axiom => "axiom"
  | .kernelReject => "kernel_reject"
  | .kernelCrash => "kernel_crash"
  | .kernelTimeout => "kernel_timeout"
  | .kernelDecline => "kernel_decline"
  | .sandboxSetup => "sandbox_setup"
  | .toolMissing => "tool_missing"
  | .staleReceipt => "stale_receipt"
  | .retracted => "retracted"
  | .policyProofRequired => "policy_proof_required"
  | .mismatch => "mismatch"
  | .notDelivered => "not_delivered"
  | .usage => "usage"
  | .noProject => "no_project"
  | .schema => "schema"
  | .toolchain => "toolchain"
  | .adapter => "adapter"
  | .fetchFailed => "fetch_failed"
  | .io => "io"
  | .commitIo => "commit_io"
  | .internal => "internal"
  | .busy => "busy"

/-- D6: the lifecycle status snapshot's state: its commit, fetch time + last fetch error. -/
structure SnapshotState where
  commit : Option Commit
  fetched : Option String
  fetchError : Option String

/-- D6: the exit-2 cause that stopped the command. -/
structure Failure where
  code : PublicCode
  detail : String

/-- D6: the `--json` envelope. -/
structure Envelope where
  command : Command
  exit : Exit
  error : Option Failure
  result : List (String × Value)
  status : SnapshotState
  trusted : List String

/-- D6: the envelope's JSON object (`toJson` clips the diagnostic strings). -/
def Envelope.toJson (e : Envelope) : Value :=
  .obj
    [("command", .str e.command.spelling),
      ("error",
        match e.error with
        | none => .null
        | some f => .obj [("code", .str f.code.spelling), ("detail", .str (clip f.detail))]),
      ("exit", .int e.exit.code.toNat), ("result", .obj e.result), ("schema", .int 1),
      ("status",
        .obj
          [("commit",
              match e.status.commit with
              | some c => .str (toString c)
              | none => .null),
            ("fetch_error", optStr (e.status.fetchError.map clip)),
            ("fetched", optStr e.status.fetched)]),
      ("trusted", .arr (e.trusted.map fun s => .str (clip s)))]

/-- Consecutive keys strictly ascend. -/
def keysAscending : List (String × Value) → Bool
  | a :: b :: rest => decide (a.1 < b.1) && keysAscending (b :: rest)
  | _ => true

mutual
/-- J1 validity with the depth bound `d`: integers + strings within the profile, every object's
keys strictly ascending, depth ≤ `d`. -/
def fits (d : Nat) : Value → Bool
  | .int n => n.natAbs ≤ maxInt
  | .str s => s.utf8ByteSize ≤ maxStringBytes
  | .arr xs => 1 ≤ d && fitsList (d - 1) xs
  | .obj ms => 1 ≤ d && keysAscending ms && fitsMembers (d - 1) ms
  | _ => true
def fitsList (d : Nat) : List Value → Bool
  | [] => true
  | v :: vs => fits d v && fitsList d vs
def fitsMembers (d : Nat) : List (String × Value) → Bool
  | [] => true
  | (k, v) :: ms => k.utf8ByteSize ≤ maxStringBytes && fits d v && fitsMembers d ms
end

/-- D6: `WellFormed` as a check. -/
def Envelope.wellFormed (e : Envelope) : Bool :=
  (e.error.isSome == (e.exit == .failure)) && fits 31 (.obj e.result) && e.status.fetched.all isUtc

end FvdepCore.Doc
