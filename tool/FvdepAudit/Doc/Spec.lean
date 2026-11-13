import FvdepAudit.Json.Spec
import FvdepCore.Doc

/-! Specs for fvdep's documents (contract `docs/contracts/U3-codecs.md` D1–D8), written from the
contract apart from `FvdepCore.Doc`'s code: the text bound (D1), field syntax + well-formedness
(D2–D4, D6), the refusal walk as the ordered list of EVERY violation (D5; the first is reported),
the layouts (D3, D4, D6). Shared with the code (data, not semantics): the schema syntax (`Ty`,
`Rule`, `Disc`, `Order`, `kindOf`) + the schema values `receiptTy`, `lockTy`; `ReceiptSchemaExact`
+ `LockSchemaExact` check those values against the layouts + `WellFormed` written here. Byte order:
schema fields are stored in ascending key order (`receiptTy_sorted`, `lockTy_sorted`) + a decoded
value's members ascend (J1 `Valid`), so this walk's stored order = D5's byte order. -/

namespace FvdepAudit.Doc.Spec

noncomputable section

open Classical
open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc

/-! ## D1 text bound -/

/-- UTF-8 bytes of a scalar list. -/
def bytes (cs : List Char) : Nat := (cs.map Char.utf8Size).sum

/-- Every prefix of `xs`, shortest first. -/
def prefixes {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => [] :: (prefixes xs).map (x :: ·)

/-- The longest prefix of `cs` within `n` UTF-8 bytes (a prefix of scalars ends on a scalar
boundary). -/
def longestPrefix (n : Nat) (cs : List Char) : List Char :=
  (((prefixes cs).filter fun p => bytes p ≤ n).getLast?).getD []

/-- D1: `s` within 65,536 bytes, else its longest prefix of ≤ 65,520 bytes + ` [truncated]`. -/
def clipSpec (s : String) : String :=
  if s.utf8ByteSize ≤ 65536 then s
  else String.ofList (longestPrefix 65520 s.toList) ++ " [truncated]"

/-! ## D2 field syntax -/

def Digit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

/-- 64 lowercase hex digits (`0`–`9`, `a`–`f`). -/
def DigestText (s : String) : Prop :=
  s.toList.length = 64 ∧ ∀ c ∈ s.toList, Digit c ∨ 'a' ≤ c ∧ c ≤ 'f'

/-- Two decimal digits as a number. -/
def num2 (a b : Char) : Nat := 10 * (a.toNat - '0'.toNat) + (b.toNat - '0'.toNat)

/-- `YYYY-MM-DDTHH:MM:SSZ`: digits; month 01–12, day 01–31, hour 00–23, minute 00–59, second 00–60
(no calendar check). -/
def UtcText (s : String) : Prop :=
  ∃ y1 y2 y3 y4 o1 o2 d1 d2 h1 h2 m1 m2 s1 s2 : Char,
    s.toList =
        [y1, y2, y3, y4, '-', o1, o2, '-', d1, d2, 'T', h1, h2, ':', m1, m2, ':', s1, s2, 'Z'] ∧
      (∀ c ∈ [y1, y2, y3, y4, o1, o2, d1, d2, h1, h2, m1, m2, s1, s2], Digit c) ∧
      1 ≤ num2 o1 o2 ∧
      num2 o1 o2 ≤ 12 ∧
      1 ≤ num2 d1 d2 ∧ num2 d1 d2 ≤ 31 ∧ num2 h1 h2 ≤ 23 ∧ num2 m1 m2 ≤ 59 ∧ num2 s1 s2 ≤ 60

/-- 1–1,024 UTF-8 bytes, no control character (U+0000–U+001F, U+007F). -/
def ConstantText (s : String) : Prop :=
  1 ≤ s.utf8ByteSize ∧ s.utf8ByteSize ≤ 1024 ∧ ∀ c ∈ s.toList, 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F

/-- 1–256 bytes of `[A-Za-z0-9._@+-]`. -/
def ProfileText (s : String) : Prop :=
  1 ≤ s.utf8ByteSize ∧
    s.utf8ByteSize ≤ 256 ∧
    ∀ c ∈ s.toList, 'A' ≤ c ∧ c ≤ 'Z' ∨ 'a' ≤ c ∧ c ≤ 'z' ∨ Digit c ∨ c ∈ ['.', '_', '@', '+', '-']

/-- An adapter argument: ≤ 65,536 UTF-8 bytes (`argv[0]`: ≥ 1), no U+0000. -/
def ArgText (first : Bool) (s : String) : Prop :=
  (first = true → 1 ≤ s.utf8ByteSize) ∧ s.utf8ByteSize ≤ 65536 ∧ '\x00' ∉ s.toList

/-- D2 adapter argv: ≥ 1 element, `argv[0]` 1–65,536 bytes, every later element 0–65,536. -/
def Argv (argv : List String) : Prop :=
  ∃ a rest, argv = a :: rest ∧ ArgText true a ∧ ∀ x ∈ rest, ArgText false x

/-- D2: a module id or entry version's printed spelling fits the document bound. -/
def SpellingFits (s : String) : Prop := s.utf8ByteSize ≤ 65536

/-- The meaning of each scalar rule (D2 syntax, enumerations, the evidence kind's nullness). -/
def ruleHolds : Rule → Value → Prop
  | .null, v => v = .null
  | .commit, v => ∃ c : Commit, v = .str (toString c)
  | .digest, v => ∃ s, v = .str s ∧ DigestText s
  | .utc, v => ∃ s, v = .str s ∧ UtcText s
  | .moduleId, v => ∃ m : ModuleId, v = .str (toString m) ∧ SpellingFits (toString m)
  | .version, v => ∃ x : EntryVersion, v = .str (toString x) ∧ SpellingFits (toString x)
  | .constant, v => ∃ s, v = .str s ∧ ConstantText s
  | .profile, v => ∃ s, v = .str s ∧ ProfileText s
  | .oneOf xs, v => ∃ s, v = .str s ∧ s ∈ xs
  | .arg first, v => ∃ s, v = .str s ∧ ArgText first s

/-! ## D5 refusal walk: every violation, in order -/

/-- `t` under the nearest enclosing string discriminator's value. -/
def resolveSpec (tag : String) : Ty → Ty
  | .byTag cs => (cs.lookup tag).getD (.byTag [])
  | t => t

/-- D5 (a): absent → `missing_field`; JSON kind outside the discriminator's → `wrong_type`; another
value → `bad_value` (nothing else in the object judged); else the tag for nested `byTag` types +
the discriminator's key (known, judged here). -/
def discSpec (tag : String) (p : List PathSeg) (ms : List (String × Value)) :
    Option Disc → Except DocError (String × List String)
  | none => .ok (tag, [])
  | some (.int k n) =>
    match ms.lookup k with
    | none => .error ⟨p ++ [.key k], .missingField, none⟩
    | some x =>
      if kindOf x ≠ .int then .error ⟨p ++ [.key k], .wrongType, some x⟩
      else if x = .int n then .ok (tag, [k]) else .error ⟨p ++ [.key k], .badValue, some x⟩
  | some (.str k xs) =>
    match ms.lookup k with
    | none => .error ⟨p ++ [.key k], .missingField, none⟩
    | some (.str s) =>
      if s ∈ xs then .ok (s, [k]) else .error ⟨p ++ [.key k], .badValue, some (.str s)⟩
    | some x => .error ⟨p ++ [.key k], .wrongType, some x⟩

/-- D5 (b): every member whose key the object does not define, in member order. -/
def unknownSpec (known : List String) (p : List PathSeg) (ms : List (String × Value)) :
    List DocError :=
  (ms.filter fun m => m.1 ∉ known).map fun m => ⟨p ++ [.key m.1], .unknownField, some m.2⟩

/-- D5 (d): every field the object lacks, in field order. -/
def missingSpec (ms : List (String × Value)) (p : List PathSeg) (keys : List String) :
    List DocError :=
  (keys.filter fun k => ms.lookup k = none).map fun k => ⟨p ++ [.key k], .missingField, none⟩

/-- A scalar type: `wrong_type` ⟺ the value's kind lies outside the general type; `bad_value` ⟺
inside it but the rule fails (one kind per value). -/
def leafSpec (ks : List JKind) (r : Rule) (p : List PathSeg) (v : Value) : List DocError :=
  if kindOf v ∈ ks then if ruleHolds r v then [] else [⟨p, .badValue, some v⟩]
  else [⟨p, .wrongType, some v⟩]

/-- An array type met by a value that is no array. -/
def kindMissSpec (ks : List JKind) (p : List PathSeg) (v : Value) : List DocError :=
  if kindOf v ∈ ks then [⟨p, .badValue, some v⟩] else [⟨p, .wrongType, some v⟩]

/-- The value at a key path inside nested objects. -/
def atPath : List String → Value → Option Value
  | [], v => some v
  | k :: ks, .obj ms => (ms.lookup k).bind (atPath ks)
  | _ :: _, _ => none

/-- D4: every element (index `i` onward) whose string at `path` is ≤ its predecessor's. -/
def descentsSpec (p : List PathSeg) (path : List String) : Nat → List Value → List DocError
  | i, a :: b :: rest =>
    (match atPath path a, atPath path b with
      | some (.str x), some (.str y) =>
        if x < y then [] else [⟨p ++ [.index i] ++ path.map .key, .badValue, some (.str y)⟩]
      | _, _ => []) ++
      descentsSpec p path (i + 1) (b :: rest)
  | _, _ => []

/-- D5 (e): an array's constraint, after its elements. -/
def orderSpec (p : List PathSeg) (xs : List Value) : Order → List DocError
  | .nonempty => if xs = [] then [⟨p, .badValue, some (.arr [])⟩] else []
  | .ascending path => descentsSpec p path 1 xs

mutual
/-- D5: every violation of `v` against `t` in walk order: the value's kind against the type; an
object's discriminator (alone when it fails), then unknown members, missing members, member
values in member order (recursively); an array's elements in index order, then its constraint. -/
def violations (tag : String) (t : Ty) (p : List PathSeg) : Value → List DocError
  | .obj ms =>
    match resolveSpec tag t with
    | .obj d fs =>
      match discSpec tag p ms d with
      | .error e => [e]
      | .ok (tag', extra) =>
        unknownSpec (extra ++ fs.map (·.1)) p ms ++ missingSpec ms p (fs.map (·.1)) ++
          memberViolations tag' fs p ms
    | .scalar ks r => leafSpec ks r p (.obj ms)
    | .arr ks .. => kindMissSpec ks p (.obj ms)
    | .byTag _ => [⟨p, .wrongType, some (.obj ms)⟩]
  | .arr xs =>
    match resolveSpec tag t with
    | .arr _ h tl o => elemViolations tag h tl p 0 xs ++ orderSpec p xs o
    | .scalar ks r => leafSpec ks r p (.arr xs)
    | .obj .. => [⟨p, .wrongType, some (.arr xs)⟩]
    | .byTag _ => [⟨p, .wrongType, some (.arr xs)⟩]
  | v =>
    match resolveSpec tag t with
    | .scalar ks r => leafSpec ks r p v
    | .arr ks .. => kindMissSpec ks p v
    | .obj .. => [⟨p, .wrongType, some v⟩]
    | .byTag _ => [⟨p, .wrongType, some v⟩]
/-- Member values in member order; a member without a field (unknown) has none here. -/
def memberViolations (tag : String) (fs : List (String × Ty)) (p : List PathSeg) :
    List (String × Value) → List DocError
  | [] => []
  | (k, x) :: ms =>
    (match fs.lookup k with
      | some t => violations tag t (p ++ [.key k]) x
      | none => []) ++
      memberViolations tag fs p ms
/-- Array elements in index order: element 0 against `h`, the rest against `tl`. -/
def elemViolations (tag : String) (h tl : Ty) (p : List PathSeg) (i : Nat) :
    List Value → List DocError
  | [] => []
  | x :: xs =>
    violations tag (if i = 0 then h else tl) (p ++ [.index i]) x ++
      elemViolations tag h tl p (i + 1) xs
end

/-- D5: the reported refusal = the first violation. -/
def firstViolation (t : Ty) (v : Value) : Option DocError := (violations "" t [] v).head?

/-! ## D3 + D4 layouts + well-formedness -/

def nullOr : Option String → Value
  | some s => .str s
  | none => .null

/-- D3: a receipt's JSON object; `evidence` = the receipt constructor's kind. -/
def receiptLayout (r : Receipt) : Value :=
  let c := r.common
  let q := c.request
  let d := q.decl
  .obj
    [("checked", .str c.checked),
      ("digests",
        .obj
          [("adapter", nullOr q.adapter), ("impl_sources", nullOr q.implSources),
            ("phase1_export",
              match r with
              | .proof _ e1 _ => .str e1
              | .differential _ => .null),
            ("proof_sources", nullOr q.proofSources),
            ("solution_export",
              match r with
              | .proof _ _ e2 => .str e2
              | .differential _ => .null),
            ("spec_closure", .str q.specClosure)]),
      ("evidence",
        match r with
        | .proof .. => .str "proof"
        | .differential _ => .str "differential"),
      ("library", .str (toString c.library)),
      ("policy",
        match c.policy with
        | .required => .str "required"
        | .development => .str "development"),
      ("request",
        .obj
          [("adapter",
              match d.adapter with
              | some argv => .arr (argv.map .str)
              | none => .null),
            ("impl", nullOr d.impl), ("module", .str (toString d.module)),
            ("proof", nullOr d.proof),
            ("shape",
              match d.shape with
              | some .fn => .str "fn"
              | some .abi => .str "abi"
              | none => .null),
            ("version", .str (toString d.version))]),
      ("verification_profile", .str c.profile)]

/-- D2 + D3: every field meets its syntax; the constructor = the declaration's evidence kind; a
proof receipt carries shape, constants, both source digests + both exports, no adapter; a
differential receipt the adapter argv + its digest, none of the proof fields. -/
def ReceiptWF (r : Receipt) : Prop :=
  let c := r.common
  let q := c.request
  let d := q.decl
  UtcText c.checked ∧
    ProfileText c.profile ∧
    SpellingFits (toString d.module) ∧
    SpellingFits (toString d.version) ∧
    DigestText q.specClosure ∧
    match r with
    | .proof _ e1 e2 =>
      d.kind = .proof ∧
        d.shape ≠ none ∧
        (∃ i, d.impl = some i ∧ ConstantText i) ∧
        (∃ x, d.proof = some x ∧ ConstantText x) ∧
        d.adapter = none ∧
        (∃ x, q.implSources = some x ∧ DigestText x) ∧
        (∃ x, q.proofSources = some x ∧ DigestText x) ∧
        q.adapter = none ∧ DigestText e1 ∧ DigestText e2
    | .differential _ =>
      d.kind = .differential ∧
        d.shape = none ∧
        d.impl = none ∧
        d.proof = none ∧
        (∃ argv, d.adapter = some argv ∧ Argv argv) ∧
        q.implSources = none ∧ q.proofSources = none ∧ ∃ x, q.adapter = some x ∧ DigestText x

/-- The id a lock orders by: the module id's printed spelling. -/
def idOf (r : Receipt) : String := toString r.common.request.decl.module

/-- D4: `{"library":commit,"modules":[receipt…],"schema":1}`. -/
def lockLayout (l : Lock) : Value :=
  .obj
    [("library", .str (toString l.library)), ("modules", .arr (l.entries.map receiptLayout)),
      ("schema", .int 1)]

/-- D2 + D4: every receipt well-formed; module ids strictly ascending in byte order. -/
def LockWF (l : Lock) : Prop :=
  (∀ r ∈ l.entries, ReceiptWF r) ∧ (l.entries.map idOf).Pairwise (· < ·)

/-! ## D6 envelope -/

/-- Interface §6: the name of each command with `--json` output. -/
def commandText : Command → String
  | .check => "check"
  | .list => "list"
  | .lock => "lock"
  | .outdated => "outdated"
  | .scan => "scan"
  | .status => "status"
  | .upgrade => "upgrade"

/-- Interface §6's codes + `busy` (contract F): each public code's spelling. -/
def codeText : PublicCode → String
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

/-- D6's layout; `detail`, `fetch_error` + `trusted` lines pass D1. -/
def envelopeLayout (e : Envelope) : Value :=
  .obj
    [("command", .str (commandText e.command)),
      ("error",
        match e.error with
        | none => .null
        | some f => .obj [("code", .str (codeText f.code)), ("detail", .str (clipSpec f.detail))]),
      ("exit",
        match e.exit with
        | .ok => .int 0
        | .negative => .int 1
        | .failure => .int 2),
      ("result", .obj e.result), ("schema", .int 1),
      ("status",
        .obj
          [("commit",
              match e.status.commit with
              | some c => .str (toString c)
              | none => .null),
            ("fetch_error", nullOr (e.status.fetchError.map clipSpec)),
            ("fetched", nullOr e.status.fetched)]),
      ("trusted", .arr (e.trusted.map fun s => .str (clipSpec s)))]

/-- D6: an error exactly when exit = 2; the result object J1-valid at depth ≤ 31 (the envelope
adds one level); `fetched` a UTC time when set. -/
def EnvelopeWF (e : Envelope) : Prop :=
  (e.error ≠ none ↔ e.exit = .failure) ∧
    FvdepAudit.Json.Spec.Valid (.obj e.result) ∧
    FvdepAudit.Json.Spec.depth (.obj e.result) ≤ 31 ∧ ∀ f, e.status.fetched = some f → UtcText f

end

end FvdepAudit.Doc.Spec
