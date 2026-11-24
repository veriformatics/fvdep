import FvdepCore.Manifest
import FvdepCore.Profile.Types

/-! P5a + P5b (contract `docs/contracts/U6-profile.md`): a batch's request + record as canonical J
values, each read back canonical-only (another JSON spelling of the same value is refused, as
`FvdepCore.Step.read`), + the supervisor's intake: the record bound to its request, the first
failure named in P5b's order. Pure. -/

namespace FvdepCore.Profile

open FvdepCore.Json

/-- A plain module name: U3 T3's component syntax + size, its reservation aside (I2 judges that). -/
def isModule (s : String) : Bool :=
  s.utf8ByteSize ≤ 256 && (FvdepCore.Ids.cut '.' s.toList).all FvdepCore.Manifest.isComponent

/-- A request or record label (a profile or recipe id): 1–256 UTF-8 bytes. -/
def isLabel (s : String) : Bool := 1 ≤ s.utf8ByteSize && s.utf8ByteSize ≤ 256

def isDetail (s : String) : Bool := s.utf8ByteSize ≤ detailMax

/-- A canonical decimal ≥ 1 (no leading zero). -/
def isPositive (s : String) : Bool :=
  match s.toList with
  | c :: cs => '1' ≤ c && c ≤ '9' && cs.all fun d => '0' ≤ d && d ≤ '9'
  | [] => false

/-- T: a rule + a detail of its arity + values. -/
def causeOk : String → List String → Bool
  | "parse", [_] => true
  | "cap", [l, n] => (l == "depth" || l == "nodes") && isPositive n
  | "header", [w] => w == "module" || w == "prelude"
  | "header", [w, v] =>
    (w == "modifier" && (v == "public" || v == "meta" || v == "all")) || w == "import" ||
      w == "name"
  | "scope", [w, _] => w == "namespace" || w == "open"
  | "ownership", [_] => true
  | "kind", [_] => true
  | "shape", [_] => true
  | "atom", [_, _] => true
  | "reserved", [_] => true
  | "name", [w, _] => w == "deriving"
  | _, _ => false

/-- `path` = `module`'s file under the snapshot root (`A.B` → `A/B.lean`). -/
def modulePath (m : String) : String := "/".intercalate (m.splitOn ".") ++ ".lean"

def ModuleRec.ok (m : ModuleRec) : Bool :=
  isModule m.module && FvdepCore.Doc.isDigest m.sha256 && m.grammar.all isModule

def Refusal.ok (r : Refusal) : Bool :=
  isModule r.module && 1 ≤ r.line && r.line ≤ maxInt && r.column ≤ maxInt && isLabel r.rule &&
    r.detail.all isDetail &&
    causeOk r.rule r.detail

def Outcome.ok : Outcome → Bool
  | .refused r => r.ok
  | _ => true

def Record.ok (r : Record) : Bool :=
  r.modules.all ModuleRec.ok && r.outcome.ok && isLabel r.profile && isLabel r.recipe &&
    FvdepCore.Doc.isDigest r.request

def LibModule.ok (l : LibModule) : Bool := isModule l.module && l.imports.all isModule

/-- The path's size bound restates what `modulePath` of a ≤ 256-byte name implies (≤ 261 bytes),
so the request's J text stays inside J's string cap without a lemma about `splitOn`. -/
def ReqModule.ok (m : ReqModule) : Bool :=
  isModule m.module && m.path == modulePath m.module && m.path.utf8ByteSize ≤ 1024 &&
    FvdepCore.Doc.isDigest m.sha256

def Limits.ok (l : Limits) : Bool :=
  1 ≤ l.depth && l.depth ≤ maxInt && 1 ≤ l.nodes && l.nodes ≤ maxInt && 1 ≤ l.batchNodes &&
    l.batchNodes ≤ maxInt

/-- `consumer/1` serves the consumer role, `library/1` the library role (U5 T2's recipes). -/
def Role.recipe : Role → String
  | .consumer => "consumer/1"
  | .library => "library/1"

/-- P5a + C1: both module lists strictly ascending by name (UTF-8 byte order = batch order), this
profile's literal id, the library role with no library rows (its batch = the library's modules). -/
def Request.ok (r : Request) : Bool :=
  r.library.all LibModule.ok && FvdepCore.Doc.ascendingStrs (r.library.map (·.module)) &&
    (r.role != .library || r.library.isEmpty) &&
    r.limits.ok &&
    r.modules.all ReqModule.ok &&
    FvdepCore.Doc.ascendingStrs (r.modules.map (·.module)) &&
    r.profile == profileId &&
    isLabel r.recipe &&
    r.recipe == r.role.recipe &&
    FvdepCore.Doc.isDigest r.toolchain

/-! ## J values (keys ascending: J's canonical order) -/

def strs (xs : List String) : Value := .arr (xs.map .str)

def ModuleRec.toJson (m : ModuleRec) : Value :=
  .obj [("grammar", strs m.grammar), ("module", .str m.module), ("sha256", .str m.sha256)]

def Outcome.toJson : Outcome → Value
  | .accepted => .obj [("kind", .str "accepted")]
  | .refused r =>
    .obj
      [("cause", .obj [("detail", strs r.detail), ("rule", .str r.rule)]),
        ("column", .int r.column), ("kind", .str "refused"), ("line", .int r.line),
        ("module", .str r.module)]
  | .over => .obj [("kind", .str "over"), ("limit", .str "batchNodes")]

def Record.toJson (r : Record) : Value :=
  .obj
    [("modules", .arr (r.modules.map ModuleRec.toJson)), ("outcome", r.outcome.toJson),
      ("profile", .str r.profile), ("recipe", .str r.recipe), ("request", .str r.request),
      ("schema", .int 1)]

def LibModule.toJson (l : LibModule) : Value :=
  .obj [("imports", strs l.imports), ("module", .str l.module)]

def ReqModule.toJson (m : ReqModule) : Value :=
  .obj [("module", .str m.module), ("path", .str m.path), ("sha256", .str m.sha256)]

def Limits.toJson (l : Limits) : Value :=
  .obj [("batchNodes", .int l.batchNodes), ("depth", .int l.depth), ("nodes", .int l.nodes)]

def Request.toJson (r : Request) : Value :=
  .obj
    [("library", .arr (r.library.map LibModule.toJson)), ("limits", r.limits.toJson),
      ("modules", .arr (r.modules.map ReqModule.toJson)), ("profile", .str r.profile),
      ("recipe", .str r.recipe), ("role", .str r.role.text), ("schema", .int 1),
      ("toolchain", .str r.toolchain)]

/-! ## Exact forms back (`none` = any other value) -/

def ModuleRec.ofJson : Value → Option ModuleRec
  | .obj [("grammar", .arr gs), ("module", .str m), ("sha256", .str h)] =>
    (FvdepCore.Doc.strsOf gs).map fun g => ⟨m, h, g⟩
  | _ => none

/-- A natural number from J's integer (`none` below zero). -/
def natOf (n : Int) : Option Nat := if 0 ≤ n then some n.toNat else none

def Outcome.ofJson : Value → Option Outcome
  | .obj [("kind", .str "accepted")] => some .accepted
  |
  .obj
      [("cause", .obj [("detail", .arr ds), ("rule", .str rule)]), ("column", .int c),
        ("kind", .str "refused"), ("line", .int l), ("module", .str m)] =>
    do
    let d ← FvdepCore.Doc.strsOf ds
    let c ← natOf c
    let l ← natOf l
    some (.refused ⟨m, l, c, rule, d⟩)
  | .obj [("kind", .str "over"), ("limit", .str "batchNodes")] => some .over
  | _ => none

def Record.ofJson : Value → Option Record
  |
  .obj
      [("modules", .arr ms), ("outcome", o), ("profile", .str p), ("recipe", .str rc),
        ("request", .str rq), ("schema", .int 1)] =>
    do
    let ms ← ms.mapM ModuleRec.ofJson
    let o ← Outcome.ofJson o
    let r : Record := ⟨ms, o, p, rc, rq⟩
    if r.ok then
      some r
    else
      none
  | _ => none

def LibModule.ofJson : Value → Option LibModule
  | .obj [("imports", .arr is), ("module", .str m)] => (FvdepCore.Doc.strsOf is).map fun i => ⟨m, i⟩
  | _ => none

def ReqModule.ofJson : Value → Option ReqModule
  | .obj [("module", .str m), ("path", .str p), ("sha256", .str h)] => some ⟨m, p, h⟩
  | _ => none

def Limits.ofJson : Value → Option Limits
  | .obj [("batchNodes", .int b), ("depth", .int d), ("nodes", .int n)] => do
    let b ← natOf b
    let d ← natOf d
    let n ← natOf n
    some ⟨d, n, b⟩
  | _ => none

def Role.ofText : String → Option Role
  | "consumer" => some .consumer
  | "library" => some .library
  | _ => none

def Request.ofJson : Value → Option Request
  |
  .obj
      [("library", .arr ls), ("limits", l), ("modules", .arr ms), ("profile", .str p),
        ("recipe", .str rc), ("role", .str ro), ("schema", .int 1), ("toolchain", .str t)] =>
    do
    let ls ← ls.mapM LibModule.ofJson
    let l ← Limits.ofJson l
    let ms ← ms.mapM ReqModule.ofJson
    let ro ← Role.ofText ro
    let r : Request := ⟨ls, l, ms, p, rc, ro, t⟩
    if r.ok then
      some r
    else
      none
  | _ => none

/-- P5b: the record whose canonical J text `b` is, else `none` (another spelling of the same value,
a field outside the schema or a value outside `Record.ok` included). -/
def readRecord (b : ByteArray) : Option Record := do
  let v ← (decode b).toOption
  let r ← Record.ofJson v
  if b.data == (print r.toJson).data then
    some r
  else
    none

/-- P5a: the request whose canonical J text `b` is, else `none` (the child's intake). -/
def readRequest (b : ByteArray) : Option Request := do
  let v ← (decode b).toOption
  let r ← Request.ofJson v
  if b.data == (print r.toJson).data then
    some r
  else
    none

/-! ## P5b's intake -/

/-- P5b: why a record fails intake (rendered `the result record <text>`). -/
inductive IntakeError where
  | malformed
  | profile (got : String)
  | request (got expected : String)
  | recipe (got : String)
  | count (got expected : Nat)
  | name (got : String) (index : Nat) (expected : String)
  | digest (got module expected : String)
  | outside (module : String)
  deriving DecidableEq, Repr

def IntakeError.text : IntakeError → String
  | .malformed => "is malformed"
  | .profile p => s!"names profile {p}"
  | .request g e => s!"names request {g}, expected {e}"
  | .recipe r => s!"names recipe {r}"
  | .count g e => s!"lists {g} modules, expected {e}"
  | .name g i e => s!"lists {g} at {i}, expected {e}"
  | .digest g m e => s!"has digest {g} for {m}, expected {e}"
  | .outside m => s!"refuses {m}, outside the batch"

/-- The first position (1-based from `i`) where the record names another module than the request. -/
def firstName (i : Nat) : List ModuleRec → List ReqModule → Option IntakeError
  | m :: ms, q :: qs =>
    if m.module == q.module then firstName (i + 1) ms qs else some (.name m.module i q.module)
  | _, _ => none

/-- The first module whose recorded digest differs from the request's (S1's). -/
def firstDigest : List ModuleRec → List ReqModule → Option IntakeError
  | m :: ms, q :: qs =>
    if m.sha256 == q.sha256 then firstDigest ms qs else some (.digest m.sha256 m.module q.sha256)
  | _, _ => none

/-- P5b's intake of the record bytes `b` for `req` (its J text's SHA-256 = `digest`) under the
supervisor's profile id: the first failure in P5b's order, else the record. -/
def intake (profile : String) (req : Request) (digest : String) (b : ByteArray) :
    Except IntakeError Record := do
  let some r := readRecord b | throw .malformed
  unless r.profile == profile do
    throw (.profile r.profile)
  unless r.request == digest do
    throw (.request r.request digest)
  unless r.recipe == req.recipe do
    throw (.recipe r.recipe)
  unless r.modules.length == req.modules.length do
    throw (.count r.modules.length req.modules.length)
  if let some e := firstName 1 r.modules req.modules then
    throw e
  if let some e := firstDigest r.modules req.modules then
    throw e
  if let .refused f := r.outcome then
    unless req.modules.any (·.module == f.module) do
      throw (.outside f.module)
  return r

end FvdepCore.Profile
