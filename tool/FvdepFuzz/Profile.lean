import FvdepCore.Profile.Record

/-! Fuzz target `profile-record` (contract U6 P5a + P5b): byte 0 even = raw (bytes 1.. through
`readRecord`, `readRequest` + `intake`: no panic, no hang; an accepted record or request prints back
to the very bytes, else panic); odd = generated (a record + a request built from the rest, printed,
read back: a well-formed one reads back equal, any other is refused, else panic). -/

namespace FvdepFuzz.ProfileT

open FvdepCore.Profile FvdepCore.Json

/-- Byte `i` of `b`, 0 past the end. -/
def byteOf (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then b[i].toNat else 0

def pick (xs : List String) (n : Nat) : String := xs.getD (n % xs.length) ""

/-- Module names across U3 T3's component syntax + a few outside it. -/
def moduleOf (n : Nat) : String :=
  pick
    ["Impl", "Impl.Util", "A.B.C", "Init", "Std.Time", "_x", "Impl._y", "x'", "Impl.", "", "a b",
      "Fvdep.Base64.Rfc4648.V1_0_0"]
    n

/-- 64 lowercase hex digits from byte `n`, one byte in 8 an uppercase or short spelling. -/
def digestOf (n : Nat) : String :=
  if n % 8 == 7 then "ABC"
  else
    String.ofList ((List.range 64).map fun k => "0123456789abcdef".toList.getD ((n + k) % 16) '0')

def detailOf (n : Nat) : String :=
  pick
    ["Lean.Parser.Command.eval", "depth", "nodes", "4096", "0", "007", "module", "prelude",
      "modifier", "public", "import", "name", "namespace", "open", "deriving", "_unsafe_rec",
      String.ofList (List.replicate 1025 'x'), "é", "\n"]
    n

def ruleOf (n : Nat) : String :=
  pick
    ["parse", "cap", "header", "scope", "ownership", "kind", "shape", "atom", "reserved", "name",
      "rule"]
    n

def outcomeOf (b : ByteArray) (i : Nat) : Outcome :=
  match byteOf b i % 3 with
  | 0 => .accepted
  | 1 => .over
  | _ =>
    let d := (List.range (byteOf b (i + 1) % 3)).map fun k => detailOf (byteOf b (i + 2 + k))
    .refused
      ⟨moduleOf (byteOf b (i + 5)), byteOf b (i + 6) % 4, byteOf b (i + 7),
        ruleOf (byteOf b (i + 8)), d⟩

def recordOf (b : ByteArray) : Record :=
  let ms :=
    (List.range (byteOf b 1 % 4)).map fun k =>
      ⟨moduleOf (byteOf b (2 + k)), digestOf (byteOf b (6 + k)),
        (List.range (byteOf b (10 + k) % 3)).map fun j => moduleOf (byteOf b (14 + j))⟩
  { modules := ms
    outcome := outcomeOf b 20
    profile := pick ["fvdep/profile/1", "fvdep/profile/2", ""] (byteOf b 30)
    recipe := pick ["consumer/1", "library/1"] (byteOf b 31)
    request := digestOf (byteOf b 32) }

def requestOf (b : ByteArray) : Request :=
  let names := ((List.range (byteOf b 33 % 4)).map fun k => moduleOf (byteOf b (34 + k))).eraseDups
  let role : Role := if byteOf b 38 % 2 == 0 then .consumer else .library
  { library :=
      (List.range (byteOf b 39 % 3)).map fun k =>
        ⟨moduleOf (byteOf b (40 + k)), (List.range (byteOf b (43 + k) % 3)).map fun j => moduleOf j⟩
    limits := { depth := byteOf b 46, nodes := byteOf b 47 + 1, batchNodes := byteOf b 48 + 2 }
    modules :=
      names.map fun m =>
        ⟨m, if byteOf b 49 % 5 == 0 then "x.lean" else modulePath m,
          digestOf (byteOf b 50 + m.length)⟩
    profile := "fvdep/profile/1"
    recipe := if byteOf b 51 % 7 == 0 then "consumer/1" else role.recipe
    role
    toolchain := digestOf (byteOf b 52) }

/-- A text reader's verdict on `b`: an accepted value prints back to `b` exactly. -/
def exact {α : Type} (read : ByteArray → Option α) (printer : α → ByteArray) (b : ByteArray) :
    Bool := match read b with
  | some v => (printer v).data == b.data
  | none => true

@[export fvdep_fuzz_profile]
def profileTarget (b : ByteArray) : UInt8 :=
  if byteOf b 0 % 2 == 0 then
    let s := b.extract 1 b.size
    let req := requestOf (ByteArray.mk #[1, 1, 2, 3])
    let bound :=
      match intake "fvdep/profile/1" req (digestOf 0) s with
      | .ok _ => (readRecord s).isSome
      | .error _ => true
    let ok :=
      exact readRecord (fun r => print r.toJson) s && exact readRequest (fun r => print r.toJson) s
    if ok && bound then 0 else panic! "profile-record: an accepted text misprints"
  else
    let r := recordOf b
    let q := requestOf b
    let rr := readRecord (print r.toJson)
    let rq := readRequest (print q.toJson)
    let ok :=
      (if r.ok then rr == some r else rr == none) && if q.ok then rq == some q else rq == none
    if ok then 0 else panic! "profile-record: a generated value did not read back"

end FvdepFuzz.ProfileT
