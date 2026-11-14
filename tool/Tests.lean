import FvdepCore
import FvdepIO.Sha256
import FvdepIO.Sys
import FvdepIO.Toml

/-! `lake test` driver (contract U1 K3): PASS/FAIL per case, the slowest case, exit = failures.
Generated cases use a fixed seed (printed; `FVDEP_TEST_SEED` overrides it for exploration), so a
red reruns from committed state. -/

open FvdepCore.Cli

/-- One case: name, verdict, wall-clock (ms). -/
structure Result where
  name : String
  ok : Bool
  ms : Nat

def check (name : String) (ok : Unit → Bool) : IO Result := do
  let t0 ← IO.monoMsNow
  let held := ok ()
  let t1 ← IO.monoMsNow
  IO.println s!"{if held then "PASS" else "FAIL"} {name}"
  return ⟨name, held, t1 - t0⟩

/-- An exception = FAIL (its message on stderr), never an aborted run. -/
def checkIO (name : String) (ok : IO Bool) : IO Result := do
  let t0 ← IO.monoMsNow
  let held ←
    try
      ok
    catch e =>
      IO.eprintln s!"{name}: {e}"
      pure false
  let t1 ← IO.monoMsNow
  IO.println s!"{if held then "PASS" else "FAIL"} {name}"
  return ⟨name, held, t1 - t0⟩

/-- splitmix64: next output + next state. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- Tokens near the grammar's edges: real names, case + spacing variants, options, empties. -/
def tokens : Array String :=
  #["help", "--help", "--version", "-h", "-v", "version", "check", "--json", "", " ", "HELP",
    "help ", "--", "-", "fvdep", "--version=1", "--Help", "x"]

/-- `count` argument lists of 0–3 tokens from `seed`. -/
def argLists (seed : UInt64) (count : Nat) : List (List String) :=
  Id.run do
    let mut s := seed
    let mut out := []
    for _ in [0:count] do
      let (r, s') := splitmix s
      s := s'
      let mut args := []
      for _ in [0:(r % 4).toNat] do
        let (t, s'') := splitmix s
        s := s''
        args := tokens[(t % tokens.size.toUInt64).toNat]! :: args
      out := args :: out
    return out

/-- The contract's outcome for `args` (K2 + `docs/interface.md` §1), stated as a table. -/
def expected (args : List String) : Outcome :=
  if args == ["--version"] then ⟨s!"fvdep {Fvdep.version}\n", "", 0⟩
  else
    if [["--help"], ["help"], ["help", "help"], ["help", "--help"]].contains args then
      ⟨usage, "", 0⟩
    else ⟨"", usage, 2⟩

/-! Core regressions (contract U2 E3, E5, P7, P9): named cases from reviewer-2's counterexamples. -/

namespace Core

open FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status

def seg : Seg := ⟨⟨0, by decide⟩, []⟩

def modId : ModuleId := ⟨seg, seg, []⟩

def commit : Commit := ⟨List.replicate 40 ⟨0, by decide⟩, by decide⟩

def decl : Decl := ⟨modId, ⟨1, 0, 0⟩, some .fn, .proof, some "Impl.f", some "Proof.eq", none⟩

def request : RequestKey := ⟨decl, "spec", some "impl", some "proof", none⟩

def profile : Profile := ⟨"qualified-v1", ["propext", "Classical.choice", "Quot.sound"]⟩

def key : ChallengeKey := ⟨request, commit, profile, "statement"⟩

/-- Phases 0–2 passed; the statement did not match. -/
def statementFailed : List Observation :=
  [Obs.implProfile none, .phase1 (.ok "e1"), .phase2 "e1" (.ok "e2"),
        .statement "e1" "e2" false].map
    fun o => ⟨key, o⟩

def base : FvdepCore.Evidence.Result := result key statementFailed

def diffKey : ChallengeKey :=
  { key with
    request :=
      { request with
        decl :=
          { decl with
            kind := .differential
            shape := none
            impl := none
            proof := none
            adapter := some ["adapter"] }
        implSources := none
        proofSources := none
        adapter := some "adapter" } }

def comparison : Observation :=
  ⟨diffKey, .compare "adapter" "encode" "00" (.mismatch "wrong" "right")⟩

def common : Common := ⟨request, commit, profile.id, .required, "now"⟩

/-- An empty manifest + a lock with one entry: the files disagree. -/
def emptyManifest : Manifest := ⟨commit, []⟩

def extraLock : Lock := ⟨commit, [.proof common "e1" "e2"]⟩

def outOfDateNamed : LockState → Bool
  | .outOfDate cs => !cs.isEmpty
  | _ => false

def cases : List (String × (Unit → Bool)) :=
  [("core: a failed statement is NOT PROVEN with statement_mismatch", fun _ =>
      match base with
      | .verdict .notProven rs => rs.any (·.code == .statementMismatch)
      | _ => false),
    ("core E3: an observation bound to other exports never changes the result", fun _ =>
      result key (statementFailed ++ [⟨key, .graph "other-e1" "other-e2" true⟩]) == base),
    ("core E5: a protocol violation keeps the failed phase's reasons", fun _ =>
      match base, result key (statementFailed ++ [⟨key, .graph "e1" "e2" true⟩]) with
      | .verdict .notProven rs, .infra cause ns => cause.code == .internal && ns == rs
      | _, _ => false),
    ("core E3: an identical comparison counts once", fun _ =>
      result diffKey [comparison, comparison] == result diffKey [comparison]),
    ("core P7: files that disagree → development status exit 1, no manifest module too", fun _ =>
      statusExit .development emptyManifest extraLock ⟨[]⟩ [] == .negative),
    ("core P7: files that disagree → required status exit 1, no manifest module too", fun _ =>
      statusExit .required emptyManifest extraLock ⟨[]⟩ [] == .negative),
    ("core P9: an export-only lock difference names its change", fun _ =>
      outOfDateNamed (lockState (some (.proof common "e1" "e2")) (.proof common "e1'" "e2"))),
    ("core P9: a policy-only lock difference names its change", fun _ =>
      outOfDateNamed
        (lockState (some (.proof common "e1" "e2"))
          (.proof { common with policy := .development } "e1" "e2")))]

end Core

/-! Compiled-code smoke for the JSON codec (contract U3 J3, J5): the proofs cover the definitions,
these run the compiled C, incl. the error-path loops over 10^6 siblings (stack safety). -/

namespace Json

open FvdepCore.Json

def text (s : String) : ByteArray := s.toUTF8

/-- `decode` names this duplicate-key site. -/
def siteIs (s : String) (site : List PathSeg × String) : Bool :=
  match decode (text s) with
  | .error (.duplicateKey got) => got == site
  | _ => false

/-- 10^6 integers, then an object repeating a key. -/
def longArray : String :=
  "[" ++ String.intercalate "," (List.replicate 1000000 "0") ++ ",{\"a\":1,\"a\":2}]"

/-- An object with 10^6 distinct keys + one late repeat of `k500000`. -/
def flatObject : String :=
  "{" ++ String.intercalate "," ((List.range 1000000).map fun i => s!"\"k{i}\":0") ++
    ",\"k500000\":1}"

def cases : List (String × (Unit → Bool)) :=
  [("json: J3 site example 1: {\"a\":{\"b\":1,\"b\":2},\"a\":3} → ([], a)", fun _ =>
      siteIs "{\"a\":{\"b\":1,\"b\":2},\"a\":3}" ([], "a")),
    ("json: J3 site example 2 → ([1], c)", fun _ =>
      siteIs "[{\"x\":1},{\"y\":1,\"y\":2,\"c\":3,\"c\":4}]" ([.index 1], "c")),
    ("json: a nested site names its key + index path", fun _ =>
      siteIs "{\"p\":[{\"q\":{\"z\":0,\"z\":1}}]}" ([.key "p", .index 0, .key "q"], "z")),
    ("json: an escaped alias repeats its key", fun _ => siteIs "{\"a\":1,\"\\u0061\":2}" ([], "a")),
    ("json: decode → canonical value; print → canonical text; decode ∘ print = id", fun _ =>
      match decode (text "{ \"b\" : [1, -2, \"\\u00e9\"], \"a\" : null }") with
      | .ok v =>
        (print v).data == (text "{\"a\":null,\"b\":[1,-2,\"é\"]}").data &&
          match decode (print v) with
          | .ok w => w == v
          | .error _ => false
      | .error _ => false),
    ("json: a site after 10^6 array elements (no stack overflow)", fun _ =>
      siteIs longArray ([.index 1000000], "a")),
    ("json: a late repeat among 10^6 object keys", fun _ => siteIs flatObject ([], "k500000"))]

end Json

/-! Compiled-code smoke for the documents (contract U3 D1, D3–D6, D8): the proofs cover the
definitions, these run the compiled C, incl. a 10^4-receipt lock (walk + extraction + sort). -/

namespace Doc

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc

def mid (s : String) : ModuleId := (ModuleId.parse s).getD Core.modId

def ver : EntryVersion := (EntryVersion.parse "1.0.0").getD ⟨0, 0, 0⟩

def cm : Commit := (Commit.parse (String.ofList (List.replicate 40 'a'))).getD Core.commit

def d64 (c : Char) : String := String.ofList (List.replicate 64 c)

def proofReceipt (m : String) : Receipt :=
  .proof
    ⟨⟨⟨mid m, ver, some .fn, .proof, some "Impl.f", some "Proof.eq", none⟩, d64 'a', some (d64 'b'),
        some (d64 'c'), none⟩,
      cm, "qualified-v1", .required, "2026-11-14T00:00:00Z"⟩
    (d64 'd') (d64 'e')

def diffReceipt (m : String) : Receipt :=
  .differential
    ⟨⟨⟨mid m, ver, none, .differential, none, none, some ["python3", "", "a.py"]⟩, d64 'a', none,
        none, some (d64 'f')⟩,
      cm, "qualified-v1", .development, "2026-11-14T00:00:00Z"⟩

/-- Alternating proof + differential receipts for the module ids. -/
def lockOf (ms : List String) : Lock :=
  ⟨cm, ms.zipIdx.map fun (m, i) => if i % 2 == 0 then proofReceipt m else diffReceipt m⟩

/-- `m00000.op`, `m00001.op`, …: zero-padded, so byte order = index order. -/
def ids (n : Nat) : List String :=
  (List.range n).map fun i =>
    let s := toString i
    "m" ++ String.ofList (List.replicate (5 - s.length) '0') ++ s ++ ".op"

def roundTrips (l : Lock) : Bool :=
  match decodeLock (encodeLock l) with
  | .ok l' => l' == l
  | .error _ => false

def rendered (s : String) : String :=
  match decodeLock s.toUTF8 with
  | .ok _ => "ok"
  | .error e => e.render

/-- The receipt's `request.adapter` member replaced by `x`. -/
def withAdapter (x : Value) : Value → Value
  | .obj ms =>
    .obj <|
      ms.map fun (k, v) =>
        if k = "request" then
          (k,
            match v with
            | .obj rs => .obj (rs.map fun (k2, v2) => if k2 = "adapter" then (k2, x) else (k2, v2))
            | other => other)
        else (k, v)
  | v => v

/-- An array nested `k` deep around `null` (depth `k`). -/
def nest : Nat → Value
  | 0 => .null
  | k + 1 => .arr [nest k]

def envelope (exit : Exit) (error : Option Failure) (result : List (String × Value)) : Envelope :=
  ⟨.check, exit, error, result, ⟨some cm, some "2026-11-14T00:00:00Z", none⟩, ["Lean runtime"]⟩

def cases : List (String × (Unit → Bool)) :=
  [("doc: a well-formed lock (proof + differential receipts) round-trips through its bytes",
      fun _ =>
      let l := lockOf ["base64.decode", "base64.encode"]
      l.wellFormed && roundTrips l),
    ("doc: an unsorted lock is refused at the second module id; normalize repairs it", fun _ =>
      let l := lockOf ["base64.encode", "base64.decode"]
      !l.wellFormed && l.normalize.wellFormed &&
        rendered ((String.fromUTF8? (encodeLock l)).getD "") ==
          "/modules/1/request/module bad_value \"base64.decode\""),
    ("doc: text refusals come first (J3)", fun _ =>
      rendered "x" == "malformed" && rendered "{\"a\":1,\"a\":2}" == "duplicate_key /a"),
    ("doc: D5 root + discriminator refusals", fun _ =>
      rendered "[]" == "wrong_type []" && rendered "{}" == "/schema missing_field" &&
        rendered "{\"schema\":\"1\"}" == "/schema wrong_type \"1\"" &&
        rendered "{\"schema\":2}" == "/schema bad_value 2"),
    ("doc: unknown members before missing ones; RFC 6901 escaping", fun _ =>
      rendered "{\"schema\":1,\"zz\":0,\"a/b~c\":1}" == "/a~1b~0c unknown_field 1"),
    ("doc: a nullness violation fails at the field itself (proof receipt, adapter [1])", fun _ =>
      match Receipt.ofJson (withAdapter (.arr [.int 1]) (proofReceipt "base64.encode").toJson) with
      | .error e => e.render == "/request/adapter bad_value [1]"
      | .ok _ => false),
    ("doc: clip keeps 65,536 bytes whole, cuts longer text to 65,532 bytes", fun _ =>
      let whole := String.ofList (List.replicate 65536 'x')
      let long := clip (String.ofList (List.replicate 70000 'é'))
      clip whole == whole && long.utf8ByteSize == 65532 && long.endsWith " [truncated]"),
    ("doc: envelope: result depth 31 ok, 32 refused; error exactly when exit 2", fun _ =>
      (envelope .ok none [("r", nest 30)]).wellFormed &&
        !(envelope .ok none [("r", nest 31)]).wellFormed &&
        !(envelope .failure none []).wellFormed &&
        (envelope .failure (some ⟨.busy, "x"⟩) []).wellFormed &&
        !(envelope .negative (some ⟨.schema, "x"⟩) []).wellFormed),
    ("doc: a 10^4-receipt lock round-trips; normalize sorts its reversal back", fun _ =>
      let l := lockOf (ids 10000)
      let r : Lock := ⟨l.library, l.entries.reverse⟩
      roundTrips l && r.normalize == l),
    ("doc: line rule: TAB, LF, CR short; every other Cc (C0, DEL, C1) → \\u00XX uppercase", fun _ =>
      escapeControls "a\tb\nc\rd\x00e\x1bf\x7fg\u0085h\u009bi" ==
        "a\\tb\\nc\\rd\\u0000e\\u001Bf\\u007Fg\\u0085h\\u009Bi"),
    ("doc: line rule: no Cc survives; every other character as is", fun _ =>
      let all :=
        (List.range 0x2100).map Char.ofNat ++
          [Char.ofNat 0x2028, Char.ofNat 0xFEFF, Char.ofNat 0x10FFFF]
      let plain := all.filter (!isControl ·)
      !(escapeControls (String.ofList all)).toList.any isControl &&
        escapeControls (String.ofList plain) == String.ofList plain)]

end Doc

/-! Compiled-code smoke for hashing (contract U3 S3, S5, H1–H3): FIPS 180-4 example digests through
HACL*'s C, streaming = one-shot over splits + shared states, hex + frame bytes, `unframe` refusals.
The blind suite (`tests/codec/`) carries NIST CAVP + the `sha256sum` differential. -/

namespace Hash

open FvdepCore.Hash FvdepIO.Hash

def bytes (xs : List Nat) : ByteArray := ⟨(xs.map Nat.toUInt8).toArray⟩

def text (s : String) : ByteArray := s.toUTF8

/-- `n < 256` as 8 big-endian bytes. -/
def be (n : Nat) : List Nat := [0, 0, 0, 0, 0, 0, 0, n]

def hexOf (b : ByteArray) : String := hex (sha256 b)

def million : ByteArray := ⟨(List.replicate 1000000 (97 : UInt8)).toArray⟩

/-- `b` fed in chunks of `n` bytes (the last shorter). -/
def chunked (b : ByteArray) (n : Nat) : ByteArray :=
  Sha256.finish <|
    (List.range ((b.size + n - 1) / n)).foldl
      (fun s i => Sha256.update s (b.extract (i * n) (i * n + n))) Sha256.init

def msg448 : String := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

def cases : List (String × (Unit → Bool)) :=
  [("sha256: FIPS 180-4 examples (empty, abc, 448-bit, 10^6 × a)", fun _ =>
      hexOf .empty == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" &&
        hexOf (text "abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" &&
        hexOf (text msg448) == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" &&
        hexOf million == "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"),
    ("sha256: update over 1, 7, 55, 63, 64, 65, 4096-byte chunks = one-shot", fun _ =>
      let b := (text msg448).extract 0 56 ++ million.extract 0 9000
      [1, 7, 55, 63, 64, 65, 4096].all fun n => (chunked b n).data == (sha256 b).data),
    ("sha256: a shared state branches without interference + stays reusable", fun _ =>
      let s := Sha256.update Sha256.init (text "abc")
      let x := Sha256.finish (Sha256.update s (text msg448))
      let y := Sha256.finish (Sha256.update s million)
      x.data == (sha256 (text ("abc" ++ msg448))).data &&
        y.data == (sha256 (text "abc" ++ million)).data &&
        (Sha256.finish s).data == (sha256 (text "abc")).data),
    ("hex: two lowercase digits per byte, high nibble first", fun _ =>
      hex (bytes [0, 15, 16, 160, 255]) == "000f10a0ff" && hex .empty == ""),
    ("frame: H2 layout (multibyte tag + path, files in path order, UTF-8 lengths)", fun _ =>
      (frame "t\u00e9" [("b", bytes [1]), ("\u00e9", .empty), ("a", bytes [2, 3])]).data ==
        (bytes
            ([0, 0, 0, 0, 0, 0, 0, 3, 116, 195, 169, 0, 0, 0, 0, 0, 0, 0, 3] ++
              [0, 0, 0, 0, 0, 0, 0, 1, 97, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3] ++
              [0, 0, 0, 0, 0, 0, 0, 1, 98, 0, 0, 0, 0, 0, 0, 0, 1, 1] ++
              [0, 0, 0, 0, 0, 0, 0, 2, 195, 169, 0, 0, 0, 0, 0, 0, 0, 0])).data),
    ("unframe: frame round trip; truncation, a trailing byte, unsorted + repeated paths → none",
      fun _ =>
      let fs := [("b", bytes [1]), ("a", bytes [2, 3])]
      let f := frame "tag" fs
      let sorted := [("a", bytes [2, 3]), ("b", bytes [1])]
      (match unframe f with
        | some (t, gs) =>
          t == "tag" && gs.map (fun g => (g.1, g.2.data)) == sorted.map (fun g => (g.1, g.2.data))
        | none => false) &&
        (unframe (f.extract 0 (f.size - 1))).isNone &&
        (unframe (f.push 0)).isNone &&
        (unframe
            (bytes
              (be 3 ++ [116, 97, 103] ++ be 2 ++ be 1 ++ [98] ++ be 0 ++ be 1 ++ [97] ++
                be 0))).isNone &&
        (unframe
            (bytes
              (be 3 ++ [116, 97, 103] ++ be 2 ++ be 1 ++ [97] ++ be 0 ++ be 1 ++ [97] ++
                be 0))).isNone),
    ("digest: hex SHA-256 of the tagged frame; adapter entries: argv first, named paths once",
      fun _ =>
      digest .entry [("x", text "y")] == hexOf (frame "fvdep/entry/1" [("x", text "y")]) &&
        (adapterEntries ["run", "a.py", "a.py"]
                [("a.py", text "1"), ("a.py", text "1"), ("", text "2")]).map
            (·.1) ==
          ["", "a.py"] &&
        (argvBytes ["ab", ""]).data ==
          (bytes
              [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 97, 98, 0, 0, 0, 0, 0, 0, 0,
                0]).data)]

end Hash

/-! Compiled-code smoke for `fvdep.toml` (contract U3 T1–T4): the text stage's order + offsets,
validation + refusal order, the canonical bytes, the read path through Lake's parser. The blind
suite (`tests/manifest/`) carries the T3 oracle, the T4 encoder + `tomllib`. -/

namespace Manifest

open FvdepCore.Manifest FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepIO.Toml

def bytes (xs : List Nat) : ByteArray := ⟨(xs.map Nat.toUInt8).toArray⟩

def textError? : Except TextError String → Option TextError
  | .error e => some e
  | .ok _ => none

def textOk? : Except TextError String → Option String
  | .ok s => some s
  | .error _ => none

def lib : String := "0123456789abcdef0123456789abcdef01234567"

def commit : Commit := (Commit.parse lib).getD FvdepCore.Doc.defaultCommit

def proofEntry : Entry :=
  { decl :=
      { module := (ModuleId.parse "base64.encode").getD FvdepCore.Doc.defaultModule
        version := ⟨1, 0, 0⟩
        shape := some .abi
        kind := .proof
        impl := some "Impl.encode"
        proof := some "Proof.encode_eq"
        adapter := none }
    implModules := ["Impl", "Impl.B"]
    proofModules := ["Proof"] }

def diffEntry : Entry :=
  { decl :=
      { module := (ModuleId.parse "base64.decode").getD FvdepCore.Doc.defaultModule
        version := ⟨1, 2, 3⟩
        shape := none
        kind := .differential
        impl := none
        proof := none
        adapter := some ["py\"th\\on\u0001", "", "é😀\x7f"] }
    implModules := []
    proofModules := [] }

def sample : ManifestFile := ⟨commit, .development, [diffEntry, proofEntry]⟩

def sampleText : String :=
  "schema = 1\n\n[library]\ncommit = \"" ++ lib ++ "\"\n\n[policy]\nproof = \"development\"\n\n" ++
    "[modules.\"base64.decode\"]\nversion = \"1.2.3\"\nevidence = \"differential\"\n" ++
    "adapter = [\"py\\\"th\\\\on\\u0001\", \"\", \"é😀\\u007F\"]\n\n[modules.\"base64.encode\"]\n" ++
    "version = \"1.0.0\"\nshape = \"abi\"\nimpl_modules = [\"Impl\", \"Impl.B\"]\n" ++
    "proof_modules = [\"Proof\"]\nimpl = \"Impl.encode\"\nproof = \"Proof.encode_eq\"\n"

def root (ms : List (String × Tree)) : Tree :=
  .tbl ([("schema", .int 1), ("library", .tbl [("commit", .str lib)])] ++ ms)

def acceptsAs (t : Tree) (m : ManifestFile) : Bool :=
  match validate t with
  | .ok m' => m' == m
  | .error _ => false

def refusedAs (t : Tree) (e : ManifestError) : Bool :=
  match validate t with
  | .error e' => e' == e
  | .ok _ => false

def cases : List (String × (Unit → Bool)) :=
  [("manifest: text stage = size, then BOM, then the first UTF-8 offset, else the text", fun _ =>
      let big := bytes (List.replicate 65537 97)
      textError? (textStage big) == some .tooLarge &&
        textError? (textStage (bytes ([0xEF, 0xBB, 0xBF] ++ List.replicate 65534 97))) ==
          some .tooLarge &&
        textError? (textStage (bytes [0xEF, 0xBB, 0xBF, 0x61])) == some .bom &&
        textError? (textStage (bytes [0x61, 0xC3, 0x28])) == some (.utf8 1) &&
        textOk? (textStage (bytes (List.replicate 65536 97))) ==
          some (String.ofList (List.replicate 65536 'a'))),
    ("manifest: utf8ErrorOffset = the longest valid prefix (truncated, overlong, surrogate)",
      fun _ =>
      utf8ErrorOffset (bytes [0xE2, 0x82]) == some 0 &&
        utf8ErrorOffset (bytes [0x41, 0xE2, 0x82]) == some 1 &&
        utf8ErrorOffset (bytes [0xC0, 0x80]) == some 0 &&
        utf8ErrorOffset (bytes [0xED, 0xA0, 0x80]) == some 0 &&
        utf8ErrorOffset (bytes [0xF0, 0x9F, 0x98, 0x80, 0xFF]) == some 4 &&
        utf8ErrorOffset (bytes [0xF0, 0x9F, 0x98, 0x80]) == none),
    ("manifest: printManifest = the canonical bytes (escapes, \\u00XX, non-BMP)", fun _ =>
      (printManifest sample).data == sampleText.toUTF8.data),
    ("manifest: validate (toTree m) = m, member order free", fun _ =>
      let t :=
        root
          [("policy", .tbl [("proof", .str "development")]),
            ("modules",
              .tbl
                [("base64.encode", .tbl ((entryMembers proofEntry).reverse)),
                  ("base64.decode", .tbl (entryMembers diffEntry))])]
      acceptsAs (toTree sample) sample && acceptsAs t sample),
    ("manifest: refusal order: repeated key, schema, unknown (byte order), missing library",
      fun _ =>
      refusedAs (.tbl [("b", .int 1), ("a", .int 1), ("b", .int 2), ("a", .int 3)])
          ⟨[], .duplicateKey "a"⟩ &&
        refusedAs (.tbl [("library", .int 1)]) ⟨[.key "schema"], .missingField⟩ &&
        refusedAs (.tbl [("schema", .str "1")]) ⟨[.key "schema"], .wrongType .integer⟩ &&
        refusedAs (.tbl [("schema", .int 2)]) ⟨[.key "schema"], .badValue⟩ &&
        refusedAs (.tbl [("schema", .int 1), ("zeta", .int 1), ("alpha", .int 1)])
          ⟨[.key "alpha"], .unknownField⟩ &&
        refusedAs (.tbl [("schema", .int 1)]) ⟨[.key "library"], .missingField⟩ &&
        refusedAs (.arr []) ⟨[], .wrongType .table⟩),
    ("manifest: entry rules: evidence kinds, forbidden + missing keys, list repeats, overlap",
      fun _ =>
      let entry (ms : List (String × Tree)) := root [("modules", .tbl [("base64.encode", .tbl ms)])]
      let p := [FvdepCore.Json.PathSeg.key "modules", .key "base64.encode"]
      refusedAs (entry [("evidence", .str "proof")]) ⟨p ++ [.key "evidence"], .badValue⟩ &&
        refusedAs (entry [("evidence", .int 1)]) ⟨p ++ [.key "evidence"], .wrongType .string⟩ &&
        refusedAs
          (entry
            [("evidence", .str "differential"), ("version", .str "1.0.0"),
              ("adapter", .arr [.str "x"]), ("shape", .str "fn")])
          ⟨p ++ [.key "shape"], .forbiddenField⟩ &&
        refusedAs (entry [("version", .str "1.0.0")]) ⟨p ++ [.key "impl"], .missingField⟩ &&
        refusedAs
          (entry
            ((entryMembers proofEntry).map fun m =>
              if m.1 == "impl_modules" then (m.1, .arr [.str "A", .str "B", .str "A"]) else m))
          ⟨p ++ [.key "impl_modules", .index 2], .badValue⟩ &&
        refusedAs
          (entry
            ((entryMembers proofEntry).map fun m =>
              if m.1 == "proof_modules" then (m.1, .arr [.str "Impl.B", .str "Impl"]) else m))
          ⟨p, .inBothLists "Impl"⟩),
    ("manifest: keyPath quotes non-bare keys + renders indices", fun _ =>
      keyPath [.key "modules", .key "base64.encode", .key "impl_modules", .index 1] ==
          "modules.\"base64.encode\".impl_modules[1]" &&
        keyPath [.key "a-b_1"] == "a-b_1" &&
        keyPath [.key ""] == "\"\""),
    ("manifest: a Lake message's C1 + C0 controls render escaped (interface §1 line rule)", fun _ =>
      (ReadError.parse (.syntax 1 0 "bad \u0085\u009b\x1b token")).detail ==
        "syntax at 1:1: bad \\u0085\\u009B\\u001B token")]

/-- Through Lake's parser (IO). -/
def ioCases : List (String × IO Bool) :=
  [("manifest: printManifest reads back through Lake's parser", do
      match ← readManifest (printManifest sample) with
      | .ok m =>
        return m == sample
      | .error _ =>
        return false),
    ("manifest: Lake syntax + repeated keys refuse with a 1-based line; code schema", do
      let a ← readManifest "schema = \n".toUTF8
      let b ← readManifest "a = 1\na = 2\n".toUTF8
      return match a, b with
        | .error (.parse (.syntax 1 _ _)), .error (.parse (.syntax 2 _ _)) => true
        | _, _ => false),
    ("manifest: a BOM refuses before Lake runs", do
      return match ← readManifest (bytes [0xEF, 0xBB, 0xBF, 0x61]) with
        | .error (.text .bom) => true
        | _ => false)]

end Manifest

/-! ## U3 F: persistence through the shim (IO; residue `sys-shim`) -/

namespace Sys

open FvdepIO.Sys

/-- `f` on a fresh directory (removed after). -/
def withDir (f : Path → System.FilePath → IO Bool) : IO Bool := do
  let d ← IO.FS.createTempDir
  try
    match Path.ofString? d.toString with
    | some p =>
      f p d
    | none =>
      return false
  finally
    IO.FS.removeDirAll d

def nameOf! (s : String) :
    Name := match Name.ofString? s with
  | some n => n
  | none => ⟨"x", rfl⟩

def entries (d : System.FilePath) : IO (List String) := do
  return ((← d.readDir).map (·.fileName)).toList.mergeSort (· ≤ ·)

def ioCases : List (String × IO Bool) :=
  [("sys: replace writes an absent then a present target, readFile reads each back, no temp left",
      withDir fun dir d => do
        let name := nameOf! "fvdep.lock"
        let r1 ← replace dir name "one".toUTF8
        let b1 ← readFile dir name
        let r2 ← replace dir name "second".toUTF8
        let b2 ← readFile dir name
        let left ← entries d
        return r1 matches .ok () && r2 matches .ok () &&
            (match b1, b2 with
            | .ok (some x), .ok (some y) => x == "one".toUTF8 && y == "second".toUTF8
            | _, _ => false) &&
            left == ["fvdep.lock"]),
    ("sys: readFile: absent → none, empty file → empty bytes",
      withDir fun dir d => do
        let a ← readFile dir (nameOf! "absent")
        IO.FS.writeFile (d / "empty") ""
        let e ← readFile dir (nameOf! "empty")
        return a matches .ok none &&
            (match e with
            | .ok (some b) => b.isEmpty
            | _ => false)),
    ("sys: readFile cap: a file of `cap` bytes reads back; one byte more → read error tooLarge",
      withDir fun dir d => do
        IO.FS.writeFile (d / "f") "0123456789"
        let ok ← readFile dir (nameOf! "f") 10
        let over ← readFile dir (nameOf! "f") 9
        return (match ok with
            | .ok (some b) => b == "0123456789".toUTF8
            | _ => false) &&
            (match over with
            | .error e => e.op == .read && e.cause == .tooLarge && e.secondary.isEmpty
            | .ok _ => false)),
    ("sys: replace in a missing directory → create error ENOENT naming temp 0, nothing written",
      withDir fun _ d => do
        let some missing := Path.ofString? (d / "missing").toString | return false
        let r ← replace missing (nameOf! "f") "x".toUTF8
        let pid := (← IO.Process.getPID).toNat
        return (match r with
            | .error e =>
              e.op == .create && e.cause == .errno 2 && e.secondary.isEmpty && !e.durability &&
                e.path.toString == (d / "missing").toString ++ s!"/.f.tmp-{pid}-0"
            | .ok _ => false) &&
            (← entries d) == []),
    ("sys: replace over a non-empty directory → rename error naming the target, temp unlinked",
      withDir fun dir d => do
        IO.FS.createDirAll (d / "t" / "inner")
        let r ← replace dir (nameOf! "t") "x".toUTF8
        return (match r with
            | .error e =>
              e.op == .rename && e.path.toString == (d / "t").toString && e.secondary.isEmpty &&
                !e.durability
            | .ok _ => false) &&
            (← entries d) == ["t"]),
    ("sys: replace swaps a symlink at the target for a regular file; the link's file is kept",
      withDir fun dir d => do
        IO.FS.writeFile (d / "real") "old"
        let _ ← IO.Process.output { cmd := "ln", args := #["-s", "real", (d / "t").toString] }
        let r ← replace dir (nameOf! "t") "new".toUTF8
        let md ← (d / "t").symlinkMetadata
        return r matches .ok () && md.type == .file && (← IO.FS.readFile (d / "t")) == "new" &&
            (← IO.FS.readFile (d / "real")) == "old"),
    ("sys: a second writer lock on the same directory → busy, its act never runs; outer act runs",
      withDir fun dir d => do
        let ran ← IO.mkRef false
        let outer ←
          withWriterLock dir do
              let inner ← withWriterLock dir (ran.set true)
              return inner
        let again ← withWriterLock dir (pure 7)
        let lockFile ← IO.FS.readFile (d / ".fvdep-writer.lock")
        return (match outer with
            | .ok (.error e) =>
              e.op == .lock && e.cause == .busy &&
                e.path.toString == (d / ".fvdep-writer.lock").toString
            | _ => false) &&
            !(← ran.get) &&
            again matches .ok 7 &&
            lockFile == "" &&
            (← entries d) == [".fvdep-writer.lock"]),
    ("sys: an exception in the locked act propagates after the lock's close",
      withDir fun dir _ => do
        let r ← (withWriterLock dir (throw (IO.userError "boom") : IO Unit)).toBaseIO
        let again ← withWriterLock dir (pure 1)
        return (match r with
            | .error e => toString e == "boom"
            | .ok _ => false) &&
            again matches .ok 1),
    ("sys: Writer: create-exclusive, write, sync, close; closed → alreadyClosed; then EEXIST",
      withDir fun _ d => do
        let some p := Path.ofString? (d / "w").toString | return false
        match ← Writer.create p with
        | .error _ =>
          return false
        | .ok w =>
          let a ← w.write "abc".toUTF8
          let b ← w.sync
          let c ← w.close
          let e ← w.write "x".toUTF8
          let again ← Writer.create p
          return a matches .ok () && b matches .ok () && c matches .ok () &&
              (match e with
              | .error x => x.cause == .alreadyClosed && x.op == .write
              | _ => false) &&
              (match again with
              | .error x => x.op == .create && x.cause == .errno 17
              | _ => false) &&
              (← IO.FS.readFile (d / "w")) == "abc"),
    ("sys: Name refuses empty, `.`, `..`, `/`, NUL + the lock name; accepts a plain name", do
      return ["", ".", "..", "a/b", "/", "a\x00b", ".fvdep-writer.lock"].all
            (fun s => (Name.ofString? s).isNone) &&
          (Name.ofString? "fvdep.toml").isSome &&
          (Path.ofString? "a\x00b").isNone)]

end Sys

def main : IO UInt32 := do
  let seed : UInt64 ←
    do
      match (← IO.getEnv "FVDEP_TEST_SEED").bind String.toNat? with
      | some n =>
        pure n.toUInt64
      | none =>
        pure 0x5EEDF0DE00000001
  IO.println s!"seed {seed}"
  let generated := argLists seed 2000
  let results ←
    ([check "cli: --version prints exactly \"fvdep <version>\" + LF on stdout, rc 0" fun _ =>
                run ["--version"] == ⟨s!"fvdep {Fvdep.version}\n", "", 0⟩,
              check "cli: help + --help print usage on stdout, rc 0" fun _ =>
                run ["help"] == ⟨usage, "", 0⟩ && run ["--help"] == ⟨usage, "", 0⟩,
              check "cli: help <command> + <command> --help print usage on stdout, rc 0" fun _ =>
                run ["help", "help"] == ⟨usage, "", 0⟩ && run ["help", "--help"] == ⟨usage, "", 0⟩,
              check "cli: no argument → usage on stderr, rc 2" fun _ => run [] == ⟨"", usage, 2⟩,
              check "cli: unknown command, unknown option, extra argument → usage on stderr, rc 2"
                fun _ =>
                run ["frobnicate"] == ⟨"", usage, 2⟩ && run ["--frobnicate"] == ⟨"", usage, 2⟩ &&
                  run ["--version", "extra"] == ⟨"", usage, 2⟩ &&
                  run ["help", "help", "x"] == ⟨"", usage, 2⟩,
              check "cli: usage starts with the usage line + names every command and option"
                fun _ =>
                usage.startsWith "Usage: fvdep <command>" &&
                  ["help [<command>]", "--help", "--version"].all fun s =>
                    (usage.splitOn s).length > 1,
              check s!"cli: {generated.length} generated argument lists match the contract table"
                fun _ => generated.all fun args => run args == expected args,
              check "cli: generated lists reach every outcome class" fun _ =>
                [0, 2].all fun rc => generated.any fun args => (run args).exit == rc] ++
            (Core.cases ++ Json.cases ++ Doc.cases ++ Hash.cases ++ Manifest.cases).map fun c =>
              check c.1 c.2).mapM
        id
  let ioResults ← (Manifest.ioCases ++ Sys.ioCases).mapM fun c => checkIO c.1 c.2
  let results := results ++ ioResults
  let slowest := results.foldl (fun a r => if r.ms > a.ms then r else a) ⟨"none", true, 0⟩
  let failed := (results.filter (!·.ok)).length
  IO.println s!"slowest: {slowest.name} ({slowest.ms} ms)"
  IO.println s!"tests: {results.length - failed} passed, {failed} failed"
  return failed.toUInt32
