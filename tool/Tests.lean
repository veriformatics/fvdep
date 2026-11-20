import FvdepCore
import FvdepCore.Oracle
import FvdepIO.Library
import FvdepIO.Phase
import FvdepIO.Project
import FvdepIO.Sha256
import FvdepIO.Snapshot
import FvdepIO.Step
import FvdepIO.Toml
import FvdepIO.Toolchain

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
    "help ", "--", "-", "fvdep", "--version=1", "--Help", "x", "oracle"]

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
    else
      if [["oracle", "--help"], ["help", "oracle"]].contains args then
        ⟨FvdepCore.Oracle.Command.usage, "", 0⟩
      else
        if args.head? == some "oracle" then ⟨"", FvdepCore.Oracle.Command.usage, 2⟩
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

/-! Index regressions (contract U4 C6 + C9): the refusal the D5 walk over `indexTy` names. -/

namespace Index

open FvdepCore.Index

/-- `decodeIndex`'s rendered refusal of an index text whose one obligation holds `axioms` under
`status` (`accepted` when it decodes). -/
def refusal (axioms status : String) : String :=
  let text :=
    "{\"notices\":[],\"operations\":[{\"compat\":null,\"digest\":\"" ++
      String.ofList (List.replicate 64 'a') ++
      "\",\"id\":\"a.b\",\"obligations\":[{\"axioms\":" ++
      axioms ++
      ",\"name\":\"n\",\"status\":\"" ++
      status ++
      "\"}],\"version\":\"1.0.0\"}],\"removed\":[],\"schema\":1,\"toolchain\":\"t\"}\n"
  match decodeIndex text.toUTF8 with
  | .error e => e.render
  | .ok _ => "accepted"

def cases : List (String × (Unit → Bool)) :=
  [("index: proven + descending axioms → the descent first (C9: elements, order, then status)",
      fun _ =>
      refusal "[\"z\",\"a\"]" "proven" == "/operations/0/obligations/0/axioms/1 bad_value \"a\""),
    ("index: proven + ascending nonempty axioms → the status rule's array refusal", fun _ =>
      refusal "[\"a\"]" "proven" == "/operations/0/obligations/0/axioms bad_value [\"a\"]"),
    ("index: open + trusts name the descent too", fun _ =>
      refusal "[\"z\",\"a\"]" "trusts" == "/operations/0/obligations/0/axioms/1 bad_value \"a\"" &&
        refusal "[\"sorryAx\",\"a\"]" "open" ==
          "/operations/0/obligations/0/axioms/1 bad_value \"a\""),
    ("index: proven + equal adjacent axioms → the repeat (strictly ascending)", fun _ =>
      refusal "[\"a\",\"a\"]" "proven" == "/operations/0/obligations/0/axioms/1 bad_value \"a\""),
    ("index: proven + no axioms decodes", fun _ => refusal "[]" "proven" == "accepted")]

end Index

/-! Compiled-code smoke for registry reading (contract U4 C2): the proofs cover the definitions,
these run the compiled C — a 10^6-element list (the loop: no stack per element), Lean's `have`
chunks of a long list literal, root-constant + entry-reference reads, refusals + their constant. -/

namespace Registry

open Lean FvdepCore.Index.Registry

def strE (s : String) : Expr := .lit (.strVal s)

def consE (T h t : Expr) : Expr := .app (.app (.app (.const ``List.cons [.zero]) T) h) t

def nilE (T : Expr) : Expr := .app (.const ``List.nil [.zero]) T

def strT : Expr := .const ``String []

def nameT : Expr := .const ``Lean.Name []

/-- A cons spine of `n` string literals, built in a loop. -/
def spineOf (n : Nat) : Expr := n.fold (fun _ _ acc => consE strT (strE "x") acc) (nilE strT)

/-- `Name.mkStrN s₁ … sₙ` (n ≤ 8), as Lean elaborates a double-backtick name. -/
def mkStrE (parts : List String) : Expr :=
  parts.foldl (fun acc s => .app acc (strE s))
    (.const (mkStrN.getD (parts.length - 1) .anonymous) [])

def moduleT : Expr := .const `Fvdep.Registry.Types.V1.Module []

def moduleMk (id ver : String) : Expr :=
  [strE id, strE ver, mkStrE ["Fvdep", "Base64", "Encode", "V1_0_0", "encode"],
        consE nameT (mkStrE ["Fvdep", "Base64", "Encode", "V1_0_0", "bits"]) (nilE nameT),
        .app (.const ``Option.none [.zero]) nameT, .app (.const ``Option.none [.zero]) strT].foldl
    .app (.const `Fvdep.Registry.Types.V1.Module.mk [])

def appendE (T xs ys : Expr) : Expr :=
  let l := .app (.const ``List [.zero]) T
  .app
    (.app
      (.app (.app (.app (.app (.const ``HAppend.hAppend [.zero, .zero, .zero]) l) l) l)
        (.app (.app (.const ``instHAppendOfAppend [.zero]) l)
          (.app (.const ``List.instAppend [.zero]) T)))
      xs)
    ys

def entryName : Name := `Fvdep.Registry.Base64.Encode.V1_0_0.entry

def decl (n m : Name) (v : Expr) : Decl :=
  ⟨n, m, .defn, some v, .sort .zero, .safe, false, false, false⟩

/-- A registry: `modules` = a root-module chunk constant `++ []`; the chunk = one entry
reference. -/
def facts (modules notices : Expr) (extra : List Decl := []) : Facts :=
  { decls :=
      [decl entryName `Fvdep.Registry.Base64.Encode.V1_0_0 (moduleMk "base64.encode" "1.0.0"),
          decl `Fvdep.Registry.part `Fvdep.Registry
            (consE moduleT (.const entryName []) (nilE moduleT)),
          decl `Fvdep.Registry.modules `Fvdep.Registry modules,
          decl `Fvdep.Registry.profiles `Fvdep.Registry (nilE (.const `P [])),
          decl `Fvdep.Registry.notices `Fvdep.Registry.Notices notices,
          decl `Fvdep.Registry.removed `Fvdep.Registry.Removed (nilE (.const `R []))] ++
        extra
    modules := []
    entryFiles := []
    abiType := []
    specDefeq := [] }

def okModules : Expr := appendE moduleT (.const `Fvdep.Registry.part []) (nilE moduleT)

def okNotices : Expr := nilE (.const `N [])

def refused (F : Facts) :
    Option Name := match readRaw F with
  | .error n => some n
  | .ok _ => none

def cases : List (String × (Unit → Bool)) :=
  [("registry: a 10^6-element cons spine decodes in a loop", fun _ =>
      match decode ⟨[], [], [], [], []⟩ (.list .str) (spineOf 1000000) [] [`t] with
      | .ok v => v.elems.length == 1000000
      | .error _ => false),
    ("registry: Lean's `have` chunks of a long list literal (tail = a let-bound chunk)", fun _ =>
      let chunk := consE strT (strE "d") (consE strT (strE "e") (nilE strT))
      let body := consE strT (strE "a") (consE strT (strE "b") (.bvar 0))
      match decode ⟨[], [], [], [], []⟩ (.list .str) (.letE `y strT chunk body true) [] [`t] with
      | .ok v => v.elems.map Val.strD == ["a", "b", "d", "e"]
      | .error _ => false),
    ("registry: root-module chunk `++` + an entry reference → the entry + its module", fun _ =>
      match (readRaw (facts okModules okNotices)).map Lists.ofRaw with
      | .ok r =>
        r.entries.length == 1 && r.profiles == 0 &&
          r.entries.all fun e =>
            e.module == `Fvdep.Registry.Base64.Encode.V1_0_0 && e.id == "base64.encode" &&
              e.version == "1.0.0" &&
              e.spec == `Fvdep.Base64.Encode.V1_0_0.encode &&
              e.obligations == [`Fvdep.Base64.Encode.V1_0_0.bits] &&
              e.abi.isNone &&
              e.compat.isNone
      | .error _ => false),
    ("registry: an inline record in `modules` → unreadable, naming `modules`", fun _ =>
      refused (facts (consE moduleT (moduleMk "base64.encode" "1.0.0") (nilE moduleT)) okNotices) ==
        some `Fvdep.Registry.modules),
    ("registry: a helper constant outside the root module → unreadable, naming the list", fun _ =>
      refused
          (facts okModules (.const `Fvdep.Registry.helper [])
            [decl `Fvdep.Registry.helper `Fvdep.Registry.Notices okNotices]) ==
        some `Fvdep.Registry.notices),
    ("registry: read order — `modules` before `notices`", fun _ =>
      refused (facts (strE "x") (strE "y")) == some `Fvdep.Registry.modules),
    ("registry: name literals (mkStr1, mkStr5, a 9-component `Name.str` chain); `Name.num` refused",
      fun _ =>
      let nine :=
        ["A", "B", "C", "D", "E", "F", "G", "H", "I"].foldl
          (fun acc s => .app (.app (.const ``Name.str []) acc) (strE s))
          (.const ``Name.anonymous [])
      nameLit? (mkStrE ["Nat"]) == some `Nat &&
        nameLit? (mkStrE ["Fvdep", "Base64", "Encode", "V1_0_0", "encode"]) ==
          some `Fvdep.Base64.Encode.V1_0_0.encode &&
        nameLit? nine == some `A.B.C.D.E.F.G.H.I &&
        nameLit?
            (.app (.app (.const ``Name.num []) (.const ``Name.anonymous [])) (.lit (.natVal 1))) ==
          none &&
        nameLit? (.app (.const ``Name.mkStr2 []) (strE "a")) == none &&
        nameLit? (.app (.const `Foo []) (strE "a")) == none),
    ("registry: a certificate list literal decodes back to the values written", fun _ =>
      let n (r : String) (repl : Val) : Val :=
        .app
          (.app
            (.app (.app (.const `Fvdep.Registry.Types.V1.Notice.mk) (.str "a.b")) (.str "1.0.0"))
            (.str r))
          repl
      let n₁ := n "r1" (.some (.str "1.0.1"))
      let n₂ := n "r2" .none
      match
        decode ⟨[], [], [], [], []⟩ (.list noticeForm) (listLiteral noticeForm [n₁, n₂]) []
          [`t] with
      | .ok v => v == .cons n₁ (.cons n₂ .nil)
      | .error _ => false),
    ("registry: the certificate's lists (`modules` records without entry annotations, " ++
        "`profiles` while empty) decode back from their literals",
      fun _ =>
      let F := facts okModules okNotices
      match readRaw F with
      | .ok r =>
        let cs := certificate r
        cs.map (·.1) == [modulesName, profilesName, noticesName, removedName] &&
          cs.all fun x =>
            (match decode F (.list x.2.1) (listLiteral x.2.1 x.2.2) [] [x.1] with
              | .ok v => v.elems == x.2.2
              | .error _ => false) &&
              x.2.2.all fun v =>
                match v with
                | .entry _ _ => false
                | _ => true
      | .error _ => false),
    ("registry: a nonempty `profiles` is not certified", fun _ =>
      let F := facts okModules okNotices
      let ps := consE (.const `P []) (strE "p") (nilE (.const `P []))
      let F' :=
        { F with
          decls :=
            F.decls.map fun d => if d.name == profilesName then { d with value := some ps } else d }
      match readRaw F' with
      | .ok r =>
        r.profiles.length == 1 &&
          (certificate r).map (·.1) == [modulesName, noticesName, removedName]
      | .error _ => false)]

end Registry

/-! Compiled-code smoke for the entry rules (contract U4 C3, C4, C9): the proofs tie `validate` to
the rows written apart; these pin the rows against C9's text — a valid one-entry registry passes,
each plant refuses with its first failing row (flag-major order, then the least carrier; Lean's own
vs a hand-written `_unsafe_rec`; the load refusal before the entry rules). -/

namespace Rules

open Lean FvdepCore.Index.Registry FvdepCore.Index.Rules

def listT (t : Name) : Expr := .app (.const ``List [.zero]) (.const t [])

def specM : Name := `Fvdep.Base64.Encode.V1_0_0

def entryM : Name := `Fvdep.Registry.Base64.Encode.V1_0_0

def typesM : Name := `Fvdep.Registry.Types.V1

/-- A safe definition `specM.<s>`. -/
def defn (s : String) (v : Expr := .lit (.natVal 0)) (t : Expr := .sort 1) : Decl :=
  { name := .str specM s
    module := specM
    kind := .defn
    value := some v
    type := t
    safety := .safe
    implementedBy := false
    isExtern := false
    isNoncomputable := false }

/-- The spec `encode` (its value names each `reached` declaration) + the obligation `bits`, the
three modules of the entry's closure + its file. -/
def facts (reached : List Decl) (other : List Decl := []) : Facts :=
  { decls :=
      [defn "encode" (reached.foldl (fun acc d => .app acc (.const d.name [])) (.lit (.natVal 0)))
            (.forallE `x (listT ``UInt8) (listT ``Char) .default),
          defn "bits" (.const ``True []) (.sort .zero)] ++
        reached ++
        other
    modules :=
      [⟨entryM, [specM, typesM], some .empty⟩, ⟨specM, [`Init.Data.List.Basic], some .empty⟩,
        ⟨typesM, [], some .empty⟩]
    entryFiles := ["Fvdep/Registry/Base64/Encode/V1_0_0.lean"]
    abiType := []
    specDefeq := [] }

def entry : Entry :=
  { module := entryM
    id := "base64.encode"
    version := "1.0.0"
    spec := .str specM "encode"
    obligations := [.str specM "bits"]
    abi := none
    compat := none }

def lists (es : List Entry) : Lists := ⟨es, 0, [], []⟩

def subj : String := "base64.encode@1.0.0"

def withSpecModule (F : Facts) (x : ModFacts) : Facts :=
  { F with modules := F.modules.map fun y => if y.name == specM then x else y }

def cases : List (String × (Unit → Bool)) :=
  [("rules: a valid one-entry registry passes", fun _ =>
      validate (facts []) (lists [entry]) == none),
    ("rules: an entry listed twice → the second one: `listed twice` (C9 text)", fun _ =>
      (validate (facts []) (lists [entry, entry])).map render ==
        some "Library error: base64.encode@1.0.0: listed twice."),
    ("rules: flags — the first listed flag a checked constant carries, then its least carrier",
      fun _ =>
      let a := { defn "a" with isNoncomputable := true }
      let b := { defn "b" with safety := .unsafe }
      let c := { defn "c" with safety := .unsafe }
      validate (facts [c, a, b]) (lists [entry]) == some (subj, .flagged (.str specM "b") .unsafe)),
    ("rules: an opaque constant + Lean's own `_unsafe_rec` (partial safety) → `partial`", fun _ =>
      let p :=
        { defn "p" with
          kind := .opaque, value := none }
      let rec' :=
        { defn "p" with
          name := .str (.str specM "p") "_unsafe_rec", safety := .partial }
      (validate (facts [p] [rec']) (lists [entry])).map render ==
        some "Library error: base64.encode@1.0.0: Fvdep.Base64.Encode.V1_0_0.p is partial."),
    ("rules: a hand-written `_unsafe_rec` (Lean compiles callers from it) → `implemented_by`",
      fun _ =>
      let q := defn "q"
      let rec' := { defn "q" with name := .str (.str specM "q") "_unsafe_rec" }
      validate (facts [q] [rec']) (lists [entry]) ==
        some (subj, .flagged (.str specM "q") .implementedBy)),
    ("rules: a listed entry's file missing from the entry files → load refusal (C9 text)", fun _ =>
      (validate { facts [] with entryFiles := [] } (lists [entry])).map render ==
        some "Could not load the built library: no entry file observed for base64.encode@1.0.0."),
    ("rules: a closure module without a regular file → C4 (C9 text)", fun _ =>
      (validate (withSpecModule (facts []) ⟨specM, [], none⟩) (lists [entry])).map render ==
        some
          ("Library error: base64.encode@1.0.0: the closure module Fvdep.Base64.Encode.V1_0_0 " ++
            "is not a regular file at Fvdep/Base64/Encode/V1_0_0.lean.")),
    ("rules: imports outside Init, Std + the library → the least imported module", fun _ =>
      let F :=
        withSpecModule (facts []) ⟨specM, [`Lean.Expr, `FvdepProofs.X, `Std.Data], some .empty⟩
      validate F (lists [entry]) == some (subj, .closureImports `FvdepProofs.X)),
    ("rules: unlisted entry files → the first in path byte order, its id@version from the path",
      fun _ =>
      let p := "Fvdep/Registry/Base64/DecodeUrl/V1_0_0.lean"
      let F := facts []
      validate
          { F with entryFiles := F.entryFiles ++ ["Fvdep/Registry/Semver/Parse/V1_0_0.lean", p] }
          (lists [entry]) ==
        some ("base64.decode_url@1.0.0", .unlisted p)),
    ("rules: V7 holds — an unversioned library module + `V01_0_0` (not canonical) → the least",
      fun _ =>
      let F := facts []
      let M' : ModFacts :=
        ⟨entryM, [specM, typesM, `Fvdep.Registry, `Fvdep.Base64.Rfc4648.V01_0_0], some .empty⟩
      validate { F with modules := F.modules.map fun y => if y.name == entryM then M' else y }
          (lists [entry]) ==
        some (subj, .closureHolds `Fvdep.Base64.Rfc4648.V01_0_0)),
    ("rules: V6 — compat naming a later listed version → `not an earlier listed version`", fun _ =>
      let later :=
        { entry with
          version := "1.1.0", module := `Fvdep.Registry.Base64.Encode.V1_1_0 }
      let F := facts []
      validate { F with entryFiles := F.entryFiles ++ ["Fvdep/Registry/Base64/Encode/V1_1_0.lean"] }
          (lists [{ entry with compat := some "1.1.0" }, later]) ==
        some (subj, .compatNotEarlier "1.1.0")),
    ("rules: a notice naming nothing → V8", fun _ =>
      validate (facts [])
          { lists [entry] with notices := [⟨"base64.encode", "9.9.9", "r", none⟩] } ==
        some ("base64.encode@9.9.9", .noticeNamesNothing)),
    ("rules: V4 — an obligation declared in S outside S's namespace → not a Prop definition in S",
      fun _ =>
      let p :=
        { defn "x" with
          name := `Foo.p, type := .sort .zero }
      validate (facts [] [p]) (lists [{ entry with obligations := [.str specM "bits", `Foo.p] }]) ==
        some (subj, .obligationNotProp `Foo.p specM)),
    ("rules: a nonempty `profiles` → V10, the last row", fun _ =>
      validate (facts []) { lists [entry] with profiles := 1 } ==
        some ("Fvdep.Registry.profiles", .profiles))]

end Rules

/-! Compiled-code smoke for statuses + warnings (contract U4 C5, C9) and the digest's input files
(C4): the proofs cover the definitions (`StatusExact`, `closureFiles`); these cases pin C9's texts +
orders through the compiled code. -/

namespace Statuses

open Lean FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses

def nameT : Expr := .const ``Lean.Name []

def pairT : Expr := .app (.app (.const ``Prod [.zero, .zero]) nameT) nameT

/-- A proof registry literal `Proofs.mk [(o, t), …] compat` (C2's forms). -/
def proofsLit (obls : List (Name × Name)) (compat : Option Name := none) : Expr :=
  let pairE (x : Name × Name) : Expr :=
    .app (.app (.app (.app (.const ``Prod.mk [.zero, .zero]) nameT) nameT) (nameExpr x.1))
      (nameExpr x.2)
  let opt : Expr :=
    match compat with
    | none => .app (.const ``Option.none [.zero]) nameT
    | some t => .app (.app (.const ``Option.some [.zero]) nameT) (nameExpr t)
  .app
    (.app (.const ``Fvdep.Registry.Types.V1.Proofs.mk [])
      (obls.foldr (fun x acc => Registry.consE pairT (pairE x) acc) (Registry.nilE pairT)))
    opt

def proofsM : Name := `FvdepProofs.Base64.Encode.V1_0_0

def bits : Name := .str Rules.specM "bits"

/-- The theorem `FvdepProofs.Base64.Encode.V1_0_0.<s>` of type `ty`. -/
def thm (s : String) (ty : Expr := .const bits []) (m : Name := proofsM) : Decl :=
  { Rules.defn s with
    name := .str proofsM s
    module := m
    kind := .thm
    value := none
    type := ty }

/-- A proof registry constant `c` (`docs/library.md` Registry: entry module
`Fvdep.Registry.<Dep>.<Op>.V…` → `FvdepProofs.Registry.<Dep>.<Op>.V….proofs`), spelled apart from
the shipped `proofsName`. -/
def registry (c : Name) (v : Expr) : Decl :=
  { Rules.defn "proofs" v with
    name := c
    module := c.getPrefix }

def t : Name := .str proofsM "bits_eq"

/-- The one-entry library: `bits` mapped to `t`, + `extra` declarations (`reg := false` drops the
proof registry). -/
def lib (reg : Option Expr := some (proofsLit [(bits, t)])) (extra : List Decl := [thm "bits_eq"]) :
    Facts :=
  Rules.facts []
    ((reg.map (registry `FvdepProofs.Registry.Base64.Encode.V1_0_0.proofs)).toList ++ extra)

def statusOf (F : Facts) (ax : List (Name × List Name)) (es : List Entry := [Rules.entry]) :
    Option EntryStatus :=
  match statuses F ax (Rules.lists es) with
  | .ok xs => xs.getLast?.map (·.2)
  | .error _ => none

def warnings (F : Facts) (ax : List (Name × List Name)) (es : List Entry := [Rules.entry]) :
    List String :=
  ((statusOf F ax es).map fun s => s.warnings.map Warning.render).getD ["(refused)"]

def opened (why : String) : List String :=
  [s!"Warning: base64.encode@1.0.0: obligation {bits} counts as open: {why}."]

/-- The version-1.1.0 entry declaring compat with 1.0.0, its spec + the compat theorem `c` of type
`ty` (`none` = no compat theorem mapped). -/
def newEntry : Entry :=
  { Rules.entry with
    version := "1.1.0"
    module := `Fvdep.Registry.Base64.Encode.V1_1_0
    spec := `Fvdep.Base64.Encode.V1_1_0.encode
    obligations := []
    compat := some "1.0.0" }

def specT : Expr := .forallE `x (Rules.listT ``UInt8) (Rules.listT ``Char) .default

def eqNewOld (new old : Name) : Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) specT) (.const new [])) (.const old [])

def compatLib (c : Option Name) (ty : Expr) : Facts :=
  let F := lib
  { F with
    decls :=
      F.decls ++
        [{ Rules.defn "encode" with
            name := newEntry.spec
            module := `Fvdep.Base64.Encode.V1_1_0
            type := specT },
          registry `FvdepProofs.Registry.Base64.Encode.V1_1_0.proofs (proofsLit [] c),
          thm "compat" ty] }

def cases : List (String × (Unit → Bool)) :=
  [("statuses: the standard axioms alone → proven, no axioms, no warning", fun _ =>
      statusOf lib [(t, [``propext, ``Quot.sound])] ==
        some { obligations := [(bits, .proven, [])], compat := none, warnings := [] }),
    ("statuses: other axioms → trusts, printed names strictly ascending, each once", fun _ =>
      (statusOf lib [(t, [`Z.ax, ``propext, `A.ax, `Z.ax])]).map (·.obligations) ==
        some [(bits, .trusts, ["A.ax", "Z.ax"])]),
    ("statuses: an axiom list observed twice for a theorem → the first one counts", fun _ =>
      (statusOf lib [(t, [``propext]), (t, [``sorryAx])]).map (·.obligations) ==
        some [(bits, .proven, [])]),
    ("statuses: `sorryAx` among the axioms → open with its axioms, no warning", fun _ =>
      statusOf lib [(t, [``sorryAx, `B.ax, ``Classical.choice])] ==
        some
          { obligations := [(bits, .«open», ["B.ax", "sorryAx"])], compat := none,
            warnings := [] }),
    ("statuses: no proof registry → open, no axioms + C9's warning", fun _ =>
      (statusOf (lib (reg := none)) []).map (·.obligations) == some [(bits, .«open», [])] &&
        warnings (lib (reg := none)) [] == opened "no proof registry"),
    ("statuses: a registry outside C2's forms → `its proof registry cannot be read`", fun _ =>
      warnings (lib (reg := some (.lit (.natVal 0)))) [] ==
        opened "its proof registry cannot be read"),
    ("statuses: no theorem mapped → `no theorem is mapped`", fun _ =>
      warnings (lib (reg := some (proofsLit []))) [] == opened "no theorem is mapped"),
    ("statuses: two theorems mapped → `two theorems are mapped`", fun _ =>
      warnings (lib (reg := some (proofsLit [(bits, t), (bits, .str proofsM "other")]))) [] ==
        opened "two theorems are mapped"),
    ("statuses: a mapped definition → `<t> is not a theorem`", fun _ =>
      warnings (lib (extra := [{ thm "bits_eq" with kind := .defn }])) [(t, [])] ==
        opened s!"{t} is not a theorem"),
    ("statuses: a theorem outside FvdepProofs or absent → `<t> is outside FvdepProofs`", fun _ =>
      warnings (lib (extra := [thm "bits_eq" (m := `Fvdep.X)])) [(t, [])] ==
          opened s!"{t} is outside FvdepProofs" &&
        warnings (lib (extra := [])) [(t, [])] == opened s!"{t} is outside FvdepProofs"),
    ("statuses: a theorem of another statement → `<t> proves another statement`", fun _ =>
      warnings (lib (extra := [thm "bits_eq" (.const `Other [])])) [(t, [])] ==
        opened s!"{t} proves another statement"),
    ("statuses: a counted theorem without an observed axiom list → load refusal (C9 text)", fun _ =>
      match statuses lib [] (Rules.lists [Rules.entry]) with
      | .error f =>
        render f ==
          s!"Could not load the built library: no axiom list of {t} observed for " ++
            "base64.encode@1.0.0."
      | .ok _ => false),
    ("statuses: the compat edge `@Eq T new old` (T = the new spec's type) → its status + version",
      fun _ =>
      let c := Name.str proofsM "compat"
      statusOf (compatLib (some c) (eqNewOld newEntry.spec Rules.entry.spec))
          [(t, []), (c, [``propext, `K.ax])] [Rules.entry, newEntry] ==
        some { obligations := [], compat := some ("1.0.0", .trusts, ["K.ax"]), warnings := [] }),
    ("statuses: a compat theorem of another statement → compat open + C9's warning", fun _ =>
      let c := Name.str proofsM "compat"
      (warnings (compatLib (some c) (eqNewOld newEntry.spec newEntry.spec)) [(t, []), (c, [])]
          [Rules.entry, newEntry]) ==
        [s!"Warning: base64.encode@1.1.0: compat counts as open: {c} proves another statement."]),
    ("statuses: a mapped compat theorem with no compat declared → `ignored` (C9 text)", fun _ =>
      let c := Name.str proofsM "compat"
      warnings (lib (reg := some (proofsLit [(bits, t)] (some c)))) [(t, [])] ==
        [s!"Warning: base64.encode@1.0.0: the compat theorem {c} is ignored: " ++
            "no compat is declared."]),
    ("statuses: an obligation's warning before the ignored compat theorem's (C9's order)", fun _ =>
      let c := Name.str proofsM "compat"
      warnings (lib (reg := some (proofsLit [] (some c)))) [] ==
        opened "no theorem is mapped" ++
          [s!"Warning: base64.encode@1.0.0: the compat theorem {c} is ignored: " ++
              "no compat is declared."]),
    ("statuses: warnings in C9's order — obligations in entry order, then the compat edge", fun _ =>
      let e := { newEntry with obligations := [.str Rules.specM "z", .str Rules.specM "a"] }
      warnings (compatLib none (.sort .zero)) [(t, [])] [Rules.entry, e] ==
        [s!"Warning: base64.encode@1.1.0: obligation {Rules.specM}.z counts as open: " ++
            "no theorem is mapped.",
          s!"Warning: base64.encode@1.1.0: obligation {Rules.specM}.a counts as open: " ++
            "no theorem is mapped.",
          "Warning: base64.encode@1.1.0: compat counts as open: no theorem is mapped."]),
    ("closureFiles: each closure module with a file → (its path, its bytes), none without", fun _ =>
      let paths (F : Facts) := (closureFiles F Rules.entryM).map (·.1)
      let all :=
        ["Fvdep/Registry/Base64/Encode/V1_0_0.lean", "Fvdep/Base64/Encode/V1_0_0.lean",
          "Fvdep/Registry/Types/V1.lean"]
      let F := Rules.withSpecModule (Rules.facts []) ⟨Rules.specM, [], none⟩
      (paths (Rules.facts [])).length == 3 && all.all (paths (Rules.facts [])).contains &&
        paths F == (paths (Rules.facts [])).filter (· != "Fvdep/Base64/Encode/V1_0_0.lean"))]

end Statuses

/-! Compiled-code smoke for the index value (contract U4 C4, C6, C9): the proof covers the
definitions (`AssembleExact`); these cases pin the value's layout, C6's order, the warnings' order,
the toolchain trim + the schema walk's acceptance through the compiled code. -/

namespace Assemble

open Lean FvdepCore.Json FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses
open FvdepCore.Index.Assemble

/-- A digest stand-in (the claim holds for every `h`): the frame's size. -/
def hSize (b : ByteArray) : String := toString b.size

/-- One hash path: `fvdep index`'s entry digest = H3's `digest` under tag `entry`. -/
example (F : Facts) (M : Name) :
    FvdepCore.Cli.sha (entryFrame F M) = FvdepIO.Hash.digest .entry (closureFiles F M) := rfl

def tc : String := "leanprover/lean4:v4.35.0"

def run (F : Facts) (ax : List (Name × List Name)) (l : Lists) (raw : String := tc ++ "\n") :
    Option (Value × List Warning) :=
  match assemble F ax l raw hSize with
  | .ok x => some x
  | .error _ => none

/-- An entry of `id`@`version` (no proof registry: open + a warning). -/
def other (id version : String) : Entry :=
  { Rules.entry with
    id := id
    version := version
    module :=
      .str `Fvdep.Registry.X
        (String.ofList (version.toList.map fun c => if c = '.' then '_' else c)) }

/-- The operations' (id, version) in a value. -/
def opKeys (v : Value) : List (String × String) :=
  match FvdepCore.Doc.valueAt ["operations"] v with
  | some (.arr xs) =>
    xs.filterMap fun x =>
      (FvdepCore.Doc.strAt ["id"] x).bind fun i => (FvdepCore.Doc.strAt ["version"] x).map (i, ·)
  | _ => []

def toolchainOf (raw : String) : Option String :=
  (run Statuses.lib [(Statuses.t, [])] (Rules.lists [Rules.entry]) raw).bind fun x =>
    FvdepCore.Doc.strAt ["toolchain"] x.1

def cases : List (String × (Unit → Bool)) :=
  [("assemble: one entry → the C6 value (registry strings, statuses, digest, toolchain)", fun _ =>
      let F := Statuses.lib
      let digest :=
        toString (FvdepCore.Hash.frame "fvdep/entry/1" (closureFiles F Rules.entryM)).size
      run F [(Statuses.t, [])] (Rules.lists [Rules.entry]) ==
        some
          (.obj
              [("notices", .arr []),
                ("operations",
                  .arr
                    [.obj
                        [("compat", .null), ("digest", .str digest), ("id", .str "base64.encode"),
                          ("obligations",
                            .arr
                              [.obj
                                  [("axioms", .arr []), ("name", .str "bits"),
                                    ("status", .str "proven")]]),
                          ("version", .str "1.0.0")]]),
                ("removed", .arr []), ("schema", .int 1), ("toolchain", .str tc)],
            [])),
    ("assemble: operations in C6's order — id bytes, then the version numerically", fun _ =>
      let es :=
        [other "semver.parse" "1.0.0", other "base64.encode" "1.10.0",
          other "base64.encode" "2.0.0", other "base64.encode" "1.9.0"]
      ((run (Rules.facts []) [] (Rules.lists es)).map fun x => opKeys x.1) ==
        some
          [("base64.encode", "1.9.0"), ("base64.encode", "1.10.0"), ("base64.encode", "2.0.0"),
            ("semver.parse", "1.0.0")]),
    ("assemble: warnings in `modules` order, not the operations' order", fun _ =>
      let es := [other "semver.parse" "1.0.0", other "base64.encode" "1.0.0"]
      ((run (Rules.facts []) [] (Rules.lists es)).map fun x => x.2.map Warning.render) ==
        some
          [s!"Warning: semver.parse@1.0.0: obligation {Statuses.bits} counts as open: " ++
              "no proof registry.",
            s!"Warning: base64.encode@1.0.0: obligation {Statuses.bits} counts as open: " ++
              "no proof registry."]),
    ("assemble: the toolchain = the `lean-toolchain` text without surrounding whitespace", fun _ =>
      toolchainOf (" \t" ++ tc ++ " \r\n") == some tc && toolchainOf " \n\t" == some "" &&
        toolchainOf ("a b") == some "a b"),
    ("assemble: notices + removed records in registry order, from the registry strings", fun _ =>
      let l :=
        { Rules.lists
            [Rules.entry] with
          notices := [⟨"base64.encode", "1.0.0", "r2", some "2.0.0"⟩, ⟨"x.y", "0.1.0", "r1", none⟩]
          removed := [⟨"x.y", "0.1.0", .profile, "d", "lean", "c"⟩] }
      match run Statuses.lib [(Statuses.t, [])] l with
      | some (v, _) =>
        FvdepCore.Doc.valueAt ["notices"] v ==
            some
              (.arr
                [.obj
                    [("id", .str "base64.encode"), ("reason", .str "r2"),
                      ("replacement", .str "2.0.0"), ("version", .str "1.0.0")],
                  .obj
                    [("id", .str "x.y"), ("reason", .str "r1"), ("replacement", .null),
                      ("version", .str "0.1.0")]]) &&
          FvdepCore.Doc.valueAt ["removed"] v ==
            some
              (.arr
                [.obj
                    [("digest", .str "d"), ("id", .str "x.y"), ("kind", .str "profile"),
                      ("last_commit", .str "c"), ("toolchain", .str "lean"),
                      ("version", .str "0.1.0")]])
      | none => false),
    ("assemble: a compat edge + an obligation's axioms in the operations' values", fun _ =>
      let c := Name.str Statuses.proofsM "compat"
      let F :=
        Statuses.compatLib (some c) (Statuses.eqNewOld Statuses.newEntry.spec Rules.entry.spec)
      match
        run F [(Statuses.t, [`Z.ax]), (c, [`K.ax])]
          (Rules.lists [Rules.entry, Statuses.newEntry]) with
      | some (v, _) =>
        match FvdepCore.Doc.valueAt ["operations"] v with
        | some (.arr [o₁, o₂]) =>
          FvdepCore.Doc.valueAt ["obligations"] o₁ ==
              some
                (.arr
                  [.obj
                      [("axioms", .arr [.str "Z.ax"]), ("name", .str "bits"),
                        ("status", .str "trusts")]]) &&
            FvdepCore.Doc.valueAt ["compat"] o₂ ==
              some
                (.obj
                  [("axioms", .arr [.str "K.ax"]), ("status", .str "trusts"),
                    ("version", .str "1.0.0")])
        | _ => false
      | none => false),
    ("assemble: a theorem without an observed axiom list → the load refusal passes through",
      fun _ =>
      match assemble Statuses.lib [] (Rules.lists [Rules.entry]) tc hSize with
      | .error f =>
        render f ==
          s!"Could not load the built library: no axiom list of {Statuses.t} observed for " ++
            "base64.encode@1.0.0."
      | .ok _ => false),
    ("assemble: the value passes C6's schema walk + encodes, decoding back", fun _ =>
      let hex (_ : ByteArray) : String := String.ofList (List.replicate 64 'a')
      match assemble Statuses.lib [(Statuses.t, [])] (Rules.lists [Rules.entry]) tc hex with
      | .ok (v, _) =>
        match FvdepCore.Index.IndexFile.ofJson v with
        | .ok i =>
          match FvdepCore.Index.encodeIndex i with
          | .ok b =>
            match FvdepCore.Index.decodeIndex b with
            | .ok i' => i' == i && i.operations.length == 1
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | .error _ => false),
    ("entryFrame = the H3 `fvdep/entry/1` frame over `closureFiles`", fun _ =>
      let F := Rules.facts []
      (entryFrame F Rules.entryM).data ==
        (FvdepCore.Hash.frame "fvdep/entry/1" (closureFiles F Rules.entryM)).data)]

end Assemble

/-! Compiled-code smoke for the history gate (contract U4 C7 + C9): the proof covers the definition
(`HistoryExact`); these cases pin C9's texts, its order + C7's witness rule through the compiled
code. -/

namespace History

open FvdepCore.Ids FvdepCore.Index FvdepCore.Index.History

def sha (c : Char) : String := String.ofList (List.replicate 40 c)

def commitOf (c : Char) : Commit := (Commit.parse (sha c)).getD Doc.cm

def tcA : String := "leanprover/lean4:v4.35.0"

def tcB : String := "leanprover/lean4:v9.9.9"

def op (digest : Char := '1') : Operation :=
  ⟨Doc.mid "base64.encode", Doc.ver, Doc.d64 digest, [], none⟩

def rec' (last : Char) (toolchain : String := tcA) (digest : Char := '1') : Removed :=
  ⟨Doc.mid "base64.encode", Doc.ver, Doc.d64 digest, commitOf last, toolchain⟩

def notice (reason : String := "r") : Notice := ⟨Doc.mid "base64.encode", Doc.ver, reason, none⟩

def idx (ops : List Operation) (toolchain : String := tcA) (removed : List Removed := [])
    (notices : List Notice := []) : IndexFile := ⟨toolchain, ops, notices, removed⟩

def base (c : Char) (i : IndexFile) : Baseline := ⟨sha c, some (.ok i)⟩

def lines (w : Option IndexFile) (head : Baseline) (parents : List Baseline := []) : List String :=
  (history (.ok w) head parents).map Line.render

def subj : String := "base64.encode@1.0.0"

def cases : List (String × (Unit → Bool)) :=
  [("history: an unchanged index → no line", fun _ =>
      lines (some (idx [op])) (base 'b' (idx [op])) [base 'c' (idx [op])] == []),
    ("history: a changed digest → one line per baseline, HEAD first", fun _ =>
      lines (some (idx [op '3'])) (base 'b' (idx [op])) [base 'c' (idx [op])] ==
        [s!"history: {sha 'b'}: {subj} changed its digest",
          s!"history: {sha 'c'}: {subj} changed its digest"]),
    ("history: a vanished operation; an absent working index = an empty one", fun _ =>
      lines (some (idx [])) (base 'b' (idx [op])) == [s!"history: {sha 'b'}: {subj} vanished"] &&
        lines none (base 'b' (idx [op])) == [s!"history: {sha 'b'}: {subj} vanished"]),
    ("history: a removal record with another digest → changed its digest, checked first", fun _ =>
      lines (some (idx [] tcA [rec' 'b' tcA '3'] [notice])) (base 'b' (idx [op])) ==
        [s!"history: {sha 'b'}: {subj} changed its digest"]),
    ("history: a removal without a toolchain change", fun _ =>
      lines (some (idx [] tcA [rec' 'b'] [notice])) (base 'b' (idx [op])) ==
        [s!"history: {sha 'b'}: {subj} was removed without a toolchain change"]),
    ("history: an uncommitted removal names HEAD as its lastCommit (C7)", fun _ =>
      lines (some (idx [] tcB [rec' 'b'] [notice])) (base 'b' (idx [op])) == [] &&
        lines (some (idx [] tcB [rec' 'e'] [notice])) (base 'b' (idx [op])) ==
          [s!"history: {sha 'b'}: {subj}: the removal names lastCommit {sha 'e'}, " ++
              s!"expected {sha 'b'}"]),
    ("history: a removal record of another toolchain than its witness's", fun _ =>
      lines (some (idx [] tcB [rec' 'b' tcB] [notice])) (base 'b' (idx [op])) ==
        [s!"history: {sha 'b'}: {subj}: the removal names toolchain {tcB}, expected {tcA}"]),
    ("history: a committed removal — any parent listing the operation is a witness", fun _ =>
      let w := idx [] tcB [rec' 'd'] [notice]
      lines (some w) (base 'b' w) [base 'c' (idx [op]), base 'd' (idx [op])] == [] &&
        lines (some w) (base 'b' w) [base 'c' (idx [op]), base 'd' (idx [] tcA [] [])] ==
          [s!"history: {sha 'c'}: {subj}: the removal names lastCommit {sha 'd'}, " ++
              s!"expected {sha 'c'}"]),
    ("history: a parent already holding the record → no witness line (preserved)", fun _ =>
      let w := idx [] tcB [rec' 'e'] [notice]
      lines (some w) (base 'b' w) [base 'c' w, base 'd' (idx [op])] == []),
    ("history: removed records + notices not extending a baseline's, after its operations", fun _ =>
      lines (some (idx [op] tcA [] [notice "b"]))
          (base 'b' (idx [op] tcA [rec' 'f'] [notice "a"])) ==
        [s!"history: {sha 'b'}: the removed records do not extend this commit's",
          s!"history: {sha 'b'}: the notices do not extend this commit's"]),
    ("history: the parents' diverging notices → that line first", fun _ =>
      let l := idx [op] tcA [] [notice "l"]
      let r := idx [op] tcA [] [notice "r"]
      lines (some l) (base 'b' l) [base 'c' l, base 'd' r] ==
        [s!"history: {sha 'b'}: the parents' notices diverge: rebase to linearize",
          s!"history: {sha 'd'}: the notices do not extend this commit's"]),
    ("history: an undecodable baseline → its line alone; an undecodable working index → alone",
      fun _ =>
      (history (.ok (some (idx [op]))) ⟨sha 'b', some (.error "malformed")⟩ []).map Line.render ==
          [s!"history: {sha 'b'}: index.json does not decode: malformed"] &&
        (history (.error "malformed") (base 'b' (idx [op])) []).map Line.render ==
          ["history: working tree: index.json does not decode: malformed"])]

end History

/-! Compiled-code smoke for hashing (contract U3 S3, S5, H1–H3): FIPS 180-4 example digests through
HACL*'s C, streaming = one-shot over splits + shared states, hex + frame bytes, `unframe` refusals.
The blind suite (`tests/codec/`) carries NIST CAVP + the `sha256sum` differential. -/

namespace Hash

open FvdepCore.Hash FvdepIO.Hash

def bytes (xs : List Nat) : ByteArray := ⟨(xs.map Nat.toUInt8).toArray⟩

def text (s : String) : ByteArray := s.toUTF8

/-- `n < 256` as 8 big-endian bytes. -/
def be (n : Nat) : List Nat := [0, 0, 0, 0, 0, 0, 0, n]

/-- The shipped hash step (`FvdepIO.Hash.sha256Hex`), short for the known answers below. -/
def hexOf (b : ByteArray) : String := sha256Hex b

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

/-! ## U5 T3: the step limits' relation (A1) -/

namespace Sandbox

open FvdepCore.Sandbox

def cases : List (String × (Unit → Bool)) :=
  [("sandbox: the default limits hold T3's relation (the per-file cap = workBytes / 8)", fun _ =>
      ({} : Limits).check.isNone && ({} : Limits).fileCap == 134217728),
    ("sandbox: a per-file cap above workBytes / 8 is refused, at it accepted", fun _ =>
      ({ workBytes := 800000, fileBytes := some 100001 } : Limits).check.isSome &&
        ({ workBytes := 800000, fileBytes := some 100000 } : Limits).check.isNone),
    ("sandbox: workBytes below 8 leaves a per-file cap of 0, refused", fun _ =>
      ({ workBytes := 7 } : Limits).check.isSome && ({ workBytes := 8 } : Limits).check.isNone),
    ("sandbox: a tmpfs size above bwrap's cap (2^63 − 1) is refused, at it accepted", fun _ =>
      let cap := 9223372036854775807
      ({ workBytes := cap + 1 } : Limits).check.isSome &&
        ({ tmpBytes := cap + 1 } : Limits).check.isSome &&
        ({ workBytes := cap, tmpBytes := cap } : Limits).check.isNone)]

end Sandbox

/-! ## U5 R2 + R8: the spawn shim's own refusals (`c/fvdep_spawn.c`; signal 0 sends nothing) -/

namespace Spawn

def ioCases : List (String × IO Bool) :=
  [("spawn: kill refuses pid 0 (the caller's group) + -1 (every process it may signal): EINVAL", do
      let own ← IO.Process.getPID
      return (← FvdepIO.Spawn.kill 0 0) matches .error 22 &&
          (← FvdepIO.Spawn.kill 0xFFFFFFFF 0) matches .error 22 &&
          (← FvdepIO.Spawn.kill own 0) matches .ok ()),
    ("spawn: a string with an interior NUL is refused (EINVAL) before any spawn", do
      return (← FvdepIO.Spawn.bwrap "/nonexistent" #["bwrap", "a\x00b"]) matches .error 22 &&
          (← FvdepIO.Spawn.bwrap "/nonexistent\x00x" #["bwrap"]) matches .error 22 &&
          (← FvdepIO.Spawn.spawn #["/nonexistent\x00x"] "") matches .error 22 &&
          (← FvdepIO.Spawn.spawn #["true"] "out\x00x") matches .error 22 &&
          (← FvdepIO.Spawn.spawn #["/nonexistent"] "") matches .error 2)]

end Spawn

/-! ## U5 R8: the step helper's arguments (`FvdepIO.Step.plan`) -/

namespace Step

def cases : List (String × (Unit → Bool)) :=
  [("step: --file-bytes takes 1 … 2^64 − 2 (RLIMIT_FSIZE = n exactly; 2^64 − 1 = RLIM_INFINITY)",
      fun _ =>
      (FvdepIO.Step.plan ["--file-bytes", "18446744073709551614", "--", "true"]).toOption.map
            (·.fileBytes) ==
          some (some 18446744073709551614) &&
        ["0", "18446744073709551615", "18446744073709551616", "36893488147419103233"].all fun n =>
          FvdepIO.Step.plan ["--file-bytes", n, "--", "true"] matches .error _)]

end Step

/-! ## U5 K6 + T1: the manifest + fingerprint records (canonical intake), K2's ownership rule,
the cache shim (`c/fvdep_cache.c`) -/

namespace Cache

open FvdepCore.Build

/-- JSON's hard cases: escapes, control characters, non-ASCII, the metadata names. -/
def strs : Array String :=
  #["", "a", "Fvdep.A.B", "\"", "\\", "\n\t", "é∀", "\x01", "/", "x y", "manifest.json", "used",
    "𝔽"]

def nats : Array Nat := #[0, 1, 7, 4096, 9007199254740991]

/-- One draw from `xs` (nonempty) + the next state. -/
def pick {α : Type} [Inhabited α] (xs : Array α) (s : UInt64) : α × UInt64 :=
  let (r, s) := splitmix s
  (xs[(r % xs.size.toUInt64).toNat]!, s)

/-- A manifest from state `s`: every string + number drawn from the pools (within J's bounds). -/
def genManifest (s : UInt64) : Manifest × UInt64 :=
  Id.run do
    let mut s := s
    let mut draw : Array String := #[]
    for _ in [0:12] do
      let (x, s') := pick strs s
      draw := draw.push x
      s := s'
    let (n1, s1) := pick nats s
    let (n2, s2) := pick nats s1
    let (k, s3) := splitmix s2
    let imports :=
      (List.range (k % 4).toNat).map fun i =>
        { module := draw[i]!
          isPublic := i % 2 == 0
          isMeta := i % 3 == 0
          all := i == 1
          key := draw[i + 1]! : Import }
    let arts :=
      (List.range ((k >>> 8) % 4).toNat).map fun i =>
        { path := draw[i + 4]!, size := if i == 0 then n2 else i, sha256 := draw[i + 5]! : FileRec }
    let recipe : Recipe :=
      { id := draw[0]!
        release := draw[1]!
        fingerprint := draw[2]!
        argv := [draw[3]!, draw[4]!]
        leanPath := [draw[5]!]
        env := [(draw[6]!, draw[7]!)]
        options := [draw[8]!]
        threads := n1 }
    let input : KeyInput :=
      { recipe
        module := draw[9]!
        path := draw[10]!
        source := draw[11]!
        imports }
    return ({ schema := n1 % 3, input, artifacts := arts }, s3)

def sample : Manifest := (genManifest 7).1

def cases : List (String × (Unit → Bool)) :=
  [("cache: 500 generated manifests read back from their canonical text (manifestOf ∘ " ++
        "manifestText)",
      fun _ =>
      (List.range 500).foldl
          (fun (acc : Bool × UInt64) _ =>
            let (m, s) := genManifest acc.2
            (acc.1 && manifestOf (manifestText m) == some m, s))
          (true, 0x5EEDCAC4E0000001) |>.1),
    ("cache: a manifest spelled another way, with a member added or dropped, is no manifest",
      fun _ =>
      let t := FvdepCore.Index.Command.textOfBytes (manifestText sample)
      let spaced := (t.replace "\":" "\": ").toUTF8
      let ms :=
        match manifestValue sample with
        | .obj ms => ms
        | _ => []
      let added := FvdepCore.Json.print (.obj (ms ++ [("zzz", .str "x")]))
      let dropped := FvdepCore.Json.print (.obj (ms.filter (·.1 != "schema")))
      (manifestOf spaced).isNone && (manifestOf added).isNone && (manifestOf dropped).isNone &&
        (manifestOf (manifestText sample)).isSome),
    ("cache: the fingerprint record reads back; another spelling or schema does not", fun _ =>
      let f : Fingerprint :=
        { release := "4.35.0+eb6c"
          value := "ab"
          stamp := { files := 15284, bytes := 2859424511, sec := 1791823296, nsec := 7 } }
      let t := FvdepCore.Index.Command.textOfBytes (fingerprintRecord f)
      fingerprintOf (fingerprintRecord f) == some f &&
        (fingerprintOf (t.replace "\"schema\":1" "\"schema\":2").toUTF8).isNone &&
        (fingerprintOf (t ++ "\n").toUTF8).isNone),
    ("cache: the fingerprint's list is order-free (sorted by path)", fun _ =>
      let a : FileRec := { path := "lib/lean/Init.olean", size := 3, sha256 := "a" }
      let b : FileRec := { path := "bin/lean", size := 9, sha256 := "b" }
      fingerprintText [a, b] == fingerprintText [b, a]),
    ("cache: Init, Std, Lean + Lake modules are the toolchain's, every other the library's",
      fun _ =>
      ["Init", "Init.Data.List", "Std.Data", "Lean", "Lake.Build"].all toolchainModule &&
        !["Fvdep.Base64", "Initial", "LeanX.Y", "Fvdep.Init"].any toolchainModule)]

def ioCases : List (String × IO Bool) :=
  [("cache: link + touch refuse an interior NUL (EINVAL)", do
      return (← FvdepIO.Cache.link "a\x00b" "c") matches .error 22 &&
          (← FvdepIO.Cache.link "a" "c\x00d") matches .error 22 &&
          (← FvdepIO.Cache.touch "a\x00b") matches .error 22),
    ("cache: touch stamps a file now; link gives its bytes a second name", do
      let dir ← IO.FS.createTempDir
      try
        let f := dir / "used"
        IO.FS.writeFile f "x"
        let old := (← f.metadata).modified
        IO.sleep 20
        let touched ← FvdepIO.Cache.touch f.toString
        let now := (← f.metadata).modified
        let linked ← FvdepIO.Cache.link f.toString (dir / "second").toString
        let again ← FvdepIO.Cache.link f.toString (dir / "second").toString
        return touched matches .ok () &&
            (old.sec < now.sec || (old.sec == now.sec && old.nsec < now.nsec)) &&
            linked matches .ok () &&
            again matches .error 17 &&
            (← IO.FS.readFile (dir / "second")) == "x"
      finally
        IO.FS.removeDirAll dir),
    ("cache: T1's record is believed while the toolchain's stamp holds, recomputed once it " ++
        "moves; " ++
        "a link in the toolchain refused",
      do
      let dir ← IO.FS.createTempDir
      try
        let sys := dir / "sys"
        let cache := dir / "cache"
        IO.FS.createDirAll (sys / "bin")
        IO.FS.createDirAll (sys / "lib" / "lean" / "Init")
        let files :=
          [("bin/lean", "lean"), ("bin/leanexport", "leanexport"),
            ("lib/lean/Init/Core.olean", "olean")]
        for (p, t) in files do
          IO.FS.writeFile (sys / p) t
        let want :=
          FvdepIO.Hash.sha256Hex
            (fingerprintText
              (files.map fun (p, t) =>
                { path := p, size := t.utf8ByteSize, sha256 := FvdepIO.Hash.sha256Hex t.toUTF8 }))
        let first ← FvdepIO.Toolchain.fingerprint cache sys
        let record := cache / "toolchains" / "v1" / (FvdepIO.Toolchain.release ++ ".json")
        let some f := fingerprintOf (← IO.FS.readBinFile record)
          | return false
        IO.FS.writeBinFile record (fingerprintRecord { f with value := "planted" })
        let believed ← FvdepIO.Toolchain.fingerprint cache sys
        IO.FS.writeFile (sys / "lib" / "lean" / "Init" / "Core.olean") "olean, rebuilt"
        let moved ← FvdepIO.Toolchain.fingerprint cache sys
        discard <|
            IO.Process.output
              { cmd := "ln",
                args :=
                  #["-s", "Core.olean", (sys / "lib" / "lean" / "Init" / "L.olean").toString] }
        let linked ← FvdepIO.Toolchain.fingerprint cache sys
        let ok (r : Except String String) (v : String) : Bool :=
          match r with
          | .ok w => w == v
          | .error _ => false
        return ok first want && ok believed "planted" &&
            (match moved with
            | .ok v => v != want && v != "planted"
            | .error _ => false) &&
            linked matches .error _
      finally
        IO.FS.removeDirAll dir)]

end Cache

namespace Snapshot

open FvdepCore.Phase FvdepIO.Snapshot

def small : SourceLimits := { fileBytes := 10, totalBytes := 25 }

def cases : List (String × (Unit → Bool)) :=
  [("snapshot: T3's defaults = 1 MiB per source file + 16 MiB per snapshot", fun _ =>
      ({} : SourceLimits) == { fileBytes := 1048576, totalBytes := 16777216 }),
    ("snapshot: Linux's S_IF* values map to their kinds", fun _ =>
      [(0o040000, Kind.directory), (0o100000, .regular), (0o010000, .fifo), (0o140000, .socket),
            (0o020000, .charDevice), (0o060000, .blockDevice), (0o120000, .link), (7, .other 7)].all
        fun x => Kind.ofMode x.1 == x.2),
    ("snapshot: a directory on the way descends, any other kind there is refused", fun _ =>
      snapDecide small 0 false (.file .directory 4096) == .descend &&
        [Kind.regular, .fifo, .socket, .charDevice, .blockDevice, .link, .other 1].all fun k =>
          snapDecide small 0 false (.file k 0) == .refuse (.kind k)),
    ("snapshot: the module's file must be a regular file", fun _ =>
      [Kind.directory, .fifo, .socket, .charDevice, .blockDevice, .link, .other 1].all fun k =>
        snapDecide small 0 true (.file k 0) == .refuse (.kind k)),
    ("snapshot: an open error refuses at either position", fun _ =>
      [2, 6, 13, 40].all fun n =>
        snapDecide small 0 true (.error n) == .refuse (.unopened n) &&
          snapDecide small 0 false (.error n) == .refuse (.unopened n)),
    ("snapshot: the per-file cap is inclusive (n read, n + 1 refused)", fun _ =>
      snapDecide small 0 true (.file .regular 10) == .read 10 &&
        snapDecide small 0 true (.file .regular 11) == .refuse (.fileOver 11 10)),
    ("snapshot: the total is inclusive; a read's cap = the smaller remainder", fun _ =>
      snapDecide small 15 true (.file .regular 10) == .read 10 &&
        snapDecide small 20 true (.file .regular 5) == .read 5 &&
        snapDecide small 20 true (.file .regular 6) == .refuse (.totalOver 26 25)),
    ("snapshot: a read past its cap is refused by the cap that bound it", fun _ =>
      (match snapRead small 0 10 10 with
        | .ok 10 => true
        | _ => false) &&
        (match snapRead small 0 10 11 with
        | .error (.grewFile 10) => true
        | _ => false) &&
        (match snapRead small 20 5 6 with
        | .error (.grewTotal 25) => true
        | _ => false) &&
        match snapRead small 20 5 3 with
        | .ok 23 => true
        | _ => false),
    ("snapshot: a name outside T3's grammar or listed twice is refused before any open", fun _ =>
      ["A..B", "", ".A", "A.", "A/B", "/abs/A", "1A", "A-B", "A.B c"].all
          (fun m => snapNames ["Ok.A", m] == some (m, .notModuleName)) &&
        snapNames ["A.B", "C", "A.B"] == some ("A.B", .listedTwice) &&
        snapNames ["A.B", "C", "A.D'"] == none),
    ("snapshot: a module's path components (`.lean` on the last)", fun _ =>
      snapPath "A.B.C" == ["A", "B", "C.lean"] && snapPath "X" == ["X.lean"]),
    ("snapshot: a refusal's detail names the file, the component + the cause", fun _ =>
      detail "A/B.lean" "A/B.lean" (.unopened 40) == "A/B.lean is a symbolic link" &&
        detail "A/B.lean" "A" (.kind .regular) == "A/B.lean: A is not a directory" &&
        detail "A/B.lean" "A/B.lean" (.fileOver 11 10) ==
          "A/B.lean has 11 bytes, over the limit of 10 bytes per source file")]

/-- `d`'s tree removed without following a link (a link, FIFO or socket goes as itself). -/
partial def rmTree (d : System.FilePath) : IO Unit := do
  for e in ← d.readDir do
    if (← e.path.symlinkMetadata).type == .dir then
      rmTree e.path
    else
      IO.FS.removeFile e.path
  IO.FS.removeDir d

/-- `f` on a fresh project directory (2nd argument) inside a fresh directory (1st: room for files
outside the project). -/
def withProject (f : System.FilePath → System.FilePath → IO Bool) : IO Bool := do
  let d ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (d / "p")
    f d (d / "p")
  finally
    rmTree d

def put (root : System.FilePath) (rel : String) (bytes : ByteArray) : IO Unit := do
  let f := root / rel
  if let some dir := f.parent then
    IO.FS.createDirAll dir
  IO.FS.writeBinFile f bytes

def spaces (n : Nat) : ByteArray := ⟨(List.replicate n 0x20).toArray⟩

/-- A fixture command's success (a failed `ln`, `mkfifo` or `python3` fails the case). -/
def sh (cmd : String) (args : Array String) : IO Bool := do
  return (← IO.Process.output { cmd, args }).exitCode == 0

def refusedWith (r : Except String Sources) (d : String) : Bool :=
  match r with
  | .error e => e == d
  | .ok _ => false

def openFds : IO Nat := do
  return (← System.FilePath.readDir "/proc/self/fd").size

def ioCases : List (String × IO Bool) :=
  [("snapshot: each module's bytes, read once, in the listed order + split",
      withProject fun _ p => do
        put p "A/B.lean" "ab".toUTF8
        put p "C.lean" "c".toUTF8
        put p "A/D.lean" "ad".toUTF8
        match ← FvdepIO.Snapshot.read p ["A.B", "C"] ["A.D"] with
        | .ok s =>
          return s.impl.map (fun x => (x.1, x.2.toList)) ==
                [("A.B", "ab".toUTF8.toList), ("C", "c".toUTF8.toList)] &&
              s.proof.map (fun x => (x.1, x.2.toList)) == [("A.D", "ad".toUTF8.toList)]
        | .error _ =>
          return false),
    ("snapshot: a link at the module's file is refused (O_NOFOLLOW)",
      withProject fun d p => do
        put d "outside.lean" "x".toUTF8
        IO.FS.createDirAll (p / "A")
        let made ← sh "ln" #["-s", (d / "outside.lean").toString, (p / "A" / "B.lean").toString]
        return made &&
            refusedWith (← FvdepIO.Snapshot.read p ["A.B"] []) "A/B.lean is a symbolic link"),
    ("snapshot: a link at a directory on the way is refused, naming it",
      withProject fun d p => do
        put d "real/B.lean" "x".toUTF8
        let made ← sh "ln" #["-s", (d / "real").toString, (p / "A").toString]
        return made &&
            refusedWith (← FvdepIO.Snapshot.read p ["A.B"] []) "A/B.lean: A is a symbolic link"),
    ("snapshot: a FIFO is refused at once (O_NONBLOCK: no wait for a writer)",
      withProject fun _ p => do
        IO.FS.createDirAll (p / "A")
        let fifo := p / "A" / "B.lean"
        unless ← sh "mkfifo" #[fifo.toString] do
          return false
        -- A writer arrives after 3 s: an open that waits for one returns only then.
        let opener ←
          IO.Process.spawn
              { cmd := "python3"
                args :=
                  #["-c", "import os, sys, time; time.sleep(3); os.open(sys.argv[1], os.O_RDWR)",
                    fifo.toString] }
        let t0 ← IO.monoMsNow
        let r ← FvdepIO.Snapshot.read p ["A.B"] []
        let t1 ← IO.monoMsNow
        opener.kill
        discard opener.wait
        return t1 - t0 < 1500 && refusedWith r "A/B.lean is a named pipe (FIFO)"),
    ("snapshot: a socket is refused (ENXIO)",
      withProject fun _ p => do
        IO.FS.createDirAll (p / "A")
        let made ←
          sh "python3"
              #["-c", "import socket, sys; socket.socket(socket.AF_UNIX).bind(sys.argv[1])",
                (p / "A" / "B.lean").toString]
        return made &&
            refusedWith (← FvdepIO.Snapshot.read p ["A.B"] [])
              "A/B.lean is a socket or a device without a driver"),
    ("snapshot: a directory at the module's file is refused",
      withProject fun _ p => do
        IO.FS.createDirAll (p / "A" / "B.lean")
        return refusedWith (← FvdepIO.Snapshot.read p ["A.B"] []) "A/B.lean is a directory"),
    ("snapshot: a file where a directory belongs is refused",
      withProject fun _ p => do
        put p "A" "x".toUTF8
        return refusedWith (← FvdepIO.Snapshot.read p ["A.B"] []) "A/B.lean: A is not a directory"),
    ("snapshot: a missing file or directory is refused, naming it",
      withProject fun _ p => do
        IO.FS.createDirAll (p / "A")
        return refusedWith (← FvdepIO.Snapshot.read p ["A.B"] []) "A/B.lean does not exist" &&
            refusedWith (← FvdepIO.Snapshot.read p ["X.B"] []) "X/B.lean: X does not exist"),
    ("snapshot: a name outside T3's grammar is refused unread, a real file behind it",
      withProject fun d p => do
        put d "real/Impl.lean" "x".toUTF8
        put d "Abs.lean" "x".toUTF8
        let made ← sh "ln" #["-s", (d / "real").toString, (p / "Link").toString]
        let abs := (d / "Abs").toString
        return made &&
            refusedWith (← FvdepIO.Snapshot.read p ["Link/Impl"] [])
              "Link/Impl is not a module name" &&
            refusedWith (← FvdepIO.Snapshot.read p [abs] []) s!"{abs} is not a module name"),
    ("snapshot: the shim refuses a name other than one path component (EINVAL)",
      withProject fun _ p => do
        put p "A.lean" "x".toUTF8
        match ← FvdepIO.Sys.Native.openDir p.toString with
        | .error _ =>
          return false
        | .ok dir =>
          let dir := dir.toUInt32
          let refused ←
            ["", ".", "..", "x/A.lean", "./A.lean", "/etc/hostname", "A.lean\x00x"].allM fun n => do
                return (← openAt dir n) matches .error 22
          let good ←
            match ← openAt dir "A.lean" with
            | .ok #[fd, _, 1] =>
              discard <| FvdepIO.Sys.Native.close fd.toUInt32
              pure true
            | _ =>
              pure false
          discard <| FvdepIO.Sys.Native.close dir
          return refused && good),
    ("snapshot: the per-file cap holds at n bytes, refuses n + 1",
      withProject fun _ p => do
        put p "A.lean" (spaces 10)
        put p "B.lean" (spaces 11)
        let l : SourceLimits := { fileBytes := 10, totalBytes := 100 }
        let a ← FvdepIO.Snapshot.read p ["A"] [] l
        return a matches .ok _ &&
            refusedWith (← FvdepIO.Snapshot.read p ["A"] ["B"] l)
              "B.lean has 11 bytes, over the limit of 10 bytes per source file"),
    ("snapshot: the total over implementation + proof holds at n, refuses n + 1",
      withProject fun _ p => do
        put p "A.lean" (spaces 10)
        put p "B.lean" (spaces 10)
        put p "C.lean" (spaces 5)
        put p "D.lean" (spaces 6)
        let a ← FvdepIO.Snapshot.read p ["A", "B"] ["C"] small
        return a matches .ok _ &&
            refusedWith (← FvdepIO.Snapshot.read p ["A", "B"] ["D"] small)
              ("D.lean brings the sources to 26 bytes, over the limit of 25 bytes per " ++
                "project snapshot")),
    ("snapshot: the default cap: a 1 MiB file is read, one byte more is refused",
      withProject fun _ p => do
        put p "A.lean" (spaces 1048576)
        put p "B.lean" (spaces 1048577)
        let a ← FvdepIO.Snapshot.read p ["A"] []
        return a matches .ok _ &&
            refusedWith (← FvdepIO.Snapshot.read p ["B"] [])
              "B.lean has 1048577 bytes, over the limit of 1048576 bytes per source file"),
    ("snapshot: readCapped stops once past its limit (n + 1 bytes of a longer file)",
      withProject fun _ p => do
        put p "A.lean" (spaces 50)
        match ← FvdepIO.Sys.Native.openRead (p / "A.lean").toString with
        | .error _ =>
          return false
        | .ok fd =>
          let r ← readCapped fd.toUInt32 10
          discard <| FvdepIO.Sys.Native.close fd.toUInt32
          match r with
          | .ok b =>
            return b.size == 11
          | .error _ =>
            return false),
    ("snapshot: no descriptor outlives a read on any path (20 rounds after a warm-up)",
      withProject fun d p => do
        put p "Ok.lean" "x".toUTF8
        put p "Deep/Er/Ok.lean" "x".toUTF8
        put d "outside.lean" "x".toUTF8
        unless ← sh "ln" #["-s", (d / "outside.lean").toString, (p / "L.lean").toString] do
          return false
        IO.FS.createDirAll (p / "Dir.lean")
        put p "F" "x".toUTF8
        put p "Big.lean" (spaces 11)
        let l : SourceLimits := { fileBytes := 10, totalBytes := 100 }
        let reads :=
          [(["Ok"], ["Deep.Er.Ok"]), (["L"], []), (["Missing"], []), (["Dir"], []), (["F.X"], []),
            (["Big"], []), (["Ok"], ["Deep.Er.Missing"]), (["Deep.Er.Ok.X"], [])]
        let round : IO Unit := do
          for (impl, proof) in reads do
            discard <| FvdepIO.Snapshot.read p impl proof l
        round
        let before ← openFds
        for _ in [0:20] do
          round
        return before == (← openFds))]

end Snapshot

namespace PhaseIO

def ioCases : List (String × IO Bool) :=
  [("phase: a host I/O failure (the run directory or phase 1's sources a file) = infra io, " ++
        "never an " ++
        "exception",
      do
      let dir ← IO.FS.createTempDir
      try
        let run := dir / "run"
        IO.FS.writeFile run "a file where the run directory belongs"
        let e : FvdepIO.Cache.Env :=
          { root := dir / "cache"
            bwrap := "bwrap"
            sysroot := dir
            helper := dir
            recipe := FvdepCore.Build.library "r" "f"
            limits := {}
            step := {}
            trace := none
            run
            handles := ← IO.mkRef #[]
            counter := ← IO.mkRef 0 }
        let s : FvdepIO.Phase.Setup :=
          { cache := e
            recipe := FvdepCore.Build.consumer "r" "f"
            limits := {}
            library := dir }
        let r : FvdepIO.Phase.Request :=
          { impl := [("A", "def a := 1".toUTF8)]
            proof := []
            specModule := "S"
            spec := "S.s"
            abi := none
            roots1 := []
            roots2 := [] }
        let rep ← FvdepIO.Phase.check s r
        -- A run directory whose phase-1 sources directory is a file: the failure is phase 1's own.
        let run2 := dir / "run2"
        IO.FS.createDirAll run2
        IO.FS.writeFile (run2 / "sources1") "a file where phase 1's sources belong"
        let rep2 ← FvdepIO.Phase.check { s with cache := { e with run := run2 } } r
        return rep.runs.map (·.obs) matches [FvdepCore.Evidence.Obs.infra .io _] &&
            rep2.runs.map (·.obs) matches [FvdepCore.Evidence.Obs.infra .io _]
      finally
        IO.FS.removeDirAll dir)]

end PhaseIO

namespace PhaseD

open FvdepCore.Phase FvdepCore.Bundle FvdepCore.Sandbox

def jsonLine : String :=
  "{\"caption\":\"\",\"data\":\"Unknown identifier `u5`\\nsecond\"," ++
    "\"endPos\":{\"column\":35,\"line\":3}," ++
    "\"fileName\":\"./A/B.lean\",\"isSilent\":false,\"keepFullRange\":false," ++
    "\"kind\":\"lean.unknownIdentifier._namedError\",\"pos\":{\"column\":14,\"line\":3}," ++
    "\"severity\":\"error\"}"

def scanAll (chunks : List String) (cap : Nat := 4096) : Option Diag :=
  let s :=
    chunks.foldl
      (fun s c => s.push cap ofJson FvdepIO.Sandbox.jsonMarker FvdepIO.Sandbox.jsonSkip c.toUTF8)
      ({} : FvdepIO.Sandbox.Scan)
  s.finish ofJson FvdepIO.Sandbox.jsonMarker FvdepIO.Sandbox.jsonSkip

def info : String := "{\"data\":\"x\",\"severity\":\"information\"}"

def cases : List (String × (Unit → Bool)) :=
  [("phase: P1's window = the compiles in order, the roots check, the export", fun _ =>
      steps ["A", "B.C"] == [.compile "A", .compile "B.C", .consumerRoots, .exportStep] &&
        steps [] == [.consumerRoots, .exportStep]),
    ("phase: an import's class — listed, built, toolchain, library, else absent (first match)",
      fun _ =>
      let c := importClass ["P.A", "P.B"] ["Q.A"] (fun m => m == "Fvdep.X" || m == "P.A")
      c "P.A" == .listed && c "Q.A" == .built && c "Init.Data" == .toolchain &&
        c "Lean" == .toolchain &&
        c "Fvdep.X" == .library &&
        c "Fvdep.Y" == .absent &&
        c "External" == .absent),
    ("phase: the roots file puts root k on line imports + 1 + k; other lines name none", fun _ =>
      rootsSource ["A", "B"] ["x", "y"] == "import A\nimport B\n\n#check @x\n#check @y\n" &&
        rootAt ["A", "B"] ["x", "y"] 4 == some "x" &&
        rootAt ["A", "B"] ["x", "y"] 5 == some "y" &&
        (rootAt ["A", "B"] ["x", "y"] 3).isNone &&
        (rootAt ["A", "B"] ["x", "y"] 1).isNone &&
        (rootAt ["A", "B"] ["x", "y"] 6).isNone &&
        rootAt [] ["r"] 2 == some "r"),
    ("bundle: B1 reads Lean's JSON error line (file, line, message) + skips other severities",
      fun _ =>
      ofJson jsonLine ==
          some
            { file := some "./A/B.lean", line := some 3,
              message := "Unknown identifier `u5`\nsecond" } &&
        (ofJson info).isNone &&
        (ofJson "not json").isNone),
    ("bundle: B1 reads a marked stdout line nested to the capture cap (a step's bytes are " ++
        "untrusted) + returns, no diagnostic",
      fun _ =>
      let opens := String.ofList (List.replicate 65000 '[')
      let closes := String.ofList (List.replicate 65000 ']')
      (ofJson ("{\"severity\":\"error\",\"data\":" ++ opens)).isNone &&
        (ofJson ("{\"data\":" ++ opens ++ closes ++ ",\"severity\":\"error\"}")).isNone),
    ("bundle: B1 reads Lean's text-form error line (named error or not)", fun _ =>
      ofText "./A/B.lean:1:14: error(lean.unknownIdentifier): Unknown identifier `u5`" ==
          some
            { file := some "./A/B.lean", line := some 1, message := "Unknown identifier `u5`" } &&
        ofText "X.lean:7:0: error: a: b" ==
          some { file := some "X.lean", line := some 7, message := "a: b" } &&
        (ofText "plain text").isNone),
    ("bundle: B1's reason maps the path, keeps the first line, escapes controls last", fun _ =>
      reason "implementation" (ofJson jsonLine) "lean" 1 ==
          "implementation build failed (A/B.lean:3: Unknown identifier `u5`)" &&
        reason "proof" (some { file := some "/fvdep/src/P/Q.lean", line := some 2, message := "m" })
            "lean" 1 ==
          "proof build failed (P/Q.lean:2: m)" &&
        reason "proof"
            (some { file := some "/fvdep/lib/Fvdep/A/B.olean", line := some 1, message := "m" })
            "lean" 1 ==
          "proof build failed (Fvdep.A.B:1: m)" &&
        reason "proof" (some { file := none, line := none, message := "bare\nmore" }) "lean" 1 ==
          "proof build failed (bare)" &&
        reason "implementation" none "leanexport" 134 ==
          "implementation build failed (leanexport exited with code 134)" &&
        reason "proof" (some { file := none, line := none, message := "a\x1B\tb" }) "lean" 1 ==
          "proof build failed (a\\u001B\\tb)"),
    ("bundle: B2 omits the largest inputs first (ties by path) until the rest fits", fun _ =>
      omitOrder [("a", 5), ("b", 9), ("c", 9), ("d", 1)] 24 == [] &&
        omitOrder [("a", 5), ("b", 9), ("c", 9), ("d", 1)] 23 == ["b"] &&
        omitOrder [("a", 5), ("b", 9), ("c", 9), ("d", 1)] 6 == ["b", "c"] &&
        omitOrder [("a", 5), ("b", 9), ("c", 9), ("d", 1)] 0 == ["b", "c", "a", "d"]),
    ("bundle: B2 keeps the newest 16 by time, then name", fun _ =>
      let bs := (List.range 18).map fun i => (s!"n{i + 10}", if i < 2 then 0 else i)
      retainPick bs 16 == ["n10", "n11"] &&
        retainPick [("b", 1), ("a", 1), ("c", 2)] 1 == ["a", "b"] &&
        retainPick [("a", 1)] 16 == []),
    ("bundle: B2's record reads back from its canonical text alone (D4's intake; an input " ++
        "outside the roles src, lib, prior or at an unsafe path = no record)",
      fun _ =>
      let rc : Record :=
        { recipe := FvdepCore.Build.consumer "4.35.0+x" "fp"
          limits := { fileBytes := some 7, exportBytes := some 5 }
          phase := 2
          step := "compile"
          module := "A.B"
          imports := ["X"]
          roots := ["r"]
          presence := [("Y", "library")]
          inputs :=
            [{ role := "src", path := "A/B.lean", size := 3, sha256 := "ab", kept := true }] }
      let b := FvdepCore.Json.print rc.value
      let t := FvdepCore.Index.Command.textOfBytes b
      Record.ofBytes b == some rc &&
        (Record.ofBytes (t.replace "\"schema\":1" "\"schema\":2").toUTF8).isNone &&
        (Record.ofBytes (b ++ " ".toUTF8)).isNone &&
        (Record.ofBytes (t.replace "\"complete\":true" "\"complete\":false").toUTF8).isNone &&
        (Record.ofBytes (t.replace "\"phase\":2" "\"phase\": 2").toUTF8).isNone &&
        (Record.ofBytes
            (FvdepCore.Json.print
              { rc with
                  inputs :=
                    [{ role := "src", path := "../x", size := 3, sha256 := "ab",
                       kept := true }] }.value)).isNone &&
        (Record.ofBytes
            (FvdepCore.Json.print
              { rc with
                  inputs :=
                    [{ role := "etc", path := "x", size := 3, sha256 := "ab",
                       kept := true }] }.value)).isNone),
    ("sandbox: T3's export cap ≥ 1 + ≤ the per-file cap (default = it)", fun _ =>
      ({} : Limits).exportCap == ({} : Limits).fileCap &&
        ({ exportBytes := some 0 } : Limits).check.isSome &&
        ({ fileBytes := some 100, exportBytes := some 101 } : Limits).check.isSome &&
        ({ fileBytes := some 100, exportBytes := some 100 } : Limits).check.isNone),
    ("sandbox: B1's scan finds the first error line across chunk boundaries, skipping the rest",
      fun _ =>
      let line := jsonLine ++ "\n"
      let n := line.length / 2
      let a := String.ofList (line.toList.take n)
      let b := String.ofList (line.toList.drop n)
      (scanAll [info ++ "\n" ++ a, b ++ info ++ "\n"]).map (·.line) == some (some 3) &&
        (scanAll [info ++ "\n", info]).isNone &&
        (scanAll [jsonLine]).map (·.line) == some (some 3) &&
        (scanAll
                (List.replicate 50 "x\nyy\n" ++
                  [jsonLine ++ "\n", jsonLine.replace "line\":3" "line\":9"])).map
            (·.line) ==
          some (some 3)),
    ("sandbox: an error line past the cap is never read; Horspool's search finds a marker exactly",
      fun _ =>
      (scanAll [jsonLine ++ "\n"] (cap := 20)).isNone &&
        (FvdepIO.Sandbox.find "abcab".toUTF8 "cab".toUTF8 (FvdepIO.Sandbox.skipOf "cab".toUTF8)
            0) ==
          some 2 &&
        (FvdepIO.Sandbox.find "ab".toUTF8 "abc".toUTF8 (FvdepIO.Sandbox.skipOf "abc".toUTF8)
            0).isNone &&
        (FvdepIO.Sandbox.find "zzbabb".toUTF8 "abb".toUTF8 (FvdepIO.Sandbox.skipOf "abb".toUTF8)
            0) ==
          some 3)]

end PhaseD

namespace ExportR

open FvdepCore.Export

def hdr (githash : String := Lean.githash) : String :=
  "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":" ++
    "{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"" ++
    githash ++
    "\",\"version\":\"" ++
    Lean.versionString ++
    "\"}}}"

def rdWith (h : String) (ls : List String) : Except Refusal (List Decl) :=
  read Lean.githash Lean.versionString ("\n".intercalate (h :: ls) ++ "\n").toUTF8

def rd (ls : List String) : Except Refusal (List Decl) := rdWith (hdr) ls

/-- name 1 = `a`, name 2 = `b`, level 1 = succ 0, expr 0 = Sort 1, expr 1 = const a. -/
def tables : List String :=
  ["{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}", "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"b\"}}",
    "{\"il\":1,\"succ\":0}", "{\"ie\":0,\"sort\":1}", "{\"const\":{\"name\":1,\"us\":[]},\"ie\":1}"]

def axiomA : String := "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"

def defB : String :=
  "{\"def\":{\"all\":[2],\"hints\":{\"regular\":1},\"levelParams\":[],\"name\":2," ++
    "\"safety\":\"safe\",\"type\":0,\"value\":1}}"

/-- The refusal's (line, class), or `none` when accepted. -/
def refusal (r : Except Refusal (List Decl)) : Option (Nat × Class) :=
  match r with
  | .error e => some (e.line, e.cls)
  | .ok _ => none

/-- Every name, level + expression form and every declaration kind (Q4). -/
def every : List String :=
  ["{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}", "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"b\"}}",
    "{\"in\":3,\"num\":{\"i\":7,\"pre\":1}}", "{\"in\":4,\"str\":{\"pre\":0,\"str\":\"u\"}}",
    "{\"in\":5,\"str\":{\"pre\":0,\"str\":\"T\"}}", "{\"in\":6,\"str\":{\"pre\":5,\"str\":\"mk\"}}",
    "{\"in\":7,\"str\":{\"pre\":5,\"str\":\"rec\"}}",
    "{\"in\":8,\"str\":{\"pre\":0,\"str\":\"q\"}}", "{\"in\":9,\"str\":{\"pre\":0,\"str\":\"o\"}}",
    "{\"in\":10,\"str\":{\"pre\":0,\"str\":\"t\"}}", "{\"il\":1,\"succ\":0}",
    "{\"il\":2,\"param\":4}", "{\"il\":3,\"max\":[1,2]}", "{\"il\":4,\"imax\":[2,1]}",
    "{\"ie\":0,\"sort\":1}", "{\"const\":{\"name\":1,\"us\":[2,3]},\"ie\":1}",
    "{\"bvar\":0,\"ie\":2}",
    "{\"forallE\":{\"binderInfo\":\"default\",\"body\":0,\"name\":2,\"type\":0},\"ie\":3}",
    "{\"ie\":4,\"lam\":{\"binderInfo\":\"implicit\",\"body\":2,\"name\":2,\"type\":0}}",
    "{\"app\":{\"arg\":2,\"fn\":4},\"ie\":5}",
    "{\"ie\":6,\"letE\":{\"body\":2,\"name\":2,\"nondep\":true,\"type\":0,\"value\":0}}",
    "{\"ie\":7,\"proj\":{\"idx\":0,\"struct\":2,\"typeName\":5}}", "{\"ie\":8,\"natVal\":\"42\"}",
    "{\"ie\":9,\"strVal\":\"s\"}", "{\"ie\":10,\"sort\":4}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[4],\"name\":1,\"type\":8}}",
    "{\"def\":{\"all\":[2],\"hints\":{\"regular\":3},\"levelParams\":[],\"name\":2," ++
      "\"safety\":\"partial\",\"type\":3,\"value\":4}}",
    "{\"thm\":{\"all\":[10],\"levelParams\":[3],\"name\":10,\"type\":0,\"value\":6}}",
    "{\"opaque\":{\"all\":[9],\"isUnsafe\":true,\"levelParams\":[],\"name\":9,\"type\":1," ++
      "\"value\":7}}",
    "{\"quot\":{\"kind\":\"lift\",\"levelParams\":[4],\"name\":8,\"type\":10}}", block 6]
where
  /-- An inductive block whose constructor is named `n`. -/
  block (n : Nat) : String :=
    "{\"inductive\":{\"ctors\":[{\"cidx\":0,\"induct\":5,\"isUnsafe\":false,\"levelParams\":[]," ++
      "\"name\":" ++
      toString n ++
      ",\"numFields\":0,\"numParams\":0,\"type\":9}],\"recs\":" ++
      "[{\"all\":[5],\"isUnsafe\":false,\"k\":true,\"levelParams\":[4],\"name\":7," ++
      "\"numIndices\":0,\"numMinors\":1,\"numMotives\":1,\"numParams\":0,\"rules\":" ++
      "[{\"ctor\":6,\"nfields\":0,\"rhs\":2}],\"type\":5}],\"types\":[{\"all\":[5]," ++
      "\"ctors\":[6],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false," ++
      "\"levelParams\":[],\"name\":5,\"numIndices\":0,\"numNested\":0,\"numParams\":0," ++
      "\"type\":0}]}}"

/-- A declaration's projection, `Expr`s compared with binder names + annotations. -/
def projects (d : Decl) (n : Lean.Name) (k : Kind) (lps : List Lean.Name) (ty : Lean.Expr)
    (v : Option Lean.Expr) : Bool :=
  d.name == n && d.kind == k && d.levelParams == lps && d.type.equal ty &&
    match d.value, v with
    | some a, some b => a.equal b
    | none, none => true
    | _, _ => false

def cases : List (String × (Unit → Bool)) :=
  [("export: a hand-made export reads back (names, levels, exprs, an axiom + a def)", fun _ =>
      match rd (tables ++ [axiomA, defB]) with
      | .ok [a, b] =>
        a.name == `a && a.kind == .axiom && a.type == .sort (.succ .zero) && a.value.isNone &&
          b.name == `b &&
          b.kind == .defn &&
          b.type == .sort (.succ .zero) &&
          b.value == some (.const `a [])
      | _ => false),
    ("export: every record form + declaration kind reads back (types, constructors, recursors)",
      fun _ =>
      let s1 : Lean.Expr := .sort (.succ .zero)
      let u : Lean.Level := .param `u
      let lam : Lean.Expr := .lam `b s1 (.bvar 0) .implicit
      match rd every with
      | .ok [a, b, t, o, q, ty, mk, rc] =>
        projects a `a .axiom [`u] (.lit (.natVal 42)) none &&
          projects b `b .defn [] (.forallE `b s1 s1 .default) (some lam) &&
          projects t `t .thm [.num `a 7] s1 (some (.letE `b s1 s1 (.bvar 0) true)) &&
          projects o `o .opaque [] (.const `a [u, .max (.succ .zero) u])
            (some (.proj `T 0 (.bvar 0))) &&
          projects q `q .quot [`u] (.sort (.imax u (.succ .zero))) none &&
          projects ty `T .induct [] s1 none &&
          projects mk `T.mk .ctor [] (.lit (.strVal "s")) none &&
          projects rc `T.rec .recursor [`u] (.app lam (.bvar 0)) none
      | _ => false),
    ("export: a block member named like its type, a missing or extra member, a non-natural " ++
        "mdata index, an integer beyond J's bound + a def height past 32 bits refuse (malformed)",
      fun _ =>
      let n := every.length + 1
      let tall := every[26]!.replace "\"regular\":3" "\"regular\":4294967296"
      refusal (rd (every.dropLast ++ [every.block 5])) == some (n, .malformed) &&
        refusal (rd ["{\"il\":1,\"succ\":0,\"x\":1}"]) == some (2, .malformed) &&
        refusal (rd ["{\"axiom\":{\"levelParams\":[],\"name\":0,\"type\":0}}"]) ==
          some (2, .malformed) &&
        refusal (rd ["{\"ie\":\"x\",\"mdata\":{}}"]) == some (2, .malformed) &&
        refusal (rd ["{\"ie\":9007199254740992,\"sort\":0}"]) == some (2, .malformed) &&
        refusal (rd (every.take 25 ++ [tall])) == some (27, .malformed)),
    ("export: lines — empty = no header, a final LF optional, an empty line refused at its line",
      fun _ =>
      let ended := fun (ls : List String) (tail : String) =>
        read Lean.githash Lean.versionString ("\n".intercalate (hdr :: ls) ++ tail).toUTF8
      refusal (read Lean.githash Lean.versionString .empty) == some (1, .malformed) &&
        refusal (read Lean.githash Lean.versionString "\n".toUTF8) == some (1, .malformed) &&
        refusal (ended tables "") == none &&
        refusal (ended tables "\n") == none &&
        refusal (ended (tables.take 2 ++ [""] ++ tables.drop 2) "\n") == some (4, .malformed) &&
        refusal (ended tables "\n\n") == some (7, .malformed)),
    ("export: dense profile — a skipped index refuses at its line (profile)", fun _ =>
      refusal (rd ["{\"in\":2,\"str\":{\"pre\":0,\"str\":\"a\"}}"]) == some (2, .profile)),
    ("export: an unbound reference refuses at its line (malformed)", fun _ =>
      refusal (rd ["{\"const\":{\"name\":5,\"us\":[]},\"ie\":0}"]) == some (2, .malformed)),
    ("export: a declaration declared twice refuses (malformed)", fun _ =>
      refusal (rd (tables ++ [axiomA, axiomA])) == some (8, .malformed)),
    ("export: mdata is outside the profile", fun _ =>
      refusal (rd (tables ++ ["{\"ie\":2,\"mdata\":{\"data\":{},\"expr\":0}}"])) ==
        some (7, .profile)),
    ("export: another Lean build's header is outside the profile; a header member more = malformed",
      fun _ =>
      refusal (rdWith (hdr "0000") tables) == some (1, .profile) &&
        refusal (rdWith ("{\"extra\":1," ++ (hdr).drop 1) tables) == some (1, .malformed)),
    ("export: a string over J's 64 KiB bound is outside the profile", fun _ =>
      refusal
          (rd
            (tables ++
              ["{\"ie\":2,\"strVal\":\"" ++ String.ofList (List.replicate 65537 'x') ++ "\"}"])) ==
        some (7, .profile)),
    ("export: natural literals — 0 + digits read, a leading zero, empty or non-digit refused",
      fun _ =>
      let lit := fun (s : String) =>
        rd
          (tables ++
            ["{\"ie\":2,\"natVal\":\"" ++ s ++ "\"}",
              "{\"axiom\":{\"isUnsafe\":false," ++ "\"levelParams\":[],\"name\":1,\"type\":2}}"])
      let typeOf := fun (r : Except Refusal (List Decl)) =>
        match r with
        | .ok [d] => some d.type
        | _ => none
      typeOf (lit "0") == some (.lit (.natVal 0)) &&
        typeOf (lit "120") == some (.lit (.natVal 120)) &&
        refusal (lit "012") == some (7, .malformed) &&
        refusal (lit "") == some (7, .malformed) &&
        refusal (lit "1a") == some (7, .malformed)),
    ("export: an unknown record + an unknown expression form refuse (malformed)", fun _ =>
      refusal (rd ["{\"zz\":1,\"yy\":2}"]) == some (2, .malformed) &&
        refusal (rd ["{\"ie\":0,\"zzz\":1}"]) == some (2, .malformed))]

end ExportR

namespace LibraryT

open FvdepCore.Library FvdepCore.Project

/-- `n` pseudo-random tokens over `alphabet`, each 1–8 characters (an LCG over `seed`). -/
def tokens (seed : UInt64) (n : Nat) (alphabet : List Char) : List String :=
  Id.run do
    let mut s := seed
    let mut out := #[]
    for _ in [0:n] do
      s := s * 6364136223846793005 + 1442695040888963407
      let len := (s >>> 33).toNat % 8 + 1
      let mut t := ""
      for _ in [0:len] do
        s := s * 6364136223846793005 + 1442695040888963407
        t := t.push (alphabet.getD ((s >>> 33).toNat % alphabet.length) 'x')
      out := out.push t
    return out.toList

def oidA : String := "8a86ca5622e1112a7e5df7e2d2e6dd63516d5640"

def oidB : String := "9e5aa9c65f9cbe28045f10463d324ee242412242"

/-- One `ls-tree -z -l` record as git 2.53 prints it (`%06o %s %s %7s\t%s\0`). -/
def rec (mode kind oid size path : String) : String :=
  mode ++ " " ++ kind ++ " " ++ oid ++ " " ++
    String.ofList (List.replicate (7 - size.length) ' ') ++
    size ++
    "\t" ++
    path ++
    "\x00"

def blob (path : String) (n : Nat := 3) : String := rec "100644" "blob" oidA (toString n) path

def dir (path : String) : String := rec "040000" "tree" oidB "-" path

/-- A minimal library listing: its required files + one module under `Fvdep`. -/
def library : List String :=
  [blob "Fvdep.lean", dir "Fvdep", blob "Fvdep/Registry.lean", blob "index.json",
    blob "lakefile.lean", blob "lean-toolchain"]

def tree (rs : List String) : Option (List TreeEntry) := parseTree (String.join rs).toUTF8

def plan (rs : List String) : Option (Except String (List Blob)) := (tree rs).map (planTree {})

def refused (r : Option (Except String (List Blob))) (needle : String) : Bool :=
  match r with
  | some (.error why) => (why.splitOn needle).length > 1
  | _ => false

def head : Head := ⟨oidA, "2026-11-20T08:00:00Z", String.ofList (List.replicate 64 'a')⟩

def cases (seed : UInt64) : List (String × (Unit → Bool)) :=
  [("library: the source — FVDEP_LIBRARY_URL unset or empty = the default", fun _ =>
      sourceOf none == defaultSource && sourceOf (some "") == defaultSource &&
        sourceOf (some "/srv/lib") == "/srv/lib"),
    ("library: git's URL rule + anchoring (a URL as written, a local path made absolute)", fun _ =>
      isUrl "https://h/p" && isUrl "file:///srv/lib" && isUrl "git@h:p" && !isUrl "/srv/lib" &&
        !isUrl "rel/lib" &&
        !isUrl "./a:b" &&
        anchor "/w" "rel" == "/w/rel" &&
        anchor "/" "rel" == "/rel" &&
        anchor "/w" "/abs" == "/abs" &&
        anchor "/w" "https://h/p" == "https://h/p" &&
        anchor "/w" "h:p" == "h:p"),
    ("library: redaction — userinfo → ***, a local path unchanged", fun _ =>
      redact ("https://u:" ++ "pw@h/p") == "https://***@h/p" &&
        redact "https://h/p" == "https://h/p" &&
        redact "ssh://u@h:22/p" == "ssh://***@h:22/p" &&
        redact "u@h:p" == "***@h:p" &&
        redact "/srv/a@b" == "/srv/a@b" &&
        redact ("https://u:" ++ "p@x@h/p") == "https://***@h/p" &&
        redact "https://h/a@b" == "https://h/a@b"),
    (s!"library: redaction — 150 generated credentials never reach the text", fun _ =>
      let alpha := "abcXYZ019-_.~!$&'()*+,;=%".toList
      (tokens seed 150 alpha).zip (tokens (seed + 1) 150 alpha) |>.all fun (u, pw) =>
        let r := redact ("https://" ++ u ++ ":" ++ pw ++ "secret" ++ "@host/path")
        r == "https://***@host/path" && (r.splitOn "secret").length == 1),
    ("library: head.json round trip; a changed byte, other spacing or schema = damaged", fun _ =>
      let b := headText head
      headOf b == some head && headOf ((b.toList.set 2 32).toByteArray) == none &&
        headOf (("{ " ++ String.fromUTF8! (b.extract 1 b.size)).toUTF8) == none &&
        headOf ((String.fromUTF8! b).replace "\"schema\":1" "\"schema\":2").toUTF8 == none &&
        headOf (headText { head with commit := oidA.toUpper }) == none &&
        headOf (headText { head with fetched := "2026-13-01T00:00:00Z" }) == none &&
        headOf (headText { head with source := String.ofList (List.replicate 63 'a') }) == none),
    ("library: ls-tree records read exactly (sizes, -, paths with TAB + LF)", fun _ =>
      match tree [blob "a\tb\nc" 103, dir "Fvdep"] with
      | some [x, y] =>
        x.kind == .blob && x.size == some 103 && x.path == "a\tb\nc" && y.kind == .tree &&
          y.size == none &&
          y.path == "Fvdep"
      | _ => false),
    ("library: ls-tree refusals — unterminated, padding, uppercase hex, a tree's size", fun _ =>
      (parseTree ((blob "a").toUTF8.extract 0 ((blob "a").utf8ByteSize - 1))).isNone &&
        (tree [(blob "a").replace "      3" "     3"]).isNone &&
        (tree [rec "100644" "blob" oidA.toUpper "3" "a"]).isNone &&
        (tree [rec "040000" "tree" oidB "5" "Fvdep"]).isNone &&
        tree [] == some []),
    ("library: the tree policy plans a library's blobs in listing order", fun _ =>
      match plan library with
      | some (.ok bs) =>
        bs.map (·.path) ==
          ["Fvdep.lean", "Fvdep/Registry.lean", "index.json", "lakefile.lean", "lean-toolchain"]
      | _ => false),
    ("library: the tree policy refuses a link, a submodule, a dot path, a misplaced root", fun _ =>
      refused (plan (library ++ [rec "120000" "blob" oidA "4" "Fvdep/l"])) "a link" &&
        refused (plan (library ++ [rec "160000" "commit" oidA "-" "Fvdep/s"])) "a submodule" &&
        refused (plan (library ++ [blob "Fvdep/.hidden"])) "unsafe path" &&
        refused (plan (library ++ [dir "index.json"])) "unexpected entry" &&
        refused (plan (library ++ [blob "README.md"])) "unexpected entry" &&
        refused (plan (library ++ [rec "100600" "blob" oidA "1" "Fvdep/m"])) "mode 100600"),
    ("library: the tree policy — a missing required file, the per-file cap", fun _ =>
      refused (plan (library.filter (· != blob "Fvdep/Registry.lean"))) "no fvdep library" &&
        refused (plan (library ++ [blob "Fvdep/big.lean" 1048577])) "size limits" &&
        refused ((tree library).map (planTree { entries := 3 })) "limit of 3 tree entries" &&
        refused ((tree library).map (planTree { depth := 1 })) "deeper than 1 components" &&
        refused ((tree library).map (planTree { pathBytes := 12 })) "over 12 bytes" &&
        refused ((tree library).map (planTree { pathTotal := 20 })) "limit of 20 path bytes"),
    ("library: batch replies read in plan order; a missing object or extra byte refuses", fun _ =>
      let x : Blob := ⟨"a", oidA.toUTF8.toList, 2⟩
      let y : Blob := ⟨"b", oidB.toUTF8.toList, 0⟩
      let reply := s!"{oidA} blob 2\x00hi\x00{oidB} blob 0\x00\x00"
      parseBatch [x, y] reply.toUTF8 == some ["hi".toUTF8, ByteArray.empty] &&
        (parseBatch [x, y] (reply ++ "x").toUTF8).isNone &&
        (parseBatch [x] s!"{oidA} missing\x00".toUTF8).isNone),
    ("library: toolchain — equal after trimming, else the interface §1 refusal", fun _ =>
      toolchainRefusal oidA "leanprover/lean4:v4.35.0\n" "leanprover/lean4:v4.35.0" == none &&
        match toolchainRefusal oidA "leanprover/lean4:v4.36.0" "leanprover/lean4:v4.35.0" with
        | some m => m.startsWith s!"Library commit {oidA} uses Lean leanprover/lean4:v4.36.0;"
        | none => false),
    ("library: selection — pin never falls back; the head falls back on transport alone", fun _ =>
      start (some oidA) true == .serve oidA && start (some oidA) false == .fetchPin oidA &&
        start none true == .fetchHead &&
        afterPin oidA (.transport "down") == .refuse "Fetch failed: down." &&
        afterHead (.valid head) (.transport "down") ==
          .serve oidA (some "Fetch failed: down. Last successful fetch: 2026-11-20T08:00:00Z.") &&
        afterHead .absent (.transport "down") ==
          .refuse "Fetch failed: down. Last successful fetch: never." &&
        afterHead (.valid head) (.received "fsck") == .refuse "Fetch failed: fsck." &&
        afterHead (.valid head) (.ok oidB) == .serve oidB none),
    ("project: --project decides alone; the nearest manifest decides; links never followed",
      fun _ =>
      selectProject (.explicit "/p" .file) == .project "/p" &&
        (match selectProject (.explicit "/p" .link) with
        | .refuse r => (r.splitOn "link").length > 1 && (r.splitOn "fvdep.toml").length > 1
        | _ => false) &&
        selectProject (.ancestors [("/a/b", .absent), ("/a", .file), ("/", .file)]) ==
          .project "/a" &&
        (match selectProject (.ancestors [("/a/b", .absent), ("/a", .special), ("/", .file)]) with
        | .refuse r => (r.splitOn "special").length > 1
        | _ => false) &&
        selectProject (.ancestors [("/a", .absent)]) == .none)]

/-- The committed `git-tree` seed (byte 0 = the fuzz mode) = git 2.53.0's real `ls-tree -r -t -l -z
--full-tree` output of this repository's library paths. -/
def ioCases : List (String × IO Bool) :=
  [("library: git 2.53.0's real listing of the library reads + plans (82 entries, 40 blobs)", do
      let b ← IO.FS.readBinFile "../tests/fuzz/git-tree/library-listing"
      match parseTree (b.extract 1 b.size) with
      | some es =>
        match planTree {} es with
        | .ok bs =>
          return es.length == 82 && bs.length == 40
        | .error _ =>
          return false
      | none =>
        return false)]

end LibraryT

/-! ## U5b W: the internal wire codec -/

namespace WireT

open FvdepCore.Protocol FvdepCore.Oracle.Wire Fvdep.Semver.Version.V1_0_0

/-- An LCG step: the next state + a draw below `m` (`m ≥ 1`). -/
def draw (s : UInt64) (m : Nat) : UInt64 × Nat :=
  let s := s * 6364136223846793005 + 1442695040888963407
  (s, (s >>> 33).toNat % m)

/-- `n` draws below `m`. -/
def draws (s : UInt64) (n m : Nat) : UInt64 × List Nat :=
  n.fold
    (fun _ _ (acc : UInt64 × List Nat) =>
      let (s', d) := draw acc.1 m
      (s', d :: acc.2))
    (s, [])

/-- Characters across UTF-8's 1–4 byte forms + the line's separators. -/
def chars : List Char := ['a', 'Z', '0', ' ', ':', '/', '.', '-', '\n', 'é', '中', '😀', '\x00']

def charsOf (s : UInt64) (n : Nat) : UInt64 × List Char :=
  let (s, ds) := draws s n chars.length
  (s, ds.map fun d => chars.getD d 'a')

/-- A generated value of type `t` (atypical shapes included: empty lists + identifiers, 0, a
negative int, large numbers). -/
def valOf (s : UInt64) : Ty → UInt64 × Val
  | .bytes =>
    let (s, n) := draw s 5
    let (s, ds) := draws s n 256
    (s, .bytes (ds.map (·.toUInt8)))
  | .text =>
    let (s, n) := draw s 5
    let (s, cs) := charsOf s n
    (s, .text cs)
  | .utf16 =>
    let (s, n) := draw s 4
    let (s, ds) := draws s n 65536
    (s, .utf16 (ds.map (·.toUInt16)))
  | .nat =>
    let (s, d) := draw s 4
    let (s, n) := draw s 1000000007
    (s, .nat (if d == 0 then 0 else n * 10 ^ (d * 7)))
  | .int =>
    let (s, d) := draw s 3
    let (s, n) := draw s 1000000007
    (s, .int (if d == 0 then 0 else if d == 1 then -(n : Int) - 1 else n))
  | .ordering =>
    let (s, d) := draw s 3
    (s, .ordering (if d == 0 then .lt else if d == 1 then .eq else .gt))
  | .version =>
    let (s, a) := draw s 100
    let (s, np) := draw s 3
    let (s, pre) :=
      np.fold
        (fun _ _ (acc : UInt64 × List Ident) =>
          let (s, k) := draw acc.1 2
          let (s, n) := draw s 30
          let (s, cs) := charsOf s (n % 3)
          (s, (if k == 0 then .num n else .alnum cs) :: acc.2))
        (s, [])
    let (s, nb) := draw s 3
    let (s, build) :=
      nb.fold
        (fun _ _ (acc : UInt64 × List (List Char)) =>
          let (s, cs) := charsOf acc.1 (acc.2.length % 3)
          (s, cs :: acc.2))
        (s, [])
    (s, .version ⟨a, a * 7, 0, pre, build⟩)

def tys : List Ty := [.bytes, .text, .utf16, .nat, .int, .ordering, .version]

/-- `n` generated argument lists (1–3 values of drawn types). -/
def argLists (seed : UInt64) (n : Nat) : List (List Val) :=
  (n.fold
      (fun _ _ (acc : UInt64 × List (List Val)) =>
        let (s, k) := draw acc.1 3
        let (s, xs) :=
          (k + 1).fold
            (fun _ _ (b : UInt64 × List Val) =>
              let (s, t) := draw b.1 tys.length
              let (s, v) := valOf s (tys.getD t .nat)
              (s, v :: b.2))
            (s, [])
        (s, xs :: acc.2))
      (seed, [])).2

def decodes (ts : List Ty) (s : String) (xs : List Val) : Bool :=
  match decodeArgs ts s with
  | some ys => ys == xs
  | none => false

def refused (t : Ty) (s : String) : Bool := (decodeArgs [t] s).isNone

def cases (seed : UInt64) : List (String × (Unit → Bool)) :=
  [("wire: 400 generated argument lists round-trip (encodeArgs → decodeArgs)", fun _ =>
      (argLists seed 400).all fun xs => decodes (xs.map Val.ty) (encodeArgs xs) xs),
    ("wire: tokens are canonical — lowercase hex, decimals without a leading zero, no -0", fun _ =>
      encodeArgs [.bytes [0xAB, 0], .nat 0, .int (-5), .int 0, .utf16 [0xD800]] ==
          "b:ab00 n:0 i:-5 i:0 u:d800" &&
        refused .bytes "b:AB" &&
        refused .bytes "b:abc" &&
        refused .nat "n:01" &&
        refused .nat "n:" &&
        refused .int "i:-0" &&
        refused .int "i:-" &&
        refused .int "i:+1" &&
        refused .utf16 "u:d80" &&
        refused .ordering "o:LT" &&
        refused .nat "x:1"),
    ("wire: text = hex of UTF-8 — invalid UTF-8 + surrogate encodings refused", fun _ =>
      encodeArgs [.text ['é']] == "t:c3a9" && refused .text "t:ff" && refused .text "t:eda080" &&
        refused .text "t:c0af" &&
        decodes [.text] "t:" [.text []]),
    ("wire: versions — empty lists, an empty identifier keeps its tag, the three parts exact",
      fun _ =>
      let v : Version := ⟨1, 0, 2, [.num 0, .alnum []], [[]]⟩
      encodeArgs [.version v] == "v:1.0.2/n0.a/x" &&
        decodes [.version] "v:1.0.2//" [.version ⟨1, 0, 2, [], []⟩] &&
        decodes [.version] "v:1.0.2/n0.a/x" [.version v] &&
        refused .version "v:1.0/n0/" &&
        refused .version "v:1.0.2/n/" &&
        refused .version "v:1.0.2/n01/" &&
        refused .version "v:1.0.2/b/" &&
        refused .version "v:1.0.2//y" &&
        refused .version "v:1.0.2/./" &&
        refused .version "v:1.0.2///"),
    ("wire: argument count + types — a missing, extra or mistyped token refused", fun _ =>
      (decodeArgs [.nat, .nat] "n:1").isNone && (decodeArgs [.nat] "n:1 n:2").isNone &&
        (decodeArgs [.nat] "t:31").isNone &&
        (decodeArgs [.nat] "n:1 ").isNone &&
        (decodeArgs [.nat] " n:1").isNone &&
        (decodeArgs [] "").isSome &&
        (decodeArgs [] "n:1").isNone),
    ("wire: results — ok <token> for a value, err for an optional none alone", fun _ =>
      parseResult (.plain .nat) (printResult (.nat 7)) == some (.ok (.nat 7)) &&
        parseResult (.option .nat) printNone == some .err &&
        parseResult (.plain .nat) printNone == none &&
        parseResult (.plain .nat) "ok n:7 " == none &&
        parseResult (.option .text) (printResult (.nat 7)) == none &&
        (argLists seed 200).all fun xs =>
          xs.all fun v => parseResult (.plain v.ty) (printResult v) == some (.ok v)),
    ("wire: native bridge — ofVal ∘ toVal = some, another type = none", fun _ =>
      Native.ofVal (Native.toVal ([1, 2] : List UInt8)) == some ([1, 2] : List UInt8) &&
        (Native.ofVal (Native.toVal (ByteArray.mk #[3])) : Option ByteArray).map (·.toList) ==
          some [3] &&
        Native.ofVal (Native.toVal (-3 : Int)) == some (-3 : Int) &&
        (Native.ofVal (Val.nat 1) : Option Int) == none &&
        (Native.ofVal (Val.text ['a']) : Option (List UInt8)) == none &&
        Native.ty (List UInt16) == .utf16 &&
        Native.ty Version == .version),
    ("wire: serve — arguments through ofVal in order, the result through printResult", fun _ =>
      answer (fun (a b : Nat) => a - b) "n:5 n:2" == "ok n:3" &&
        answer (fun (a : Int) (b : List Char) (c : Ordering) => (a, b, c).1) "i:-1 t:61 o:gt" ==
          "ok i:-1" &&
        answer (fun (s : List Char) => if s.isEmpty then none else some s) "t:" == "err" &&
        answer (fun (s : List Char) => if s.isEmpty then none else some s) "t:61" == "ok t:61" &&
        answer (fun (b : ByteArray) => b.size) "b:00ff" == "ok n:2" &&
        answer (fun (a b : Nat) => a + b) "n:1" == "malformed" &&
        Serve.args (Nat → List Char → Option Version) == [.nat, .text] &&
        Serve.rty (Nat → List Char → Option Version) == .option .version),
    ("merge: refusals stay where they stand, each valid request takes the next reply line", fun _ =>
      let rt : RTy := .plain .nat
      let merged (reqs : List FvdepCore.Oracle.Req) (b : String) (out : List Reply) : Bool :=
        match FvdepCore.Oracle.merge rt reqs b.toUTF8 with
        | Except.ok rs => rs == out
        | Except.error _ => false
      merged [.valid, .valid] "ok n:3\nok n:5\n" [Reply.ok (.nat 3), Reply.ok (.nat 5)] &&
        merged [.invalid "x", .valid, .invalid "y"] "ok n:1\n"
          [Reply.invalid "x", Reply.ok (.nat 1), Reply.invalid "y"] &&
        merged [.invalid "x"] "" [Reply.invalid "x"] &&
        merged [] "" []),
    ("merge: a missing, extra, unterminated, malformed, mistyped or non-UTF-8 line → its rank",
      fun _ =>
      let rt : RTy := .plain .nat
      let err (reqs : List FvdepCore.Oracle.Req) (b : ByteArray) (k : Nat) : Bool :=
        match FvdepCore.Oracle.merge rt reqs b with
        | Except.ok _ => false
        | Except.error j => j == k
      err [.valid, .valid] "ok n:1\n".toUTF8 2 && err [.valid] "ok n:1\nok n:2\n".toUTF8 2 &&
        err [.valid] "ok n:1".toUTF8 1 &&
        err [.valid] "ok x:1\n".toUTF8 1 &&
        err [.valid] "ok t:61\n".toUTF8 1 &&
        err [.valid] ⟨#[0xff, 0x0a]⟩ 1 &&
        err [.invalid "x"] "ok n:1\n".toUTF8 1 &&
        err [.valid, .invalid "x", .valid] "ok n:1\nerr\n".toUTF8 2)]

end WireT

/-! ## U5b E + V + O: entry resolution, staging, the driver text, the oracle plan -/

namespace OracleT

open Lean FvdepCore FvdepCore.Ids FvdepCore.Protocol FvdepCore.Oracle FvdepCore.Index

def op (s : String) : Option (ModuleId × EntryVersion) :=
  match Target.parse s with
  | some (.op m v) => some (m, v)
  | _ => none

def trialM : ModuleId × EntryVersion := (op "trial.weight_mix@1.0.0").getD (Core.modId, ⟨0, 0, 0⟩)

def specName : Name := `Fvdep.Trial.WeightMix.V1_0_0.foldPulse

/-- An entry value as Lean elaborates it (`Module.mk id version spec [] none none`). -/
def entryVal (id ver : String) (spec : Name) : Expr :=
  mkAppN (.const ``Fvdep.Registry.Types.V1.Module.mk [])
    #[toExpr id, toExpr ver, toExpr spec, toExpr ([] : List Name), toExpr (none : Option Name),
      toExpr (none : Option String)]

def entryDecl (v : Expr) (kind : Export.Kind := .defn) : Export.Decl :=
  ⟨`Fvdep.Registry.Trial.WeightMix.V1_0_0.entry, kind, [], .sort .zero, some v⟩

def mods : List Name := [`Fvdep.Registry.Trial.WeightMix.V1_0_0, `Fvdep.Trial.WeightMix.V1_0_0]

def entryOk (r : Except Why Name) (n : Name) : Bool :=
  match r with
  | .ok x => x == n
  | .error _ => false

def entryWhy (r : Except Why Name) :
    Option Why := match r with
  | .ok _ => none
  | .error w => some w

def isIncons : Option Why → Bool
  | some (.inconsistent _) => true
  | _ => false

/-- The effect kinds of a plan run whose effects get `answer` (fuel-bounded) + its result. -/
def trace (answer : Eff → Response) : Nat → Plan UInt32 → List String × Option UInt32
  | 0, _ => ([], none)
  | _ + 1, .pure a => ([], some a)
  | n + 1, .step e k =>
    let name :=
      match e with
      | .project _ => "project"
      | .manifest _ => "manifest"
      | .parse _ => "parse"
      | .snapshot _ _ => "snapshot"
      | .closure _ _ => "closure"
      | .view _ _ => "view"
      | .leanexport _ _ _ => "export"
      | .stdin _ => "stdin"
      | .evaluate _ _ _ _ => "evaluate"
      | .outBytes _ => "out"
      | .err _ => "err"
      | .out _ => "stdout"
      | _ => "other"
    let (es, r) := trace answer n (k (answer e))
    (name :: es, r)

def tc : ByteArray := (FvdepCore.Index.Command.toolchain ++ "\n").toUTF8

def snap (index : ByteArray) (notice : Option String := none) : Snap :=
  ⟨"0123456789abcdef0123456789abcdef01234567", "/t", notice, tc, index⟩

def emptyIndex : ByteArray :=
  ("{\"notices\":[],\"operations\":[],\"removed\":[],\"schema\":1,\"toolchain\":\"" ++
      FvdepCore.Index.Command.toolchain ++
      "\"}\n").toUTF8

def answering (s : Snap) (seen : FvdepCore.Project.Seen := .ancestors []) : Eff → Response
  | .project _ => .project seen
  | .snapshot _ _ => .snapshot (.ok s)
  | .err _ => .done
  | _ => .done

def runOracle (t : String) (answer : Eff → Response) : List String × Option UInt32 :=
  match Target.parse t with
  | some tgt => trace answer 50 (FvdepCore.Oracle.Command.plan (fun _ => "") {} tgt none)
  | none => ([], none)

def cases : List (String × (Unit → Bool)) :=
  [("oracle: target grammar — an operation needs its version; a profile is <eco>:<pkg>@<ver>",
      fun _ =>
      ["trial.weight_mix@1.0.0", "base64.decode_url@12.0.3"].all (fun t => (op t).isSome) &&
        ["trial.weight_mix", "TRIAL.weight_mix@1.0.0", "trial.weight__mix@1.0.0",
              "trial.0mix@1.0.0", "trial.weight_0mix@1.0.0", "trial.weight_mix@01.0.0",
              "trial.weight_mix@1.0.0-rc.1", "trial.weight_mix@1.0.0@2.0.0", "@1.0.0", "",
              "npm:@1.0", "npm:pkg@", ":pkg@1", "NPM:x@1", "npm:a b@1"].all
          (fun t => (Target.parse t).isNone) &&
        ["npm:base64-js@1.5.1", "npm:@scope/name@2.0.0", "crates:base64@0.22.1"].all fun t =>
          Target.parse t == some (.profile t)),
    ("oracle: E5 — the expanded size counts each let value at every use, stops past the budget",
      fun _ =>
      let leaf : Expr := .lit (.natVal 1)
      let app := Expr.app leaf leaf
      let twice : Expr := .letE `x (.sort .zero) app (.app (.bvar 0) (.bvar 0)) false
      FvdepCore.Oracle.within 3 app [] == some 0 && FvdepCore.Oracle.within 2 app [] == none &&
        FvdepCore.Oracle.within 10 twice [] == some 0 &&
        FvdepCore.Oracle.within 9 twice [] == none &&
        FvdepCore.Oracle.within 1 (.bvar 7) [] == some 0),
    ("oracle: E3 — the entry's record names the target + S.<fn> inside M's closure", fun _ =>
      let (m, v) := trialM
      entryOk (entrySpec 1000 m v mods [entryDecl (entryVal "trial.weight_mix" "1.0.0" specName)])
          specName &&
        entryWhy
            (entrySpec 3 m v mods [entryDecl (entryVal "trial.weight_mix" "1.0.0" specName)]) ==
          some .budget &&
        isIncons
          (entryWhy
            (entrySpec 1000 m v mods [entryDecl (entryVal "trial.other" "1.0.0" specName)])) &&
        isIncons
          (entryWhy
            (entrySpec 1000 m v mods [entryDecl (entryVal "trial.weight_mix" "4.0.0" specName)])) &&
        isIncons
          (entryWhy
            (entrySpec 1000 m v mods
              [entryDecl (entryVal "trial.weight_mix" "1.0.0" `Fvdep.Trial.Other.V1_0_0.f)])) &&
        isIncons
          (entryWhy
            (entrySpec 1000 m v mods
              [entryDecl (entryVal "trial.weight_mix" "1.0.0" specName) .«opaque»])) &&
        isIncons
          (entryWhy
            (entrySpec 1000 m v [`Fvdep.Registry.Trial.WeightMix.V1_0_0]
              [entryDecl (entryVal "trial.weight_mix" "1.0.0" specName)])) &&
        isIncons (entryWhy (entrySpec 1000 m v mods []))),
    ("oracle: E4 — the spec's type through sigOf; a non-definition or another type refused",
      fun _ =>
      let int : Expr := .const ``Int []
      let ty : Expr :=
        .forallE `a int (.forallE `b int (.app (.const ``Option [.zero]) int) .default) .implicit
      let d (k : Export.Kind) (t : Expr) : Export.Decl := ⟨specName, k, [], t, none⟩
      (match specSig specName [d .defn ty] with
        | .ok sig => sig == ⟨"foldPulse", [.int, .int], .option .int⟩
        | .error _ => false) &&
        (match specSig specName [d .defn (.const ``Bool [])] with
        | .error .cannotCarry => true
        | _ => false) &&
        (match specSig specName [d .thm ty] with
        | .error (.inconsistent _) => true
        | _ => false)),
    ("oracle: E2 — a closure module without its source is inconsistent, even under a digest " ++
        "of the rest",
      fun _ =>
      let h (b : ByteArray) : String := toString b.size
      let i : IndexFile := ⟨FvdepCore.Index.Command.toolchain, [], [], []⟩
      let M : Name := `Fvdep.Registry.Trial.WeightMix.V1_0_0
      let srcM : Src :=
        ⟨"Fvdep.Registry.Trial.WeightMix.V1_0_0", "x".toUTF8, ["Fvdep.Trial.Missing"]⟩
      let srcN : Src := ⟨"Fvdep.Trial.Missing", "y".toUTF8, []⟩
      let part : String := h (FvdepCore.Index.Assemble.entryFrame (factsOf [srcM]) M)
      let whole : String := h (FvdepCore.Index.Assemble.entryFrame (factsOf [srcM, srcN]) M)
      let o (d : String) : Operation :=
        ⟨(op "trial.weight_mix@1.0.0").map (·.1) |>.getD Core.modId, ⟨1, 0, 0⟩, d, [], none⟩
      (coherence h FvdepCore.Index.Command.toolchain i (o part) M [srcM]).isSome &&
        coherence h FvdepCore.Index.Command.toolchain i (o whole) M [srcM, srcN] == none &&
        (coherence h FvdepCore.Index.Command.toolchain i (o whole) M [srcN]).isSome),
    ("oracle: V2 — lines by offsets (CRLF kept, a final fragment counts), staging + budgets",
      fun _ =>
      let sig : Sig := ⟨"f", [.nat], .plain .nat⟩
      let b := "{\"op\":\"f\",\"args\":[1]}\r\n\nx\n{\"op\":\"f\",\"args\":[2]}".toUTF8
      (match FvdepCore.Oracle.Command.stageFrom {} sig b 0 {} with
        | .ok st =>
          st.reqs.reverse.map (· == .valid) == [true, false, false, true] &&
            st.staged == "n:1\nn:2\n" &&
            st.stagedBytes == 8
        | .error _ => false) &&
        (match FvdepCore.Oracle.Command.stageFrom { stagingBytes := 7 } sig b 0 {} with
        | .error .staging => true
        | _ => false) &&
        (match FvdepCore.Oracle.Command.stageFrom { batchBytes := 20 } sig b 0 {} with
        | .error .batch => true
        | _ => false)),
    ("oracle: the driver = its imports + W's two texts after their import lines + main", fun _ =>
      let d := FvdepCore.Oracle.Driver.driverText `Fvdep.Registry.Trial.WeightMix.V1_0_0 specName
      d.startsWith
          ("import «Fvdep».«Registry».«Trial».«WeightMix».«V1_0_0»\n" ++
            "import Fvdep.Semver.Version.V1_0_0\n") &&
        (d.splitOn "\nimport ").length == 2 &&
        (d.splitOn "namespace FvdepCore.Oracle.Wire").length == 2 &&
        (d.splitOn
              ("(«FvdepCore».«Oracle».«Wire».«answer» " ++
                "(@«Fvdep».«Trial».«WeightMix».«V1_0_0».«foldPulse»)")).length ==
          2),
    ("oracle: an unknown target, a profile, a bad index → one stderr line, exit 2, stdin unread",
      fun _ =>
      let s := snap emptyIndex
      runOracle "trial.weight_mix@1.0.0" (answering s) ==
          (["project", "snapshot", "err"], some 2) &&
        runOracle "npm:x@1" (answering s) == (["project", "snapshot", "err"], some 2) &&
        runOracle "trial.weight_mix@1.0.0" (answering (snap "{bad".toUTF8)) ==
          (["project", "snapshot", "err"], some 2)),
    ("oracle: a served head's notice goes first; another toolchain is refused before index.json",
      fun _ =>
      runOracle "a.b@1.0.0" (answering (snap emptyIndex (some "Fetch failed: x."))) ==
          (["project", "snapshot", "err", "err"], some 2) &&
        runOracle "a.b@1.0.0" (answering { snap emptyIndex with toolchain := "x".toUTF8 }) ==
          (["project", "snapshot", "err"], some 2)),
    ("oracle: a project's manifest is read + parsed before the snapshot; a refusal stops there",
      fun _ =>
      let ans : Eff → Response
        | .project _ => .project (.ancestors [("/p", .file)])
        | .manifest _ => .manifest (.bytes "schema = [\n".toUTF8)
        | .parse _ => .parse (.error (.syntax 1 9 "x"))
        | _ => .done
      runOracle "a.b@1.0.0" ans == (["project", "manifest", "parse", "err"], some 2))]

/-- Q4: the embedded list = W0's two modules, each text = its file's bytes as built (a stale
embedding fails; the ledger's `StepSource` reads the same list). -/
def ioCases : List (String × IO Bool) :=
  [("oracle: Q4 — the driver embeds Protocol/Types.lean + Oracle/Wire.lean exactly", do
      let es := FvdepCore.Oracle.Driver.embedded
      let same ←
        es.allM fun m => do
            return m.2 == (← IO.FS.readFile ⟨(m.1.toString.replace "." "/") ++ ".lean"⟩)
      return same && es.map (·.1) == [`FvdepCore.Protocol.Types, `FvdepCore.Oracle.Wire])]

end OracleT

/-! ## U5b L2: the library store + git (residues `git`, `library-store`) -/

namespace LibraryR

open FvdepCore.Library FvdepCore.Project

/-- git 2.53.0's lines measured per class (U5b-L2: `tools/vflab-run bash tools/git-probe.sh`). -/
def transportLines : List String :=
  ["fatal: '/w/gone' does not appear to be a git repository",
    "fatal: Could not read from remote repository.",
    "fatal: couldn't find remote ref refs/heads/main",
    "fatal: unable to access 'https://nonexistent.invalid/x.git/': Could not resolve host: " ++
      "nonexistent.invalid",
    "fatal: unable to access 'https://127.0.0.1:1/x.git/': Failed to connect to 127.0.0.1 port " ++
      "1 after 0 ms: Could not connect to server",
    "ssh: Could not resolve hostname nonexistent.invalid: Name or service not known\r",
    "ssh: connect to host 127.0.0.1 port 1: Connection refused\r",
    "fatal: unable to look up nonexistent.invalid (port 9418) (Name or service not known)",
    "fatal: unable to connect to 127.0.0.1:", "fatal: unable to get password from user"]

def receivedLines : List String :=
  ["error: object 10b02062df2d8cd0581e07dfafa73e829b0e98d8: badFilemode: contains bad file modes",
    "fatal: fsck error in packed object", "fatal: index-pack failed",
    "fatal: remote error: upload-pack: not our ref 0123456789abcdef0123456789abcdef01234567",
    "remote: fatal: '/w/gone' does not appear to be a git repository",
    "fatal: the remote end hung up unexpectedly", "fatal: early EOF", ""]

def errIs {α : Type} (r : Except String α) (msg : String) : Bool :=
  match r with
  | .error e => e == msg
  | .ok _ => false

def entry (path : String) (dir : Bool := false) : TreeEntry :=
  if dir then ⟨modeTree, .tree, List.replicate 40 98, none, path⟩
  else ⟨modeFile, .blob, List.replicate 40 97, some 1, path⟩

def cases (seed : UInt64) : List (String × (Unit → Bool)) :=
  [("library: transport = a line git prints before any object arrives; the rest + server text " ++
        "never",
      fun _ =>
      transportLines.all transportLine && !receivedLines.any transportLine &&
        transport ("x\n".toUTF8 ++ (transportLines.headD "").toUTF8) &&
        !transport ("\n".intercalate receivedLines).toUTF8),
    ("library: the first nonblank stderr line, CR dropped, scrubbed + escaped (§1)", fun _ =>
      firstLine "/s" "\n  \nfatal: x\r\nsecond\n".toUTF8 == some "fatal: x" &&
        firstLine "/s" "\x1b[2Jboom\tz".toUTF8 == some "\\u001B[2Jboom\\tz" &&
        firstLine "/s" " \n\n".toUTF8 == none),
    ("library: a source's userinfo never reaches a diagnostic (its spelling redacted, each copy " ++
        "masked)",
      fun _ =>
      let src := "file://user:" ++ "pw@h/x"
      scrub src s!"fatal: '{src}' does not appear" == "fatal: 'file://***@h/x' does not appear" &&
        scrub src ("token user:" ++ "pw here") == "token *** here" &&
        scrub "/local/a@b" "at /local/a@b" == "at /local/a@b" &&
        userinfo ("u@h:" ++ "p") == some "u" &&
        userinfo "https://h/p" == none &&
        (LibraryT.tokens seed 200 "ab:x".toList).all fun t =>
          let u := t ++ ":" ++ t
          let s := "https://" ++ u ++ "@h/p"
          ((scrub s s!"fatal: '{s}' with {u} and {s}").splitOn u).length == 1),
    ("library: git's environment — L3's eight names, HOME = the private repository; SSH keeps " ++
        "the caller's HOME + agent",
      fun _ =>
      gitEnv "/src" "/r.git" (some "/bin") (some "/home") (some "/sock") ==
          ["PATH=/bin", "LC_ALL=C", "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_TERMINAL_PROMPT=0", "GIT_ASKPASS=", "SSH_ASKPASS=", "HOME=/r.git"] &&
        gitEnv "h:p" "/r.git" none (some "/home") (some "/sock") ==
          ["LC_ALL=C", "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_TERMINAL_PROMPT=0", "GIT_ASKPASS=", "SSH_ASKPASS=", "HOME=/home",
            "SSH_AUTH_SOCK=/sock"] &&
        isSsh "ssh://h/p" &&
        isSsh "u@h:p" &&
        isSsh "git+ssh://h/p" &&
        !isSsh "https://h/p" &&
        !isSsh "file:///p" &&
        !isSsh "/p"),
    ("library: L3's fetch argv — each config its own element, the source + refspec last", fun _ =>
      let a := fetchArgs "/r.git" "/src" none
      a.take 28 == fetchConfig.flatMap (fun c => ["-c", c]) &&
        a.drop 28 ==
          ["-C", "/r.git", "fetch", "--depth=1", "--atomic", "--no-tags", "--no-prune",
            "--no-recurse-submodules", "--no-auto-maintenance", "--no-write-commit-graph",
            "--no-write-fetch-head", "--refmap=", "--", "/src",
            "+refs/heads/main:refs/fvdep/head"] &&
        (fetchArgs "/r.git" "/src" (some "ab")).getLast? == some "+ab:refs/fvdep/pin" &&
        initArgs "/r.git" == ["init", "--bare", "-q", "--template=", "/r.git"] &&
        (subArgs "/r" "c" "Fvdep").getLast? == some "Fvdep" &&
        !((topArgs "/r" "c" ++ subArgs "/r" "c" "Fvdep" ++ batchArgs "/r" ++ typeArgs "/r" "x" ++
                revArgs "/r" "x").any
            fun x => x == "fetch" || x == "init")),
    ("library: the listings combine into one entry list (each root directory once)", fun _ =>
      let top := [entry "Fvdep" true, entry "index.json", entry "FvdepProofs" true]
      let fv := [entry "Fvdep" true, entry "Fvdep/A.lean"]
      combine top [("Fvdep", fv), ("FvdepProofs", [entry "FvdepProofs" true])] ==
          [entry "Fvdep" true, entry "Fvdep/A.lean", entry "index.json",
            entry "FvdepProofs" true] &&
        combine [entry "Fvdep"] [("Fvdep", fv)] == [entry "Fvdep"]),
    ("library: path bytes counted over every printed record — at the cap accepted, one byte " ++
        "over refused at that record",
      fun _ =>
      let caps : Caps := { pathTotal := 12 }
      listedRefusal caps [entry "Fvdep" true, entry "Fvdep" true, entry "ab"] == none &&
        listedRefusal caps [entry "Fvdep" true, entry "Fvdep" true, entry "abc"] ==
          some "exceeds the limit of 12 path bytes at abc"),
    ("library: --limit names (fetchSeconds, lockSeconds, gitBytes, treeEntries, snapshotBytes)",
      fun _ =>
      let l : Limits := {}
      (l.set "fetchSeconds" 2).map (·.fetchSeconds) == some 2 &&
        (l.set "lockSeconds" 1).map (·.lockSeconds) == some 1 &&
        (l.set "gitBytes" 192).map (·.gitBytes) == some 192 &&
        (l.set "treeEntries" 9).map (·.caps.entries) == some 9 &&
        (l.set "snapshotBytes" 7).map (·.caps.totalBytes) == some 7 &&
        l.set "pathBytes" 1 == none),
    ("library: cat-file's requests + the reply length parseBatch accepts", fun _ =>
      let plan : List Blob := [⟨"a", [97, 98], 3⟩, ⟨"b", [99], 0⟩]
      (batchInput plan).toList == [97, 98, 0, 99, 0] &&
        batchBytes plan == (batchHeader [97, 98] 3).length + 4 + (batchHeader [99] 0).length + 1),
    ("library: UTC text of a second count (epoch, leap day, year ends) + Doc.isUtc on " ++
        "generated counts",
      fun _ =>
      utcText 0 == "1970-01-01T00:00:00Z" && utcText 951782400 == "2000-02-29T00:00:00Z" &&
        utcText 1767225599 == "2025-12-31T23:59:59Z" &&
        utcText 4107542400 == "2100-03-01T00:00:00Z" &&
        utcText 253402300799 == "9999-12-31T23:59:59Z" &&
        (List.range 300).all fun i =>
          FvdepCore.Doc.isUtc (utcText ((seed.toNat * (i + 7919)) % 253402300800))),
    ("library: head.json read back — a record of this store's key, else damaged (decoded, " ++
        "another source)",
      fun _ =>
      let k := String.ofList (List.replicate 64 'a')
      let h : Head := ⟨String.ofList (List.replicate 40 'c'), "2026-11-20T08:00:00Z", k⟩
      (match recordOf k (headText h) with
        | .ok h' => h' == h
        | .error _ => false) &&
        errIs (recordOf (String.ofList (List.replicate 64 'b')) (headText h))
          "head.json names another source" &&
        errIs (recordOf k "{".toUTF8) "head.json is no head record")]

/-- `git` with a neutral configuration (no user or system config, an identity, no hooks). -/
def git (repo : System.FilePath) (args : Array String) : IO String := do
  let o ←
    IO.Process.output
        { cmd := "git"
          args :=
            #["-C", repo.toString, "-c", "user.name=t", "-c", "user.email=t@t.invalid", "-c",
                "core.hooksPath=/dev/null", "-c", "commit.gpgSign=false"] ++
              args
          env := #[("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_NOSYSTEM", some "1")] }
  unless o.exitCode == 0 do
    throw (IO.userError s!"git {args}: {o.stderr}")
  return o.stdout

def commitAll (src : System.FilePath) (msg : String) : IO String := do
  discard <| git src #["add", "-A"]
  discard <| git src #["commit", "-qm", msg]
  return FvdepCore.Index.Assemble.trimText (← git src #["rev-parse", "HEAD"])

/-- A fixture library at `src`: the required files + a file outside the roots (`first`), then one
more module (`second`). -/
def library (src : System.FilePath) : IO (String × String) := do
  IO.FS.createDirAll src
  discard <| git src #["init", "-q", "-b", "main"]
  Snapshot.put src "lakefile.lean" "-- fixture\n".toUTF8
  Snapshot.put src "lean-toolchain" (FvdepCore.Index.Command.toolchain ++ "\n").toUTF8
  Snapshot.put src "index.json" "{}\n".toUTF8
  Snapshot.put src "Fvdep.lean" "import Fvdep.Registry\n".toUTF8
  Snapshot.put src "Fvdep/Registry.lean" "-- registry\n".toUTF8
  Snapshot.put src "outside.txt" "not a root\n".toUTF8
  let first ← commitAll src "one"
  Snapshot.put src "Fvdep/Second.lean" "-- second\n".toUTF8
  return (first, ← commitAll src "two")

def withTmp (f : System.FilePath → IO Bool) : IO Bool := do
  let d ← IO.FS.createTempDir
  try
    f d
  finally
    Snapshot.rmTree d

def store (d src : System.FilePath) (l : Limits := {}) (program := "git") :
    IO FvdepIO.Library.Store := FvdepIO.Library.Store.of (d / "cache") src.toString l program

/-- An executable shell script. -/
def script (path : System.FilePath) (body : String) : IO Unit := do
  IO.FS.writeFile path ("#!/bin/sh\n" ++ body)
  IO.setAccessRights path
      { user := { read := true, write := true, execution := true }
        group := { read := true, execution := true } }

def mode (p : System.FilePath) : IO String := do
  return FvdepCore.Index.Assemble.trimText
      (← IO.Process.output { cmd := "stat", args := #["-c", "%a", p.toString] }).stdout

def bytesOf (p : System.FilePath) : IO (List UInt8) := do
  return (← IO.FS.readBinFile p).toList

def isError (r : Except String FvdepIO.Library.Served) (needle : String) : Bool :=
  match r with
  | .error e => (e.splitOn needle).length > 1
  | .ok _ => false

def libraryFiles : List String :=
  ["lakefile.lean", "lean-toolchain", "index.json", "Fvdep.lean", "Fvdep/Registry.lean",
    "Fvdep/Second.lean"]

def ioCases : List (String × IO Bool) :=
  [("spawn: killGroup refuses 0, 1, a value read as negative + the caller's own group (EINVAL; " ++
        "a group leader by setsid: a job's PID namespace shows the caller's group as 0)",
      do
      let dev := (← IO.currentDir) / ".lake" / "build" / "bin" / "fvdep-dev"
      let o ←
        IO.Process.output
            { cmd := "setsid", args := #["-w", dev.toString, "library", "killgroup", "self"] }
      return (← FvdepIO.Git.killGroup 0 0) matches .error 22 &&
          (← FvdepIO.Git.killGroup 1 0) matches .error 22 &&
          (← FvdepIO.Git.killGroup 0x80000000 0) matches .error 22 &&
          o.stdout == "refused 22\n"),
    ("library: a head fetch publishes the roots' blobs (0644) + `.complete`, records the head, " ++
        "removes its temps",
      withTmp fun d => do
        let src := d / "src"
        let (_, second) ← library src
        let s ← store d src
        match ← FvdepIO.Library.snapshot s none with
        | .error _ =>
          return false
        | .ok sv =>
          let same ←
            libraryFiles.allM fun (f : String) => do
                let shown ← git src #["show", s!"{second}:{f}"]
                return (← bytesOf (sv.tree / f)) == shown.toUTF8.toList
          let modes ← libraryFiles.allM fun (f : String) => return (← mode (sv.tree / f)) == "644"
          let head := recordOf s.key (← IO.FS.readBinFile (s.dir / "head.json"))
          return sv.commit == second && sv.notice.isNone && same && modes &&
              !(← (sv.tree / "outside.txt").pathExists) &&
              (← FvdepIO.Library.kind (sv.tree / ".complete")) matches some .file &&
              (match head with
              | .ok h => h.commit == second && FvdepCore.Doc.isUtc h.fetched
              | .error _ => false) &&
              (← s.tmp.readDir).isEmpty),
    ("library: a pin's tree served (head.json untouched); a published pin runs no git",
      withTmp fun d => do
        let src := d / "src"
        let (first, _) ← library src
        let r ← FvdepIO.Library.snapshot (← store d src) (some first)
        let gitless ← store d src (program := "/nonexistent/git")
        let warm ← FvdepIO.Library.snapshot gitless (some first)
        let cold ← FvdepIO.Library.snapshot gitless (some (String.ofList (List.replicate 40 'e')))
        let servedFirst (x : Except String FvdepIO.Library.Served) : Bool :=
          match x with
          | .ok sv => sv.commit == first && sv.notice.isNone
          | .error _ => false
        return servedFirst r && servedFirst warm &&
            isError cold "Fetch failed: git could not start: " &&
            !(← ((← store d src).dir / "head.json").pathExists)),
    ("library: an unreachable source (gone, no main) serves the last head + its notice; never " ++
        "fetched → never",
      withTmp fun d => do
        let src := d / "src"
        let (_, second) ← library src
        let s ← store d src
        let _ ← FvdepIO.Library.snapshot s none
        let raw ← bytesOf (s.dir / "head.json")
        let fetched :=
          match recordOf s.key (← IO.FS.readBinFile (s.dir / "head.json")) with
          | .ok h => h.fetched
          | .error _ => ""
        IO.FS.rename src (d / "away")
        let r ← FvdepIO.Library.snapshot s none
        let never ← FvdepIO.Library.snapshot (← store (d / "other") src) none
        let gone := s!"Fetch failed: fatal: '{src}' does not appear to be a git repository."
        let rawAfter ← bytesOf (s.dir / "head.json")
        IO.FS.rename (d / "away") src
        discard <| git src #["branch", "-m", "main", "side"]
        let noMain ← FvdepIO.Library.snapshot s none
        let lastNotice (x : Except String FvdepIO.Library.Served) (first : String) : Bool :=
          match x with
          | .ok sv =>
            sv.commit == second && sv.notice == some s!"{first} Last successful fetch: {fetched}."
          | .error _ => false
        return lastNotice r gone && errIs never s!"{gone} Last successful fetch: never." &&
            rawAfter == raw &&
            lastNotice noMain "Fetch failed: fatal: couldn't find remote ref refs/heads/main." &&
            (← bytesOf (s.dir / "head.json")) == raw),
    ("library: after a transport failure a damaged store refuses (record bytes, another source, " ++
        "the tree missing or incomplete) + keeps the record",
      withTmp fun d => do
        let src := d / "src"
        let (_, second) ← library src
        let s ← store d src
        let _ ← FvdepIO.Library.snapshot s none
        let good ← IO.FS.readBinFile (s.dir / "head.json")
        IO.FS.rename src (d / "away")
        let pre := s!"infra io: the library store of {src} is damaged: "
        let damagedBy (bytes : ByteArray) (why : String) : IO Bool := do
          IO.FS.writeBinFile (s.dir / "head.json") bytes
          let r ← FvdepIO.Library.snapshot s none
          return errIs r (pre ++ why) && (← bytesOf (s.dir / "head.json")) == bytes.toList
        let other :=
          headText ⟨second, "2026-11-20T08:00:00Z", String.ofList (List.replicate 64 'f')⟩
        let a ← damagedBy "{".toUTF8 "head.json is no head record"
        let b ← damagedBy other "head.json names another source"
        IO.FS.rename (s.trees / second) (d / "aside")
        let gone := s!"the snapshot {second} that head.json names is missing or incomplete"
        let c ← damagedBy good gone
        IO.FS.rename (d / "aside") (s.trees / second)
        IO.FS.removeFile (s.trees / second / ".complete")
        let e ← damagedBy good gone
        return a && b && c && e),
    ("library: a received candidate that fails (link, submodule, missing required file, a path " ++
        "not UTF-8, a tag at the ref) never falls back, publishes nothing + removes its temps",
      withTmp fun d => do
        let src := d / "src"
        let (first, second) ← library src
        let s ← store d src
        let _ ← FvdepIO.Library.snapshot s none
        let raw ← bytesOf (s.dir / "head.json")
        let refusedAs (needle : String) (add := true) : IO Bool := do
          if add then
            discard <| git src #["add", "-A"]
          discard <| git src #["commit", "-qm", "bad"]
          let c := FvdepCore.Index.Assemble.trimText (← git src #["rev-parse", "HEAD"])
          let r ← FvdepIO.Library.snapshot s none
          let ok :=
            isError r needle && !isError r "Last successful fetch" &&
              (← bytesOf (s.dir / "head.json")) == raw &&
              !(← (s.trees / c).pathExists) &&
              (← s.tmp.readDir).isEmpty
          discard <| git src #["reset", "-q", "--hard", second]
          return ok
        let made ← Snapshot.sh "ln" #["-s", "../lakefile.lean", (src / "Fvdep" / "l").toString]
        let a ← refusedAs "holds a link at Fvdep/l"
        discard <| git src #["update-index", "--add", "--cacheinfo", s!"160000,{first},Fvdep/sub"]
        let b ← refusedAs "holds a submodule at Fvdep/sub" (add := false)
        IO.FS.removeFile (src / "Fvdep" / "Registry.lean")
        let c ← refusedAs "is no fvdep library"
        let tag ← git src #["tag", "-a", "-m", "t", "v1"] *> git src #["rev-parse", "v1"]
        IO.FS.writeFile (src / ".git" / "refs" / "heads" / "main")
            (FvdepCore.Index.Assemble.trimText tag ++ "\n")
        let r ← FvdepIO.Library.snapshot s none
        let t :=
          isError r "the fetched ref names a tag, not a commit" && !isError r "Last successful"
        let t := t && (← s.tmp.readDir).isEmpty
        IO.FS.writeFile (src / ".git" / "refs" / "heads" / "main") (second ++ "\n")
        discard <| git src #["reset", "-q", "--hard", second]
        let made2 ←
          Snapshot.sh "sh"
              #["-c", "printf x > \"$1/Fvdep/bad$(printf '\\377').txt\"", "sh", src.toString]
        let e ← refusedAs "holds a path that is not valid UTF-8"
        return made && a && b && c && t && made2 && e),
    ("library: an incomplete tree is rebuilt + stale temps removed under the lock",
      withTmp fun d => do
        let src := d / "src"
        let (first, _) ← library src
        let s ← store d src
        Snapshot.put (s.trees / first) "index.json" "not json".toUTF8
        Snapshot.put (s.trees / first) "junk" "must go".toUTF8
        IO.FS.createDirAll (s.tmp / "2147483647.1.git" / "objects")
        let r ← FvdepIO.Library.snapshot s (some first)
        return (r matches .ok _) && !(← (s.trees / first / "junk").pathExists) &&
            (← bytesOf (s.trees / first / "index.json")) == "{}\n".toUTF8.toList &&
            (← FvdepIO.Library.kind (s.trees / first / ".complete")) matches some .file &&
            (← s.tmp.readDir).isEmpty),
    ("library: the store lock's wait ends after lockSeconds (stayed locked), before any git " ++
        "run; a published pin is served without the lock",
      withTmp fun d => do
        let src := d / "src"
        let (first, _) ← library src
        let _ ← FvdepIO.Library.snapshot (← store d src) (some first)
        let s ← store d src { lockSeconds := 1 } "/nonexistent/git"
        let h ← IO.FS.Handle.mk (s.dir / "lock") .append
        h.lock
        let t0 ← IO.monoMsNow
        let r ← FvdepIO.Library.snapshot s none
        let t1 ← IO.monoMsNow
        let warm ← FvdepIO.Library.snapshot s (some first)
        let t2 ← IO.monoMsNow
        h.unlock
        let served :=
          match warm with
          | .ok sv => sv.commit == first
          | .error _ => false
        return errIs r s!"infra io: the library store of {src} stayed locked" && 900 ≤ t1 - t0 &&
            t1 - t0 < 5000 &&
            served &&
            t2 - t1 < 500),
    ("library: the fetch deadline kills git's process group (a helper too) + reaps it",
      withTmp fun d => do
        let src := d / "src"
        let _ ← library src
        let log := d / "pids"
        script (d / "git")
            ("for a in \"$@\"; do if [ \"$a\" = fetch ]; then sleep 30 & echo \"$$ $!\" > '" ++
              log.toString ++
              "'; wait; exit 1; fi; done\nexec git \"$@\"\n")
        let s ← store d src { fetchSeconds := 2 } (d / "git").toString
        let t0 ← IO.monoMsNow
        let r ← FvdepIO.Library.snapshot s none
        let t1 ← IO.monoMsNow
        let pids :=
          ((FvdepCore.Index.Assemble.trimText (← IO.FS.readFile log)).splitOn " ").filterMap
            String.toNat?
        let stopped (pid : Nat) : IO Bool := do
          let st := s!"/proc/{pid}/stat"
          unless ← System.FilePath.pathExists st do
            return true
          let text ← IO.FS.readFile st
          return ((text.splitOn ") ").getLastD "").startsWith "Z"
        let mut helper := false
        for _ in [0:30] do
          if ← stopped (pids.getD 1 0) then
            helper := true
            break
          IO.sleep 100
        let leaderGone := !(← System.FilePath.pathExists s!"/proc/{pids.getD 0 0}")
        return errIs r "Fetch failed: git fetch passed its deadline of 2 seconds." &&
            t1 - t0 < 10000 &&
            pids.length == 2 &&
            helper &&
            leaderGone &&
            (← s.tmp.readDir).isEmpty),
    ("library: git runs with exactly L3's environment + argv (init, fetch) in a private repository",
      withTmp fun d => do
        let src := d / "src"
        let _ ← library src
        let log := d / "calls"
        let record :=
          "{ printf 'ARGS'; for a in \"$@\"; do printf '\\t%s' \"$a\"; done; " ++
            "printf '\\nENV'; tr '\\000' '\\n' < /proc/$$/environ | sed 's/=.*//' | sort | " ++
            "tr '\\n' ' '; printf '\\nHOME %s\\n' \"$HOME\"; }"
        script (d / "git") (record ++ " >> '" ++ log.toString ++ "'\nexec git \"$@\"\n")
        let s ← store d src {} (d / "git").toString
        let r ← FvdepIO.Library.snapshot s none
        let lines := (← IO.FS.readFile log).splitOn "\n"
        let calls :=
          lines.filterMap fun l =>
            if l.startsWith "ARGS" then some ((l.splitOn "\t").drop 1) else none
        let envs := lines.filter (·.startsWith "ENV")
        let homes := lines.filter (·.startsWith "HOME ")
        let init := calls.headD []
        let repo := init.getLastD ""
        let fetch := calls.getD 1 []
        return (r matches .ok _) && init == initArgs repo &&
            repo.startsWith (s.tmp.toString ++ "/") &&
            repo.endsWith ".git" &&
            fetch == fetchArgs repo src.toString none &&
            envs.all
              (· ==
                "ENVGIT_ASKPASS GIT_CONFIG_GLOBAL GIT_CONFIG_NOSYSTEM GIT_TERMINAL_PROMPT HOME " ++
                  "LC_ALL PATH SSH_ASKPASS ") &&
            homes.all (· == s!"HOME {repo}") &&
            !(← System.FilePath.pathExists repo) &&
            calls.length == envs.length &&
            (calls.filter (·.contains "fetch")).length == 1),
    ("library: a failed fetch's line — the source's userinfo masked, §1 escapes, the kept bytes " ++
        "alone",
      withTmp fun d => do
        let err := d / "err"
        script (d / "git")
            ("for a in \"$@\"; do if [ \"$a\" = fetch ]; then cat '" ++ err.toString ++
              "' >&2; exit 128; fi; done\nexec git \"$@\"\n")
        let src := "file://user:" ++ "pw@localhost/nonexistent"
        let run (l : Limits) : IO (Except String FvdepIO.Library.Served) := do
          let st ← FvdepIO.Library.Store.of (d / "cache") src l (d / "git").toString
          FvdepIO.Library.snapshot st none
        IO.FS.writeFile err
            s!"fatal: '{src}' does not appear to be a git repository\nuser:pw again\n"
        let a ← run {}
        IO.FS.writeFile err "\x1b[2Jboom\tz\nsecond\n"
        let b ← run {}
        IO.FS.writeFile err ("0123456789" ++ String.ofList (List.replicate 300 'X') ++ "PLANT\n")
        let c ← run { gitBytes := 40 }
        return errIs a
              ("Fetch failed: fatal: 'file://***@localhost/nonexistent' does not " ++
                "appear to be a git repository. Last successful fetch: never.") &&
            errIs b "Fetch failed: \\u001B[2Jboom\\tz." &&
            errIs c ("Fetch failed: 0123456789" ++ String.ofList (List.replicate 30 'X') ++ ".")),
    ("library: a listing past its stdout cap is refused before any plan",
      withTmp fun d => do
        let src := d / "src"
        let (_, second) ← library src
        let st ← store d src { caps := { entries := 1, pathTotal := 10 } }
        let r ← FvdepIO.Library.snapshot st none
        return errIs r
            (s!"Fetch failed: the library snapshot {second} lists more than its " ++
              "limits allow (1 tree entries, 10 path bytes).")),
    ("library: path bytes counted over both listings (the root directory's name twice): 93 " ++
        "printed > 90 refused at the crossing record, though the distinct entries hold 88",
      withTmp fun d => do
        let src := d / "src"
        let (_, second) ← library src
        let st ← store d src { caps := { pathTotal := 90 } }
        let r ← FvdepIO.Library.snapshot st none
        let st93 ← store (d / "b") src { caps := { pathTotal := 93 } }
        let ok ← FvdepIO.Library.snapshot st93 none
        return errIs r
              (s!"Fetch failed: the library snapshot {second} exceeds the limit of 90 " ++
                "path bytes at Fvdep/Second.lean.") &&
            ok matches .ok _),
    ("project: fvdep.toml by lstat — a file, a link, a FIFO, a directory, absent",
      withTmp fun d => do
        Snapshot.put (d / "f") "fvdep.toml" "x".toUTF8
        IO.FS.createDirAll (d / "l")
        let target := (d / "f" / "fvdep.toml").toString
        let a ← Snapshot.sh "ln" #["-s", target, (d / "l" / "fvdep.toml").toString]
        IO.FS.createDirAll (d / "p")
        let b ← Snapshot.sh "mkfifo" #[(d / "p" / "fvdep.toml").toString]
        IO.FS.createDirAll (d / "dir" / "fvdep.toml")
        return a && b && (← FvdepIO.Project.found (d / "f")) == .file &&
            (← FvdepIO.Project.found (d / "l")) == .link &&
            (← FvdepIO.Project.found (d / "p")) == .special &&
            (← FvdepIO.Project.found (d / "dir")) == .special &&
            (← FvdepIO.Project.found (d / "none")) == .absent &&
            (FvdepIO.Project.ancestors "/a/b").map (·.toString) == ["/a/b", "/a", "/"]),
    ("project: the pin through U3's reader; its refusals name the file (syntax, schema, size)",
      withTmp fun d => do
        let pin := String.ofList (List.replicate 40 'a')
        let m := s!"schema = 1\n\n[library]\ncommit = \"{pin}\"\n"
        let file := s!"{d}/fvdep.toml"
        Snapshot.put d "fvdep.toml" m.toUTF8
        let ok ← FvdepIO.Project.pin d.toString
        Snapshot.put d "fvdep.toml" "schema = [\n".toUTF8
        let syn ← FvdepIO.Project.pin d.toString
        Snapshot.put d "fvdep.toml" (m.replace "schema = 1" "schema = 2").toUTF8
        let schema ← FvdepIO.Project.pin d.toString
        let body := m.toUTF8 ++ "#".toUTF8
        Snapshot.put d "fvdep.toml" (body ++ ⟨(List.replicate (65537 - body.size) 0x78).toArray⟩)
        let big ← FvdepIO.Project.pin d.toString
        Snapshot.put d "fvdep.toml" (body ++ ⟨(List.replicate (200000 - body.size) 0x78).toArray⟩)
        let huge ← FvdepIO.Project.pin d.toString
        let tooLarge := s!"infra schema: {file}: too_large (more than 65536 bytes)"
        return (match ok with
            | .ok p => p == pin
            | .error _ => false) &&
            (match syn with
            | .error e => e.startsWith s!"infra schema: {file}: syntax at 2:1: "
            | .ok _ => false) &&
            (match schema with
            | .error e => e.startsWith s!"infra schema: {file}: " && (e.splitOn "schema").length > 2
            | .ok _ => false) &&
            errIs big tooLarge &&
            errIs huge tooLarge &&
            errIs (← FvdepIO.Project.pin (d / "none").toString)
              s!"No fvdep.toml found in {d}/none."),
    ("library: fvdep-dev library fetch end to end — a project's pin under umask 077 still " ++
        "writes 0644 files; git through PATH, no inherited descriptor; stdout = served <commit>",
      withTmp fun d => do
        let src := d / "src"
        let (first, _) ← library src
        Snapshot.put (d / "proj") "fvdep.toml"
            s!"schema = 1\n\n[library]\ncommit = \"{first}\"\n".toUTF8
        IO.FS.createDirAll (d / "proj" / "a")
        let dev := (← IO.currentDir) / ".lake" / "build" / "bin" / "fvdep-dev"
        let real :=
          FvdepCore.Index.Assemble.trimText
            (← IO.Process.output { cmd := "sh", args := #["-c", "command -v git"] }).stdout
        let fds := (d / "fds").toString
        IO.FS.createDirAll (d / "bin")
        script (d / "bin" / "git")
            ("ls /proc/$$/fd | tr '\\n' ' ' >> '" ++ fds ++ "'; echo >> '" ++ fds ++ "'\nexec '" ++
              real ++
              "' \"$@\"\n")
        let path := (d / "bin").toString ++ ":" ++ ((← IO.getEnv "PATH").getD "/usr/bin:/bin")
        let o ←
          IO.Process.output
              { cmd := "sh"
                args :=
                  #["-c", "umask 077 && exec 7</dev/null && cd \"$1\" && exec \"$2\" library fetch",
                    "sh", (d / "proj" / "a").toString, dev.toString]
                env :=
                  #[("FVDEP_CACHE", some (d / "cache").toString),
                    ("FVDEP_LIBRARY_URL", some src.toString), ("PATH", some path)] }
        let seen := ((← IO.FS.readFile (d / "fds")).splitOn "\n").filter (· != "")
        let s ← store d src
        return o.exitCode == 0 && o.stdout == s!"served {first}\n" && o.stderr == "" &&
            !seen.isEmpty &&
            seen.all (fun l => !(l.splitOn " ").contains "7") &&
            (← mode (s.trees / first / "Fvdep/Registry.lean")) == "644" &&
            !(← (s.dir / "head.json").pathExists))]

end LibraryR

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
            (Core.cases ++ Json.cases ++ Doc.cases ++ Index.cases ++ Registry.cases ++
                  Rules.cases ++
                  Statuses.cases ++
                  Assemble.cases ++
                  History.cases ++
                  Hash.cases ++
                  Manifest.cases ++
                  Sandbox.cases ++
                  Step.cases ++
                  Cache.cases ++
                  Snapshot.cases ++
                  PhaseD.cases ++
                  ExportR.cases ++
                  LibraryT.cases seed ++
                  LibraryR.cases seed ++
                  WireT.cases seed ++
                  OracleT.cases).map
              fun c => check c.1 c.2).mapM
        id
  let ioResults ←
    (Manifest.ioCases ++ Sys.ioCases ++ Spawn.ioCases ++ Cache.ioCases ++ Snapshot.ioCases ++
            PhaseIO.ioCases ++
            LibraryT.ioCases ++
            LibraryR.ioCases ++
            OracleT.ioCases).mapM
        fun c => checkIO c.1 c.2
  let results := results ++ ioResults
  let slowest := results.foldl (fun a r => if r.ms > a.ms then r else a) ⟨"none", true, 0⟩
  let failed := (results.filter (!·.ok)).length
  IO.println s!"slowest: {slowest.name} ({slowest.ms} ms)"
  IO.println s!"tests: {results.length - failed} passed, {failed} failed"
  return failed.toUInt32
