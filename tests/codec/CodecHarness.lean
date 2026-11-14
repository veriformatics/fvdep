import FvdepCore.Doc
import FvdepCore.Hash.Frame
import FvdepIO.Sha256

open FvdepCore.Json

namespace CodecTest

-- Test transport is length-prefixed, independent of both APIs under test.
def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

def bytesHex (b : ByteArray) : String :=
  b.data.foldl (fun s x => (s.push (digit (x.toNat / 16))).push (digit (x.toNat % 16))) ""

def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 87) else .error "transport: invalid hex"

def fromHex (s : String) : Except String ByteArray := do
  let mut out := ByteArray.empty
  let mut hi : Option Nat := none
  for c in s.toList do
    let n ← nibble c
    match hi with
    | none =>
      hi := some n
    | some h =>
      out := out.push (UInt8.ofNat (h * 16 + n))
      hi := none
  if hi.isSome then
    throw "transport: odd hex"
  return out

def net (s : String) : ByteArray := s!"{s.utf8ByteSize}:".toUTF8 ++ s.toUTF8

partial def wire (v : Value) : ByteArray :=
  match v with
  | .null => "n".toUTF8
  | .bool false => "f".toUTF8
  | .bool true => "t".toUTF8
  | .int n => s!"i{n};".toUTF8
  | .str s => "s".toUTF8 ++ net s
  | .arr xs => xs.foldl (fun b x => b ++ wire x) s!"a{xs.length}:".toUTF8
  | .obj ms => ms.foldl (fun b (k, x) => b ++ net k ++ wire x) s!"o{ms.length}:".toUTF8

partial def readUntil (b : ByteArray) (i : Nat) (stop : UInt8)
    (acc : ByteArray := ByteArray.empty) : Except String (String × Nat) := do
  if i ≥ b.size then
    throw "transport: missing delimiter"
  let c := b[i]!
  if c == stop then
    let some s := String.fromUTF8? acc | throw "transport: UTF-8"
    return (s, i + 1)
  readUntil b (i + 1) stop (acc.push c)

def readCount (b : ByteArray) (i : Nat) : Except String (Nat × Nat) := do
  let (s, j) ← readUntil b i 58
  let some n := s.toNat? | throw "transport: count"
  return (n, j)

def readNet (b : ByteArray) (i : Nat) : Except String (String × Nat) := do
  let (n, j) ← readCount b i
  if j + n > b.size then
    throw "transport: short string"
  let some s := String.fromUTF8? (b.extract j (j + n)) | throw "transport: UTF-8"
  return (s, j + n)

partial def readValue (b : ByteArray) (i : Nat) : Except String (Value × Nat) := do
  if i ≥ b.size then
    throw "transport: short value"
  match b[i]!.toNat with
  | 110 =>
    return (.null, i + 1)
  | 102 =>
    return (.bool false, i + 1)
  | 116 =>
    return (.bool true, i + 1)
  | 105 =>
    let (s, j) ← readUntil b (i + 1) 59
    let some n := s.toInt? | throw "transport: integer"
    return (.int n, j)
  | 115 =>
    let (s, j) ← readNet b (i + 1)
    return (.str s, j)
  | 97 =>
    let (n, start) ← readCount b (i + 1)
    let mut j := start
    let mut xs := []
    for _ in [:n] do
      let (v, next) ← readValue b j
      xs := v :: xs
      j := next
    return (.arr xs.reverse, j)
  | 111 =>
    let (n, start) ← readCount b (i + 1)
    let mut j := start
    let mut ms := []
    for _ in [:n] do
      let (k, afterKey) ← readNet b j
      let (v, next) ← readValue b afterKey
      ms := (k, v) :: ms
      j := next
    return (.obj ms.reverse, j)
  | _ =>
    throw "transport: unknown value tag"

def unwire (b : ByteArray) : Except String Value := do
  let (v, j) ← readValue b 0
  if j != b.size then
    throw "transport: trailing bytes"
  return v

def valueOut (v : Value) : String := "ok:" ++ bytesHex (wire v)

def decodeOut (r : Except DecodeError Value) : String :=
  match r with
  | .ok v => valueOut v
  | .error .malformed => "error:malformed"
  | .error .tooLarge => "error:tooLarge"
  | .error (.duplicateKey (path, key)) =>
    let segments :=
      path.map fun p =>
        match p with
        | .key s => Value.arr [.str "key", .str s]
        | .index n => Value.arr [.str "index", .int (Int.ofNat n)]
    "error:duplicate:" ++ bytesHex (wire (.arr [.arr segments, .str key]))

def optionValue (v : Option Value) : Value := .arr v.toList

def asOut (v : Value) : Value :=
  .arr
    [optionValue (v.asBool?.map Value.bool), optionValue (v.asInt?.map Value.int),
      optionValue (v.asStr?.map Value.str), optionValue (v.asArr?.map Value.arr),
      optionValue (v.asObj?.map Value.obj)]

def strings (v : Value) : Except String (List String) := do
  let .arr xs := v | throw "transport: string array expected"
  xs.mapM fun x =>
      match x with
      | .str s => .ok s
      | _ => .error "transport: string expected"

def files (v : Value) : Except String (List (String × ByteArray)) := do
  let .arr xs := v | throw "transport: files expected"
  xs.mapM fun x => do
      let .arr [.str p, .str h] := x | throw "transport: file pair expected"
      return (p, ← fromHex h)

def filesValue (fs : List (String × ByteArray)) : Value :=
  .arr (fs.map fun (p, b) => .arr [.str p, .str (bytesHex b)])

def unframeOut (r : Option (String × List (String × ByteArray))) : String :=
  match r with
  | none => "none"
  | some (t, fs) => valueOut (.arr [.str t, filesValue fs])

namespace DocumentTest

open FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc

def text (v : Value) : Except String String :=
  match v with
  | .str s => .ok s
  | _ => .error "document transport: string"

def optText (v : Value) : Except String (Option String) :=
  match v with
  | .null => .ok none
  | .str s => .ok (some s)
  | _ => .error "document transport: optional string"

def optTextValue (s : Option String) : Value := (s.map Value.str).getD .null

-- Typed 64-KiB boundary inputs grade Doc, not Ids' separate canonical text parser.
def segment (s : String) : Except String Seg := do
  let c :: cs := s.toList | throw "document transport: empty segment"
  let some h := Sym.ofChar? c | throw "document transport: segment head"
  if hh : h.val < 26 then
    let mut tail := []
    for x in cs do
      let some symbol := Sym.ofChar? x | throw "document transport: segment tail"
      tail := symbol :: tail
    return ⟨⟨h.val, hh⟩, tail.reverse⟩
  else
    throw "document transport: segment head digit"

def moduleId (s : String) : Except String ModuleId := do
  let [dep, op] := s.splitOn "." | throw "document transport: module id"
  let first :: rest := op.splitOn "_" | throw "document transport: module operation"
  return ⟨← segment dep, ← segment first, ← rest.mapM segment⟩

def entryVersion (s : String) : Except String EntryVersion := do
  let [a, b, c] := s.splitOn "." | throw "document transport: version"
  let some x := a.toNat? | throw "document transport: major"
  let some y := b.toNat? | throw "document transport: minor"
  let some z := c.toNat? | throw "document transport: patch"
  return ⟨x, y, z⟩

def libraryCommit (s : String) : Except String Commit :=
  match Commit.parse s with
  | some c => .ok c
  | none => .error "document transport: commit"

def kind (s : String) : Except String Kind :=
  match s with
  | "proof" => .ok .proof
  | "differential" => .ok .differential
  | _ => .error "document transport: kind"

def optShape (v : Value) : Except String (Option Shape) :=
  match v with
  | .null => .ok none
  | .str "fn" => .ok (some .fn)
  | .str "abi" => .ok (some .abi)
  | _ => .error "document transport: shape"

def optArgv (v : Value) : Except String (Option (List String)) := do
  if v matches .null then
    return none
  return some (← strings v)

def receipt (v : Value) : Except String Receipt := do
  let
    .arr
      [.str tag, .str dk, .str idText, .str versionText, shape, impl, proof, argv, .str specDigest,
        implDigest, proofDigest, adapterDigest, .str phase1, .str solution, .str lib, .str profile,
        .str policy, .str checked] :=
    v | throw "document transport: receipt fields"
  let declaration : Decl :=
    { module := ← moduleId idText
      version := ← entryVersion versionText
      shape := ← optShape shape
      kind := ← kind dk
      impl := ← optText impl
      proof := ← optText proof
      adapter := ← optArgv argv }
  let request : RequestKey :=
    { decl := declaration
      specClosure := specDigest
      implSources := ← optText implDigest
      proofSources := ← optText proofDigest
      adapter := ← optText adapterDigest }
  let p ←
    match policy with
    | "required" =>
      pure Policy.required
    | "development" =>
      pure Policy.development
    | _ =>
      throw "document transport: policy"
  let common : Common :=
    { request := request
      library := ← libraryCommit lib
      profile := profile
      policy := p
      checked := checked }
  match tag with
  | "proof" =>
    return .proof common phase1 solution
  | "differential" =>
    return .differential common
  | _ =>
    throw "document transport: receipt constructor"

def kindText : Kind → String
  | .proof => "proof"
  | .differential => "differential"

def receiptValue (r : Receipt) : Value :=
  let c := r.common
  let d := c.request.decl
  let tag :=
    match r with
    | .proof .. => "proof"
    | .differential _ => "differential"
  let (e1, e2) :=
    match r with
    | .proof _ a b => (a, b)
    | .differential _ => ("", "")
  let shape :=
    d.shape.map fun x =>
      match x with
      | .fn => "fn"
      | .abi => "abi"
  let av := (d.adapter.map fun xs => Value.arr (xs.map Value.str)).getD .null
  .arr
    [.str tag, .str (kindText d.kind), .str (toString d.module),
      .str s!"{d.version.major}.{d.version.minor}.{d.version.patch}", optTextValue shape,
      optTextValue d.impl, optTextValue d.proof, av, .str c.request.specClosure,
      optTextValue c.request.implSources, optTextValue c.request.proofSources,
      optTextValue c.request.adapter, .str e1, .str e2, .str (toString c.library), .str c.profile,
      .str
        (match c.policy with
        | .required => "required"
        | .development => "development"),
      .str c.checked]

def lock (v : Value) : Except String Lock := do
  let .arr [.str lib, .arr rs] := v | throw "document transport: lock"
  return ⟨← libraryCommit lib, ← rs.mapM receipt⟩

def lockValue (l : Lock) : Value :=
  .arr [.str (toString l.library), .arr (l.entries.map receiptValue)]

def commands : List Command := [.check, .list, .lock, .outdated, .scan, .status, .upgrade]

def codes : List PublicCode :=
  [.profileConstruct, .importNotAllowed, .reservedModule, .buildFailed, .statementMismatch,
    .graphMismatch, .axiom, .kernelReject, .kernelCrash, .kernelTimeout, .kernelDecline,
    .sandboxSetup, .toolMissing, .staleReceipt, .retracted, .policyProofRequired, .mismatch,
    .notDelivered, .usage, .noProject, .schema, .toolchain, .adapter, .fetchFailed, .io, .commitIo,
    .internal, .busy]

def nat (v : Value) : Except String Nat := do
  let .int n := v | throw "document transport: index"
  if n < 0 then
    throw "document transport: negative index"
  return n.toNat

def envelope (v : Value) : Except String Envelope := do
  let .arr [command, exit, failure, .obj result, .arr [lib, fetched, fetchError], trusted] :=
    v | throw "document transport: envelope"
  let some cmd := commands[← nat command]? | throw "document transport: command"
  let x ←
    match ← nat exit with
    | 0 =>
      pure Exit.ok
    | 1 =>
      pure Exit.negative
    | 2 =>
      pure Exit.failure
    | _ =>
      throw "document transport: exit"
  let err ←
    match failure with
    | .null =>
      pure none
    | .arr [code, .str detail] =>
      do
        let some publicCode := codes[← nat code]? | throw "document transport: code"
        pure (some ({ code := publicCode, detail := detail } : Failure))
    | _ =>
      throw "document transport: error"
  let commit ←
    match ← optText lib with
    | none =>
      pure none
    | some s =>
      some <$> libraryCommit s
  return {
      command := cmd
      exit := x
      error := err
      result := result
      status :=
        { commit := commit
          fetched := ← optText fetched
          fetchError := ← optText fetchError }
      trusted := ← strings trusted }

def path (v : Value) : Except String (List PathSeg) := do
  let .arr xs := v | throw "document transport: path"
  xs.mapM fun x => do
      match x with
      | .arr [.str "key", .str s] =>
        pure (.key s)
      | .arr [.str "index", n] =>
        pure (.index (← nat n))
      | _ =>
        throw "document transport: path segment"

def pathValue (ps : List PathSeg) : Value :=
  .arr
    (ps.map fun p =>
      match p with
      | .key s => .arr [.str "key", .str s]
      | .index n => .arr [.str "index", .int (Int.ofNat n)])

def errorKind (s : String) : Except String DocKind :=
  match s with
  | "missing_field" => .ok .missingField
  | "unknown_field" => .ok .unknownField
  | "wrong_type" => .ok .wrongType
  | "bad_value" => .ok .badValue
  | _ => .error "document transport: error kind"

def errorKindText : DocKind → String
  | .missingField => "missing_field"
  | .unknownField => "unknown_field"
  | .wrongType => "wrong_type"
  | .badValue => "bad_value"

def docError (v : Value) : Except String DocError := do
  let .arr [ps, .str k, .arr val] := v | throw "document transport: document error"
  let ov ←
    match val with
    | [] =>
      pure none
    | [x] =>
      pure (some x)
    | _ =>
      throw "document transport: error value"
  return ⟨← path ps, ← errorKind k, ov⟩

def errorOut (e : DocError) : String :=
  "doc-error:" ++
    bytesHex (wire (.arr [pathValue e.path, .str (errorKindText e.kind), .arr e.value.toList]))

def lockResult (r : Except LockError Lock) : String :=
  match r with
  | .ok l => valueOut (lockValue l)
  | .error (.doc e) => errorOut e
  | .error (.text e) => "lock-text:" ++ decodeOut (.error e)

def changeText : Change → String
  | .declaration => "declaration"
  | .specClosure => "spec_closure"
  | .implSources => "impl_sources"
  | .proofSources => "proof_sources"
  | .adapter => "adapter"
  | .library => "library"
  | .profile => "profile"
  | .policy => "policy"
  | .exports => "exports"

def execute (op : String) (v : Value) : Except String String := do
  match op with
  | "D.clip" =>
    return valueOut (.str (clip (← text v)))
  | "D.pointer" =>
    return valueOut (.str (pointer (← path v)))
  | "D.error.render" =>
    return valueOut (.str (DocError.render (← docError v)))
  | "D.command" =>
    let some x := commands[← nat v]? | throw "document transport: command"
    return valueOut (.str x.spelling)
  | "D.code" =>
    let some x := codes[← nat v]? | throw "document transport: code"
    return valueOut (.str x.spelling)
  | "D.receipt.decode" =>
    return match Receipt.ofJson v with
      | .ok r => valueOut (receiptValue r)
      | .error e => errorOut e
  | "D.lock.decodeValue" =>
    return match Lock.ofJson v with
      | .ok l => valueOut (lockValue l)
      | .error e => errorOut e
  | "D.receipt.transport" | "D.receipt.encode" | "D.receipt.wf" | "D.receipt.roundtrip" |
    "D.receipt.valid" | "D.decl.shaped" =>
    let r ← receipt v
    match op with
    | "D.receipt.transport" =>
      return valueOut (receiptValue r)
    | "D.receipt.encode" =>
      return valueOut r.toJson
    | "D.receipt.wf" =>
      return valueOut (.bool r.wellFormed)
    | "D.receipt.valid" =>
      return decodeOut (decode (print r.toJson))
    | "D.decl.shaped" =>
      return valueOut (.bool (shaped r.common.request))
    | _ =>
      return match Receipt.ofJson r.toJson with
        | .ok x => valueOut (receiptValue x)
        | .error e => errorOut e
  | "D.lock.transport" | "D.lock.encode" | "D.lock.value" | "D.lock.wf" | "D.lock.roundtrip" |
    "D.lock.valid" | "D.lock.normalize" | "D.lock.normalizeWf" =>
    let l ← lock v
    match op with
    | "D.lock.transport" =>
      return valueOut (lockValue l)
    | "D.lock.encode" =>
      return "bytes:" ++ bytesHex (encodeLock l)
    | "D.lock.value" =>
      return valueOut l.toJson
    | "D.lock.wf" =>
      return valueOut (.bool l.wellFormed)
    | "D.lock.valid" =>
      return decodeOut (decode (print l.toJson))
    | "D.lock.roundtrip" =>
      return lockResult (decodeLock (encodeLock l))
    | "D.lock.normalize" =>
      return valueOut (lockValue l.normalize)
    | _ =>
      return valueOut (.bool l.normalize.wellFormed)
  | "D.envelope.encode" | "D.envelope.wf" | "D.envelope.valid" =>
    let e ← envelope v
    match op with
    | "D.envelope.encode" =>
      return valueOut e.toJson
    | "D.envelope.wf" =>
      return valueOut (.bool e.wellFormed)
    | _ =>
      return decodeOut (decode (print e.toJson))
  | "D.decl.changes" | "D.decl.agreement" =>
    let .arr [old, fresh] := v | throw "document transport: declaration pair"
    let a ← receipt old
    let b ← receipt fresh
    if op == "D.decl.changes" then
      return valueOut (.arr ((changes a b.inputs).map fun x => .str (changeText x)))
    let result := agreement ⟨b.common.library, [b.common.request.decl]⟩ ⟨a.common.library, [a]⟩
    return valueOut
        (.arr
          (result.map fun x =>
            .str
              (match x with
              | .library => "library"
              | .missing _ => "missing"
              | .duplicate _ => "duplicate"
              | .declaration _ => "declaration"
              | .extra _ => "extra")))
  | _ =>
    throw ("document transport: operation " ++ op)

end DocumentTest

def execute (op : String) (b : ByteArray) : Except String String := do
  if op == "D.lock.decode" then
    return DocumentTest.lockResult (FvdepCore.Doc.decodeLock b)
  if op == "D.lock.render" then
    return match FvdepCore.Doc.decodeLock b with
      | .ok _ => "lock-ok"
      | .error e => valueOut (.str e.render)
  if op.startsWith "D." then
    return ← DocumentTest.execute op (← unwire b)
  match op with
  | "decode" =>
    return decodeOut (decode b)
  | "hex" =>
    return "text:" ++ bytesHex (FvdepCore.Hash.hex b).toUTF8
  | "unframe" =>
    return unframeOut (FvdepCore.Hash.unframe b)
  | "tags" =>
    return valueOut
        (.arr
          ([FvdepCore.Hash.Tag.specClosure, FvdepCore.Hash.Tag.implSources,
                FvdepCore.Hash.Tag.proofSources, FvdepCore.Hash.Tag.adapter,
                FvdepCore.Hash.Tag.entry].map
            (fun t => .str t.spelling)))
  | "limits" =>
    return "limits:" ++ toString maxInt ++ ":" ++ toString maxStringBytes ++ ":" ++
        toString maxDepth
  | _ =>
    let v ← unwire b
    match op with
    | "echo" =>
      return valueOut v
    | "print" =>
      return "bytes:" ++ bytesHex (print v)
    | "roundtrip" =>
      return decodeOut (decode (print v))
    | "object" =>
      let .obj ms := v | throw "transport: object expected"
      return valueOut (Value.object ms)
    | "get" =>
      let .arr [x, .str k] := v | throw "transport: get arguments"
      return valueOut (optionValue (x.get? k))
    | "as" =>
      return valueOut (asOut v)
    | "frame" | "frameRound" =>
      let .arr [.str t, fs] := v | throw "transport: frame arguments"
      let entries ← files fs
      let encoded := FvdepCore.Hash.frame t entries
      return if op == "frame" then "bytes:" ++ bytesHex encoded
        else unframeOut (FvdepCore.Hash.unframe encoded)
    | "argv" =>
      let argv ← strings v
      return "bytes:" ++ bytesHex (FvdepCore.Hash.argvBytes argv)
    | "adapter" =>
      let .arr [av, fs] := v | throw "transport: adapter arguments"
      let argv ← strings av
      let named ← files fs
      return valueOut (filesValue (FvdepCore.Hash.adapterEntries argv named))
    | _ =>
      throw ("transport: unknown operation " ++ op)

namespace ShaTest

open FvdepIO.Hash

def chunks (v : Value) : Except String (List ByteArray) := do
  let xs ← strings v
  xs.mapM fromHex

def run (op : String) (b : ByteArray) : IO String := do
  if op == "S.hash" then
    return bytesHex (sha256 b)
  if op == "S.monte" then
    let mut x := b
    let mut y := b
    let mut z := b
    for _ in [:1000] do
      let next := sha256 (x ++ y ++ z)
      x := y
      y := z
      z := next
    return bytesHex z
  let v ← IO.ofExcept (unwire b)
  match op with
  | "S.stream" =>
    let xs ← IO.ofExcept (chunks v)
    return bytesHex (Sha256.finish (xs.foldl Sha256.update Sha256.init))
  | "S.saturate" =>
    let .str n := v | throw (IO.userError "SHA transport: natural")
    let some n := n.toNat? | throw (IO.userError "SHA transport: natural")
    return toString (Sha256.saturate n)
  | "S.immutable" =>
    let .str h := v | throw (IO.userError "SHA transport: hex")
    let input ← IO.ofExcept (fromHex h)
    let held ← IO.mkRef input
    let hash ← IO.mkRef (bytesHex (sha256 input))
    let after ← held.get
    return valueOut (.arr [.str (← hash.get), .str (bytesHex after)])
  | "S.branch" =>
    let .arr [pre, left, right] := v | throw (IO.userError "SHA transport: branches")
    let xs ← IO.ofExcept (chunks (.arr [pre, left, right]))
    let [p, a, c] := xs | throw (IO.userError "SHA transport: branches")
    let root ← IO.mkRef (Sha256.update Sha256.init p)
    let sa ← IO.mkRef (Sha256.update (← root.get) a)
    let sb ← IO.mkRef (Sha256.update (← root.get) c)
    let outA ← IO.mkRef (bytesHex (Sha256.finish (← sa.get)))
    let outB ← IO.mkRef (bytesHex (Sha256.finish (← sb.get)))
    let outRoot ← IO.mkRef (bytesHex (Sha256.finish (← root.get)))
    let reused := Sha256.update (← root.get) a
    return valueOut
        (.arr
          [.str (← outRoot.get), .str (← outA.get), .str (← outB.get),
            .str (bytesHex (Sha256.finish reused)), .str (bytesHex (Sha256.finish (← sa.get)))])
  | "S.reader" =>
    let .arr [parts, .int fail] := v | throw (IO.userError "SHA transport: reader")
    let xs ← IO.ofExcept (chunks parts)
    let held ← IO.mkRef xs
    let position ← IO.mkRef 0
    let probe := IO.userError "sha-reader-probe"
    try
      let result ←
        Sha256.ofReader do
            let i ← position.get
            position.set (i + 1)
            if fail == Int.ofNat i then
              throw probe
            return ((← held.get)[i]?).getD ByteArray.empty
      let digest ← IO.mkRef (bytesHex result)
      return valueOut
          (.arr
            [.str (← digest.get), .int (Int.ofNat (← position.get)),
              .arr ((← held.get).map fun x => .str (bytesHex x))])
    catch e =>
      return if e.toString == probe.toString then "error:reader-probe" else "error:other-reader"
  | "S.file" =>
    let .str path := v | throw (IO.userError "SHA transport: file")
    try
      return bytesHex (← sha256File path)
    catch _ =>
      return "error:file"
  | "S.concurrent" =>
    let .arr [pre, parts] := v | throw (IO.userError "SHA transport: tasks")
    let [p] ← IO.ofExcept (chunks (.arr [pre])) | throw (IO.userError "SHA transport: prefix")
    let xs ← IO.ofExcept (chunks parts)
    let root ← IO.mkRef (Sha256.update Sha256.init p)
    let shared ← IO.mkRef (xs.headD ByteArray.empty)
    let mut jobs := []
    let mut index := 0
    for data in xs do
      let chosen ←
        if index < 2 then
          shared.get
        else
          pure data
      let input ← IO.mkRef chosen
      index := index + 1
      let task ←
        IO.asTask do
            let x ← input.get
            let h ← IO.mkRef (bytesHex (sha256 x))
            let s ← root.get
            return Value.arr [.str (← h.get), .str (bytesHex (Sha256.finish (Sha256.update s x)))]
      jobs := task :: jobs
    let mut answers := []
    for task in jobs.reverse do
      match task.get with
      | .ok x =>
        answers := x :: answers
      | .error e =>
        throw e
    return valueOut (.arr answers.reverse)
  | "H3.digest" =>
    let .arr [.int index, fs] := v | throw (IO.userError "SHA transport: digest")
    let tags := [FvdepCore.Hash.Tag.specClosure, .implSources, .proofSources, .adapter, .entry]
    let some tag := tags[index.toNat]? | throw (IO.userError "SHA transport: tag")
    let entries ← IO.ofExcept (files fs)
    return digest tag entries
  | _ =>
    throw (IO.userError "SHA transport: operation")

def abortRun (mode path : String) : IO UInt32 := do
  let input ← IO.FS.readBinFile path
  IO.eprintln "SHA_LIMIT_READY"
  IO.getStderr >>= (·.flush)
  let result ←
    match mode with
    | "hash" =>
      pure (sha256 input)
    | "stream" =>
      pure (Sha256.finish (Sha256.update Sha256.init input))
    | "wrap" =>
      do
        let some text := String.fromUTF8? input | throw (IO.userError "SHA limit natural")
        let some n := text.toNat? | throw (IO.userError "SHA limit natural")
        pure (Sha256.squeeze (Sha256.initState ()) ByteArray.empty (Sha256.saturate n))
    | _ =>
      throw (IO.userError "SHA limit mode")
  IO.println ("DIGEST " ++ bytesHex result)
  return 0

end ShaTest

def executeIO (op : String) (b : ByteArray) : IO String := do
  if op.startsWith "S." || op == "H3.digest" then
    return ← ShaTest.run op b
  return match execute op b with
    | .ok s => s
    | .error e => "driver-error:" ++ e

end CodecTest

namespace CodecTest

def main (args : List String) : IO UInt32 := do
  if let ["--sha-abort", mode, path] := args then
    return ← CodecTest.ShaTest.abortRun mode path
  let [requests, results] := args |
    do
      IO.eprintln "usage: codec-driver REQUESTS RESULTS"
      return 2
  let output ← IO.FS.Handle.mk results .write
  let input ← IO.FS.Handle.mk requests .read
  repeat
    let line ← input.getLine
    if line.isEmpty then
      break
    let fields := (line.dropEnd 1).toString.splitOn "\t"
    match fields with
    | [id, op, path] =>
      try
        let b ← IO.FS.readBinFile path
        let result ← CodecTest.executeIO op b
        output.putStrLn (id ++ "\t" ++ result)
        output.flush
      catch e =>
        output.putStrLn (id ++ "\tdriver-error:" ++ toString e)
        output.flush
    | _ =>
      IO.eprintln "transport: bad request row"
      return 2
  return 0

end CodecTest
