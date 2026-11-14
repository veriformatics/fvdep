import FvdepIO.Toml
import Lean.Data.Json

open Lean FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Manifest
open FvdepIO.Toml

abbrev J := Lean.Json

def obj := Lean.Json.mkObj

def field (j : J) (key : String) : Except String J := j.getObjVal? key

def str (j : J) : Except String String := j.getStr?

def array (j : J) : Except String (Array J) := j.getArr?

def nullable {α : Type} (f : α → J) : Option α → J
  | none => .null
  | some x => f x

def listJson {α : Type} (f : α → J) (xs : List α) : J := .arr (xs.map f).toArray

def getStrings (j : J) : Except String (List String) := do
  (← array j).toList.mapM str

def getOptional {α : Type} (f : J → Except String α) (j : J) : Except String (Option α) :=
  if j == .null then .ok none else (f j).map some

partial def getTree (j : J) : Except String Tree := do
  let tag ← str (← field j "t")
  let v ← field j "v"
  match tag with
  | "str" =>
    return .str (← str v)
  | "int" =>
    return .int (← v.getInt?)
  | "bool" =>
    return .bool (← v.getBool?)
  | "arr" =>
    return .arr (← (← array v).toList.mapM getTree)
  | "tbl" =>
    return .tbl
        (←
          (← array v).toList.mapM fun pair => do
              let xs ← array pair
              if xs.size != 2 then
                throw "table pair"
              return (← str xs[0]!, ← getTree xs[1]!))
  | "other" =>
    match ← str v with
    | "float" =>
      return .other .float
    | "datetime" =>
      return .other .dateTime
    | _ =>
      throw "other kind"
  | _ =>
    throw "tree tag"

partial def treeJson : Tree → J
  | .str s => obj [("t", .str "str"), ("v", .str s)]
  | .int n => obj [("t", .str "int"), ("v", toJson n)]
  | .bool b => obj [("t", .str "bool"), ("v", .bool b)]
  | .other k => obj [("t", .str "other"), ("v", .str (if k == .float then "float" else "datetime"))]
  | .arr xs => obj [("t", .str "arr"), ("v", listJson treeJson xs)]
  | .tbl ms =>
    obj [("t", .str "tbl"), ("v", listJson (fun (k, v) => .arr #[.str k, treeJson v]) ms)]

def getShape (j : J) : Except String Shape := do
  match ← str j with
  | "fn" =>
    return .fn
  | "abi" =>
    return .abi
  | _ =>
    throw "shape"

def getEntry (j : J) : Except String Entry := do
  let moduleText ← str (← field j "id")
  let some moduleId := ModuleId.parse moduleText | throw "fixture module id"
  let versionText ← str (← field j "version")
  let some version := EntryVersion.parse versionText | throw "fixture version"
  let kindText ← str (← field j "kind")
  let kind ←
    match kindText with
    | "proof" =>
      pure Kind.proof
    | "differential" =>
      pure Kind.differential
    | _ =>
      throw "fixture kind"
  return {
      decl :=
        { module := moduleId
          version := version
          shape := ← getOptional getShape (← field j "shape")
          kind := kind
          impl := ← getOptional str (← field j "impl")
          proof := ← getOptional str (← field j "proof")
          adapter := ← getOptional getStrings (← field j "adapter") }
      implModules := ← getStrings (← field j "impl_modules")
      proofModules := ← getStrings (← field j "proof_modules") }

def getManifest (j : J) : Except String ManifestFile := do
  let text ← str (← field j "library")
  let some library := Commit.parse text | throw "fixture commit"
  let p ← str (← field j "policy")
  let policy ←
    match p with
    | "required" =>
      pure Policy.required
    | "development" =>
      pure Policy.development
    | _ =>
      throw "fixture policy"
  return {
      library := library
      policy := policy
      modules := ← (← array (← field j "modules")).toList.mapM getEntry }

def declJson (d : Decl) : J :=
  obj
    [("id", .str (String.ofList d.module.chars)), ("version", .str (String.ofList d.version.chars)),
      ("kind", .str (if d.kind == .proof then "proof" else "differential")),
      ("shape", nullable (fun x => .str (if x == .fn then "fn" else "abi")) d.shape),
      ("impl", nullable .str d.impl), ("proof", nullable .str d.proof),
      ("adapter", nullable (listJson .str) d.adapter)]

def entryJson (e : Entry) : J :=
  obj
    [("decl", declJson e.decl), ("impl_modules", listJson .str e.implModules),
      ("proof_modules", listJson .str e.proofModules)]

def manifestJson (m : ManifestFile) : J :=
  obj
    [("library", .str (String.ofList m.library.chars)),
      ("policy", .str (if m.policy == .required then "required" else "development")),
      ("modules", listJson entryJson m.modules)]

def getPath (j : J) : Except String (List FvdepCore.Json.PathSeg) := do
  (← array j).toList.mapM fun x =>
      match x with
      | .str s => .ok (.key s)
      | _ => x.getNat? |>.map .index

def pathJson (p : List FvdepCore.Json.PathSeg) : J :=
  listJson
    (fun
      | .key k => .str k
      | .index n => toJson n)
    p

def fieldType : FieldType → String
  | .string => "string"
  | .integer => "integer"
  | .array => "array"
  | .table => "table"

def manifestErrorJson (e : ManifestError) : J :=
  let (kind, expected, name) : String × J × J :=
    match e.kind with
    | .missingField => ("missing_field", Lean.Json.null, Lean.Json.null)
    | .unknownField => ("unknown_field", .null, .null)
    | .forbiddenField => ("forbidden_field", .null, .null)
    | .wrongType ty => ("wrong_type", .str (fieldType ty), .null)
    | .badValue => ("bad_value", .null, .null)
    | .duplicateKey key => ("duplicate_key", .null, .str key)
    | .inBothLists moduleName => ("in_both_lists", .null, .str moduleName)
  obj [("path", pathJson e.path), ("kind", .str kind), ("expected", expected), ("name", name)]

def validatedJson : Except ManifestError ManifestFile → J
  | .ok m => obj [("ok", manifestJson m)]
  | .error e => obj [("error", manifestErrorJson e), ("detail", .str e.detail)]

def textErrorJson : TextError → J
  | .tooLarge => obj [("kind", .str "too_large")]
  | .bom => obj [("kind", .str "bom")]
  | .utf8 k => obj [("kind", .str "utf8"), ("offset", toJson k)]

partial def nameJson : Name → J
  | .anonymous => .arr #[.str "anonymous"]
  | .str p s => .arr #[.str "str", nameJson p, .str s]
  | .num p n => .arr #[.str "num", nameJson p, toJson n]

partial def getName (j : J) : Except String Name := do
  let xs ← array j
  match ← str xs[0]! with
  | "anonymous" =>
    return .anonymous
  | "str" =>
    return .str (← getName xs[1]!) (← str xs[2]!)
  | "num" =>
    return .num (← getName xs[1]!) (← xs[2]!.getNat?)
  | _ =>
    throw "fixture name"

def parseErrorJson : ParseError → J
  | .syntax line col message =>
    obj
      [("stage", .str "syntax"), ("line", toJson line), ("col", toJson col),
        ("message", .str message)]
  | .key n => obj [("stage", .str "key"), ("name", nameJson n)]

def readErrorJson (e : ReadError) : J :=
  let payload :=
    match e with
    | .text t => obj [("stage", .str "text"), ("text", textErrorJson t)]
    | .parse p => parseErrorJson p
    | .schema s => obj [("stage", .str "schema"), ("error", manifestErrorJson s)]
  obj [("error", payload), ("code", .str e.code.spelling), ("detail", .str e.detail)]

def readJson : Except ReadError ManifestFile → J
  | .ok m => obj [("ok", manifestJson m)]
  | .error e => readErrorJson e

def unhex (s : String) : Except String ByteArray := do
  let chars := s.toList
  if chars.length % 2 != 0 then
    throw "fixture hex length"
  let digits ←
    chars.mapM fun c =>
        if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
        else
          if 'a' ≤ c && c ≤ 'f' then pure (10 + c.toNat - 'a'.toNat) else throw "fixture hex digit"
  let digits := digits.toArray
  return ⟨(Array.range (digits.size / 2)).map fun i =>
        UInt8.ofNat (16 * digits[i * 2]! + digits[i * 2 + 1]!)⟩

def hexBytes (b : ByteArray) : String :=
  String.ofList
    (b.data.toList.flatMap fun x =>
      let n := x.toNat
      let digits := "0123456789abcdef".toList
      [digits[n / 16]!, digits[n % 16]!])

-- Independent traversal: observes Lake's output assumptions, without calling fvdep's converter.
mutual
partial def lakeValueJson : Lake.Toml.Value → Except String Tree
  | .string _ s => .ok (.str s)
  | .integer _ n => .ok (.int n)
  | .boolean _ b => .ok (.bool b)
  | .float .. => .ok (.other .float)
  | .dateTime .. => .ok (.other .dateTime)
  | .array _ xs => (xs.toList.mapM lakeValueJson).map Tree.arr
  | .table _ t => lakeTableJson t
partial def lakeTableJson (t : Lake.Toml.Table) : Except String Tree := do
  let mut seen : List String := []
  let mut out := []
  for (k, v) in t.items do
    let .str .anonymous s := k | throw s!"Lake key is not one string component: {k}"
    if seen.contains s then
      throw s!"Lake repeated key: {s}"
    seen := s :: seen
    out := out ++ [(s, ← lakeValueJson v)]
  return .tbl out
end

def lakeParse (text : String) : IO J := do
  match ← (Lake.Toml.loadToml (Lean.Parser.mkInputContext text "fvdep.toml")).toBaseIO with
  | .ok t =>
    match lakeTableJson t with
    | .ok tree =>
      return obj [("tree", treeJson tree)]
    | .error e =>
      return obj [("assumption_error", .str e)]
  | .error messages =>
    match messages.toList.head? with
    | none =>
      return obj [("harness_error", .str "Lake error without a message")]
    | some msg =>
      return obj
          [("error", parseErrorJson (.syntax msg.pos.line msg.pos.column (← msg.data.toString)))]

def fixture {α : Type} (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

partial def run (j : J) : IO J := do
  let op ← fixture (str (← fixture (field j "op")))
  match op with
  | "echo_hex" =>
    let b ← fixture (unhex (← fixture (str (← fixture (field j "hex")))))
    return obj [("hex", .str (hexBytes b))]
  | "echo_tree" =>
    return obj [("tree", treeJson (← fixture (getTree (← fixture (field j "tree")))))]
  | "echo_manifest" =>
    return obj [("ok", manifestJson (← fixture (getManifest (← fixture (field j "manifest")))))]
  | "max" =>
    return obj [("max", toJson maxBytes)]
  | "utf8" =>
    let b ← fixture (unhex (← fixture (str (← fixture (field j "hex")))))
    return obj [("offset", nullable toJson (utf8ErrorOffset b))]
  | "text" =>
    let b ← fixture (unhex (← fixture (str (← fixture (field j "hex")))))
    return match textStage b with
      | .ok s => obj [("ok", .str s)]
      | .error e => obj [("error", textErrorJson e), ("detail", .str e.detail)]
  | "validate" =>
    return validatedJson (validate (← fixture (getTree (← fixture (field j "tree")))))
  | "parse" =>
    match ← parseTree (← fixture (str (← fixture (field j "text")))) with
    | .ok t =>
      return obj [("tree", treeJson t)]
    | .error e =>
      return obj [("error", parseErrorJson e)]
  | "lake" =>
    return ← lakeParse (← fixture (str (← fixture (field j "text"))))
  | "read" =>
    let b ← fixture (unhex (← fixture (str (← fixture (field j "hex")))))
    return readJson (← readManifest b)
  | "print" | "tree" | "tree_round" | "round" | "projection" =>
    let m ← fixture (getManifest (← fixture (field j "manifest")))
    match op with
    | "print" =>
      return obj [("hex", .str (hexBytes (printManifest m)))]
    | "tree" =>
      return obj [("tree", treeJson (toTree m))]
    | "tree_round" =>
      return validatedJson (validate (toTree m))
    | "round" =>
      return readJson (← readManifest (printManifest m))
    | _ =>
      let p := m.manifest
      return obj
          [("library", .str (String.ofList p.library.chars)), ("decls", listJson declJson p.decls)]
  | "path" =>
    return obj [("path", .str (keyPath (← fixture (getPath (← fixture (field j "path"))))))]
  | "oflake_key" =>
    let key ← fixture (getName (← fixture (field j "name")))
    let value := Lake.Toml.Value.string .missing "payload"
    let t := Lake.Toml.Table.empty.insert key value
    let t :=
      if (← fixture (field j "nested")).getBool?.toOption == some true then
        Lake.Toml.Table.empty.insert (.str .anonymous "outer") (.table .missing t)
      else t
    return match ofLake t with
      | .ok t => obj [("tree", treeJson t)]
      | .error n => obj [("name", nameJson n)]
  | "error_code" =>
    let kind ← fixture (str (← fixture (field j "kind")))
    let e ←
      match kind with
      | "key" =>
        pure (ReadError.parse (.key (← fixture (getName (← fixture (field j "name"))))))
      | "syntax" =>
        pure
            (ReadError.parse
              (.syntax (← fixture (field j "line" >>= Lean.Json.getNat?))
                (← fixture (field j "col" >>= Lean.Json.getNat?))
                (← fixture (field j "message" >>= str))))
      | "bom" =>
        pure (ReadError.text .bom)
      | "too_large" =>
        pure (ReadError.text .tooLarge)
      | "utf8" =>
        pure (ReadError.text (.utf8 (← fixture (field j "offset" >>= Lean.Json.getNat?))))
      | _ =>
        pure (ReadError.schema { path := [.key "schema"], kind := .missingField })
    return readErrorJson e
  | _ =>
    throw (IO.userError s!"unknown fixture operation {op}")

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let response ←
      try
        match Lean.Json.parse line with
        | .ok j =>
          run j
        | .error e =>
          pure (obj [("harness_error", .str e)])
      catch e =>
        pure (obj [("harness_error", .str e.toString)])
    stdout.putStrLn response.compress
    stdout.flush
  return 0
