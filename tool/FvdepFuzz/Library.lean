import FvdepCore.Library

/-! Fuzz targets `git-tree` + `git-batch` (contract U5b L4, Q4): byte 0 even = raw (any bytes
through `parseTree` + `planTree`, or a plan from bytes 1–3 + any replies through `parseBatch`: no
panic, no hang); odd = generated (well-formed records or replies built from the bytes, printed as
git prints them: the reader must return exactly them; a mismatch panics). -/

namespace FvdepFuzz

open FvdepCore.Library

/-- Byte `i` of `b`, 0 past the end. -/
def at0 (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

def hexDigit (n : Nat) : UInt8 :=
  if n % 16 < 10 then (48 + n % 16).toUInt8 else (87 + n % 16).toUInt8

def oidOf (b : ByteArray) (i : Nat) : List UInt8 :=
  (List.range 40).map fun k => hexDigit (at0 b (i + k / 2) >>> (if k % 2 == 0 then 4 else 0)).toNat

/-- A path from bytes: 1–8 characters (ASCII, TAB, LF, a 2-byte + a 3-byte character). -/
def pathOf (b : ByteArray) (i : Nat) : String :=
  let alphabet := "abcXYZ019-_.\t\n é中/".toList
  String.ofList <|
    (List.range ((at0 b i).toNat % 8 + 1)).map fun k =>
      alphabet.getD ((at0 b (i + 1 + k)).toNat % alphabet.length) 'a'

def modes : List (List UInt8) :=
  [modeTree, modeFile, modeExec, modeLink, modeGitlink, [49, 48, 48, 54, 48, 48]]

/-- A well-formed entry from the bytes at `i`. -/
def entryOf (b : ByteArray) (i : Nat) : TreeEntry :=
  let kind : ObjKind :=
    match (at0 b i).toNat % 3 with
    | 0 => .blob
    | 1 => .tree
    | _ => .commit
  let size :=
    if kind == .blob then some ((at0 b (i + 1)).toNat * (at0 b (i + 2)).toNat * 97) else none
  ⟨modes.getD ((at0 b (i + 3)).toNat % modes.length) modeFile, kind, oidOf b (i + 4), size,
    pathOf b (i + 24)⟩

def kindBytes : ObjKind → List UInt8
  | .blob => [98, 108, 111, 98]
  | .tree => [116, 114, 101, 101]
  | .commit => [99, 111, 109, 109, 105, 116]

/-- `ls-tree -z -l`'s record of `e` (`%06o %s %s %7s\t%s\0`). -/
def recordBytes (e : TreeEntry) : List UInt8 :=
  let size :=
    match e.size with
    | some n => digits n
    | none => [45]
  e.mode ++ [32] ++ kindBytes e.kind ++ [32] ++ e.oid ++ [32] ++ pad7 size ++ [9] ++
    e.path.toUTF8.toList ++
    [0]

@[export fvdep_fuzz_git_tree]
def gitTreeTarget (b : ByteArray) : UInt8 :=
  if at0 b 0 % 2 == 0 then
    match parseTree (b.extract 1 b.size) with
    | some es =>
      match planTree {} es with
      | .ok bs => if bs.length > es.length then panic! "git-tree: more blobs than entries" else 0
      | .error _ => 0
    | none => 0
  else
    let es := (List.range ((b.size - 1) / 34 + 1)).map fun k => entryOf b (1 + 34 * k)
    let bytes := (es.flatMap recordBytes).toByteArray
    match parseTree bytes with
    | some es' => if es' == es then 0 else panic! "git-tree: a generated listing read back changed"
    | none => panic! "git-tree: a generated listing was refused"

/-- A plan of 0–3 blobs from bytes 1–3 (sizes 0–15). -/
def planOf (b : ByteArray) : List Blob :=
  (List.range ((at0 b 1).toNat % 4)).map fun k =>
    ⟨s!"f{k}", oidOf b (2 + 20 * k), (at0 b (2 + k)).toNat % 16⟩

@[export fvdep_fuzz_git_batch]
def gitBatchTarget (b : ByteArray) : UInt8 :=
  let plan := planOf b
  if at0 b 0 % 2 == 0 then
    match parseBatch plan (b.extract 4 b.size) with
    | some cs => if cs.length == plan.length then 0 else panic! "git-batch: a reply count changed"
    | none => 0
  else
    let cs :=
      plan.map fun x =>
        (b.extract 64 (64 + x.size)).toList ++ List.replicate (x.size - (b.size - 64)) 7
    let bytes := ((plan.zip cs).flatMap fun p => batchHeader p.1.oid p.1.size ++ p.2 ++ [0])
    match parseBatch plan bytes.toByteArray with
    | some cs' =>
      if cs'.map (·.toList) == cs then 0
      else panic! "git-batch: generated replies read back changed"
    | none => panic! "git-batch: generated replies were refused"

end FvdepFuzz
