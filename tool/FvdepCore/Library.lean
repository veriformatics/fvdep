import FvdepCore.Index.Assemble
import FvdepCore.Manifest
import FvdepCore.Step

/-! Library snapshots, the pure parts (contract `docs/contracts/U5b-oracle.md` L1–L7): the source
+ its key, the head record, git's two machine outputs read exactly (`ls-tree -z -l` records,
`cat-file --batch -Z` replies), the tree policy, the toolchain check + the snapshot selection
table. git + the store's filesystem effects = `FvdepIO.Library` (residues `git`,
`library-store`). Byte inputs are read by offsets: a snapshot reaches 64 MiB. -/

namespace FvdepCore.Library

open FvdepCore.Json

/-! ## L1 the source -/

def defaultSource : String := "https://github.com/veriformatics/fvdep"

/-- L1: `FVDEP_LIBRARY_URL`'s value → the source (unset or empty → the default). -/
def sourceOf : Option String → String
  | none => defaultSource
  | some s => if s == "" then defaultSource else s

/-- git's scp-like form: a `:` with no `/` before the first one. -/
def scpLike : List Char → Bool
  | [] => false
  | ':' :: _ => true
  | '/' :: _ => false
  | _ :: cs => scpLike cs

/-- L1: git's rule (`url_is_local_not_ssh`, Linux): a `:` before any `/` = a URL (`scheme://…`, the
scp-like `host:path`); anything else = a local path. -/
def isUrl (s : String) : Bool := scpLike s.toList

/-- L1: the anchored source: a URL as written, a local path made absolute against the working
directory `cwd` (taken before any directory change; no normalization). -/
def anchor (cwd s : String) : String :=
  if isUrl s || s.startsWith "/" then s else if cwd.endsWith "/" then cwd ++ s else cwd ++ "/" ++ s

/-- L1: the source's key = `h` (SHA-256 hex in IO) over the anchored spelling's UTF-8 bytes. -/
def sourceKey (h : ByteArray → String) (anchored : String) : String := h anchored.toUTF8

/-- `cs` with the part before its last `@` replaced by `***` (no `@` → unchanged). -/
def maskUser (cs : List Char) : List Char :=
  if cs.contains '@' then "***".toList ++ (cs.reverse.takeWhile (· != '@')).reverse.cons '@' else cs

/-- L1: a diagnostic's spelling of a source: a URL's userinfo replaced by `***` (`scheme://u@h/p`
→ `scheme://***@h/p`; scp-like `u@h:p` → `***@h:p`); a local path unchanged. -/
def redact (s : String) : String :=
  match s.splitOn "://" with
  | scheme :: rest@(_ :: _) =>
    let r := ("://".intercalate rest).toList
    let auth := r.takeWhile (· != '/')
    scheme ++ "://" ++ String.ofList (maskUser auth ++ r.dropWhile (· != '/'))
  | _ =>
    if scpLike s.toList then
      let host := s.toList.takeWhile (· != ':')
      String.ofList (maskUser host ++ s.toList.dropWhile (· != ':'))
    else s

/-! ## L5 the head record -/

/-- L5: the last complete head materialization of a source. -/
structure Head where
  commit : String
  fetched : String
  source : String
  deriving DecidableEq, Repr

/-- L5: a commit (40 lowercase hex), a UTC time (`Doc.isUtc`), a source key (64 lowercase hex). -/
def Head.wf (h : Head) : Bool :=
  FvdepCore.Manifest.isCommit h.commit && FvdepCore.Doc.isUtc h.fetched &&
    FvdepCore.Doc.isDigest h.source

def Head.toJson (h : Head) : Value :=
  .obj
    [("commit", .str h.commit), ("fetched", .str h.fetched), ("schema", .int 1),
      ("source", .str h.source)]

/-- L5: `head.json`'s bytes: canonical J text + LF. -/
def headText (h : Head) : ByteArray := (print h.toJson).push 0x0A

/-- L5: a `head.json` read back: its record when the bytes are exactly a well-formed record's
`headText`, else `none` (= damaged). -/
def headOf (b : ByteArray) : Option Head :=
  match decode (FvdepCore.Index.dropFinalLF b) with
  | .ok (.obj [("commit", .str c), ("fetched", .str f), ("schema", .int 1), ("source", .str s)]) =>
    let h : Head := ⟨c, f, s⟩
    if h.wf && (headText h).data == b.data then some h else none
  | _ => none

/-! ## L4 git's machine output -/

/-- A tree entry's object type. -/
inductive ObjKind where
  | blob
  | tree
  | commit
  deriving DecidableEq, Repr

/-- One `ls-tree -z -l` record: mode (6 octal digit bytes as printed), type, object name (40
lowercase hex bytes), a blob's size (`none` = git's `-`), path. -/
structure TreeEntry where
  mode : List UInt8
  kind : ObjKind
  oid : List UInt8
  size : Option Nat
  path : String
  deriving DecidableEq, Repr

def byteOf (c : Char) : UInt8 := c.toNat.toUInt8

def charOf (b : UInt8) : Char := Char.ofNat b.toNat

/-- A decimal number's bytes. -/
def digits (n : Nat) : List UInt8 := (FvdepCore.Ids.decimal n).map byteOf

def isOctal (b : UInt8) : Bool := 48 ≤ b && b ≤ 55

def isHexByte (b : UInt8) : Bool := (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102)

def isDigitByte (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- `ls-tree`'s size column: `%7s`, right-justified in at least 7 bytes. -/
def pad7 (t : List UInt8) : List UInt8 := List.replicate (7 - t.length) 32 ++ t

/-- The type's name + the size column's text it allows. -/
def kindOf : List UInt8 → Option (ObjKind × List UInt8)
  | 98 :: 108 :: 111 :: 98 :: 32 :: rest => some (.blob, rest)
  | 116 :: 114 :: 101 :: 101 :: 32 :: rest => some (.tree, rest)
  | 99 :: 111 :: 109 :: 109 :: 105 :: 116 :: 32 :: rest => some (.commit, rest)
  | _ => none

/-- A size column's text: a blob's canonical decimal, another type's `-`. -/
def sizeField : ObjKind → List UInt8 → Option (Option Nat)
  | .blob, t => if t.all isDigitByte then (FvdepCore.Ids.parseNat (t.map charOf)).map some else none
  | _, t => if t == [45] then some none else none

/-- L4: one record (the bytes between NULs): `mode SP type SP oid SP size7 TAB path`, exactly. -/
def parseRecord (r : List UInt8) : Option TreeEntry :=
  let mode := r.take 6
  if mode.length == 6 && mode.all isOctal then
    match r.drop 6 with
    | 32 :: rest =>
      match kindOf rest with
      | some (kind, rest) =>
        let oid := rest.take 40
        if oid.length == 40 && oid.all isHexByte then
          match rest.drop 40 with
          | 32 :: rest =>
            let field := rest.takeWhile (· != 9)
            match rest.dropWhile (· != 9) with
            | 9 :: path =>
              let text := field.dropWhile (· == 32)
              if pad7 text == field then
                match sizeField kind text, FvdepCore.Hash.text path with
                | some size, some p =>
                  if path != [] && !path.contains 0 then some ⟨mode, kind, oid, size, p⟩ else none
                | _, _ => none
              else none
            | _ => none
          | _ => none
        else none
      | none => none
    | _ => none
  else none

/-- The first NUL at or after `i`, else `b.size`. -/
def nulEnd (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then if b[i] == 0 then i else nulEnd b (i + 1) else b.size
termination_by b.size - i

theorem le_nulEnd (b : ByteArray) (i : Nat) (hi : i ≤ b.size) : i ≤ nulEnd b i := by
  unfold nulEnd
  split
  · rename_i h
    split
    · exact Nat.le_refl i
    · exact Nat.le_trans (Nat.le_succ i) (le_nulEnd b (i + 1) h)
  · exact hi
termination_by b.size - i

/-- L4: `ls-tree -z -l`'s records from byte `i` on (`acc` newest first): each NUL-terminated + one
record exactly; an unterminated tail or a record of another form = `none`. -/
def parseTreeFrom (b : ByteArray) (i : Nat) (acc : List TreeEntry) : Option (List TreeEntry) :=
  if h : i < b.size then
    have := le_nulEnd b i (Nat.le_of_lt h)
    if nulEnd b i < b.size then
      match parseRecord (b.extract i (nulEnd b i)).data.toList with
      | some e => parseTreeFrom b (nulEnd b i + 1) (e :: acc)
      | none => none
    else none
  else some acc.reverse
termination_by b.size - i
decreasing_by omega

/-- L4: a whole `ls-tree -z -l` output. -/
def parseTree (b : ByteArray) : Option (List TreeEntry) := parseTreeFrom b 0 []

/-- A planned blob: path, object name bytes, size. -/
structure Blob where
  path : String
  oid : List UInt8
  size : Nat
  deriving DecidableEq, Repr

/-- `cat-file --batch -Z`'s header for a planned blob: `oid SP blob SP size NUL`. -/
def batchHeader (oid : List UInt8) (size : Nat) : List UInt8 :=
  oid ++ [32, 98, 108, 111, 98, 32] ++ digits size ++ [0]

/-- `xs` occurs in `b` at `i`. -/
def bytesAt (b : ByteArray) (i : Nat) : List UInt8 → Bool
  | [] => true
  | x :: xs => if h : i < b.size then b[i] == x && bytesAt b (i + 1) xs else false

/-- L4: the batch reply to the planned blobs from byte `i` on: per blob its exact header, then
`size` content bytes, then NUL; nothing after the last. -/
def parseBatchFrom (b : ByteArray) (i : Nat) : List Blob → List ByteArray → Option (List ByteArray)
  | [], acc => if i == b.size then some acc.reverse else none
  | x :: xs, acc =>
    let hd := batchHeader x.oid x.size
    let j := i + hd.length
    if bytesAt b i hd && j + x.size < b.size && b[j + x.size]! == 0 then
      parseBatchFrom b (j + x.size + 1) xs (b.extract j (j + x.size) :: acc)
    else none

def parseBatch (plan : List Blob) (b : ByteArray) : Option (List ByteArray) :=
  parseBatchFrom b 0 plan []

/-! ## L4 the tree policy -/

/-- L4: the library's roots: the three directories + the six files. -/
def rootDirs : List String := ["Fvdep", "FvdepPreview", "FvdepProofs"]

def rootFiles : List String :=
  ["lakefile.lean", "lean-toolchain", "index.json", "Fvdep.lean", "FvdepPreview.lean",
    "FvdepProofs.lean"]

/-- L4: the files a library must hold. -/
def required : List String :=
  ["lakefile.lean", "lean-toolchain", "index.json", "Fvdep.lean", "Fvdep/Registry.lean"]

/-- L4's caps (T): entries, path bytes, depth, cumulative path bytes, file + total blob bytes. -/
structure Caps where
  entries : Nat := 10000
  pathBytes : Nat := 4096
  depth : Nat := 32
  pathTotal : Nat := 4194304
  fileBytes : Nat := 1048576
  totalBytes : Nat := 67108864
  deriving DecidableEq, Repr

def modeTree : List UInt8 := [48, 52, 48, 48, 48, 48]

def modeFile : List UInt8 := [49, 48, 48, 54, 52, 52]

def modeExec : List UInt8 := [49, 48, 48, 55, 53, 53]

def modeLink : List UInt8 := [49, 50, 48, 48, 48, 48]

def modeGitlink : List UInt8 := [49, 54, 48, 48, 48, 48]

/-- A path component fvdep accepts: nonempty, not starting with `.` (also excludes `..`). -/
def plainComponent (c : String) : Bool := c != "" && c.toList.head? != some '.'

/-- L4: a plain path within the path caps. -/
def pathOk (caps : Caps) (p : String) : Bool :=
  FvdepCore.Step.safePath p && (p.splitOn "/").all plainComponent &&
    (decide (p.utf8ByteSize ≤ caps.pathBytes) && decide ((p.splitOn "/").length ≤ caps.depth))

/-- L4: a directory (`040000 tree`) or a file (`100644`/`100755 blob`). -/
def isDir (e : TreeEntry) : Bool := e.kind == .tree && e.mode == modeTree

def isFile (e : TreeEntry) : Bool := e.kind == .blob && (e.mode == modeFile || e.mode == modeExec)

/-- L4: a root directory or root file of its kind, or a directory or file inside a root
directory. -/
def placed (e : TreeEntry) : Bool :=
  match e.path.splitOn "/" with
  | [r] => (rootDirs.contains r && isDir e) || (rootFiles.contains r && isFile e)
  | r :: _ :: _ => rootDirs.contains r && (isDir e || isFile e)
  | [] => false

/-- Why a path fails `pathOk`: unsafe, then over the byte cap, else over the depth cap. -/
def pathReason (caps : Caps) (p : String) : String :=
  if !(FvdepCore.Step.safePath p && (p.splitOn "/").all plainComponent) then
    s!"holds an unsafe path at {p}"
  else
    if caps.pathBytes < p.utf8ByteSize then s!"holds a path over {caps.pathBytes} bytes at {p}"
    else s!"holds a path deeper than {caps.depth} components at {p}"

/-- L4: an entry's own refusal (its path, then its placement + mode), before the running caps. -/
def entryRefusal (caps : Caps) (e : TreeEntry) : Option String :=
  if !pathOk caps e.path then some (pathReason caps e.path)
  else
    if placed e then none
    else
      if e.mode == modeLink then some s!"holds a link at {e.path}"
      else
        if e.mode == modeGitlink then some s!"holds a submodule at {e.path}"
        else
          if isDir e || isFile e then some s!"holds an unexpected entry at {e.path}"
          else some s!"holds an entry of mode {String.ofList (e.mode.map charOf)} at {e.path}"

/-- L4 (`planTree`'s loop): entries in listing order with the running entry count, path bytes +
blob bytes; `acc` = the planned blobs so far (newest first). -/
def planFrom (caps : Caps) (n paths total : Nat) (acc : List Blob) :
    List TreeEntry → Except String (List Blob)
  | [] => .ok acc.reverse
  | e :: es =>
    match entryRefusal caps e with
    | some why => .error why
    | none =>
      let n := n + 1
      let paths := paths + e.path.utf8ByteSize
      let size := if e.kind == .blob then e.size.getD 0 else 0
      let total := total + size
      if caps.entries < n || caps.pathTotal < paths then
        .error
          (if caps.entries < n then s!"exceeds the limit of {caps.entries} tree entries at {e.path}"
          else s!"exceeds the limit of {caps.pathTotal} path bytes at {e.path}")
      else
        if e.kind == .blob && (caps.fileBytes < size || caps.totalBytes < total) then
          .error
            (s!"exceeds the size limits ({caps.fileBytes} bytes per file, {caps.totalBytes} " ++
              s!"bytes in total) at {e.path}")
        else
          planFrom caps n paths total
            (if e.kind == .blob then ⟨e.path, e.oid, size⟩ :: acc else acc) es

/-- L4: the snapshot's blobs (path, object, size) in listing order, or the reason the listing is
refused (the first violating entry, then a missing required file). -/
def planTree (caps : Caps) (es : List TreeEntry) : Except String (List Blob) := do
  let blobs ← planFrom caps 0 0 0 [] es
  match required.find? fun p => !blobs.any (·.path == p) with
  | some _ =>
    .error "is no fvdep library"
  | none =>
    .ok blobs

/-! ## L7 the toolchain -/

/-- L7: the served tree's `lean-toolchain` (trimmed as U4 C1) against fvdep's: `none` = equal,
else the refusal (interface §1). -/
def toolchainRefusal (commit theirs ours : String) : Option String :=
  let t := FvdepCore.Index.Assemble.trimText theirs
  if t == ours then none
  else
    some
      (s!"Library commit {commit} uses Lean {t}; this fvdep checks Lean {ours}. " ++
        "Install the matching fvdep or change the library pin.")

/-! ## L6 selection -/

/-- L6: a fetch's outcome class. -/
inductive Fetch where
  | ok (commit : String)
  | transport (reason : String)
  | received (reason : String)
  | localFault (reason : String)
  | unclassified (reason : String)
  deriving DecidableEq, Repr

/-- L5 + L6: the head record's state. -/
inductive HeadState where
  | absent
  | valid (h : Head)
  | damaged (reason : String)
  deriving DecidableEq, Repr

/-- L6: before any fetch: a pin whose tree is published = served; else which fetch. -/
inductive Start where
  | serve (commit : String)
  | fetchPin (commit : String)
  | fetchHead
  deriving DecidableEq, Repr

def start : Option String → Bool → Start
  | some pin, true => .serve pin
  | some pin, false => .fetchPin pin
  | none, _ => .fetchHead

/-- L6: the selection: the served commit + a stderr notice, or the refusal (exit 2). -/
inductive Selected where
  | serve (commit : String) (notice : Option String)
  | refuse (reason : String)
  deriving DecidableEq, Repr

/-- L6 after a pin fetch: its tree, or `Fetch failed` (a pin never falls back). -/
def afterPin (pin : String) : Fetch → Selected
  | .ok _ => .serve pin none
  | .transport r | .received r | .localFault r | .unclassified r => .refuse s!"Fetch failed: {r}."

/-- L6 after a head fetch: its tree; a transport failure → the last head (+ notice) or `never`;
any other failure → its reason, no fallback; a damaged head record = a store fault. -/
def afterHead (head : HeadState) : Fetch → Selected
  | .ok c => .serve c none
  | .transport r =>
    match head with
    | .valid h => .serve h.commit (some s!"Fetch failed: {r}. Last successful fetch: {h.fetched}.")
    | .absent => .refuse s!"Fetch failed: {r}. Last successful fetch: never."
    | .damaged why => .refuse why
  | .received r | .localFault r | .unclassified r => .refuse s!"Fetch failed: {r}."

end FvdepCore.Library
