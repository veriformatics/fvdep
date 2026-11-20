import FvdepCore.Index.Command
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

/-! ## L2–L6 the residue's settings + texts (tested; outside the claims) -/

/-- T's library limits (L2–L4): seconds one git process may run, seconds to wait for the store
lock, bytes kept per git diagnostic stream, the tree caps (`treeEntries` = `caps.entries`,
`snapshotBytes` = `caps.totalBytes`). -/
structure Limits where
  fetchSeconds : Nat := 300
  lockSeconds : Nat := 60
  gitBytes : Nat := 65536
  caps : Caps := {}
  deriving DecidableEq, Repr

/-- One `--limit <name>=<n>` of the dev seam (Q3): `none` = no library limit of that name. -/
def Limits.set (l : Limits) (name : String) (n : Nat) : Option Limits :=
  match name with
  | "fetchSeconds" => some { l with fetchSeconds := n }
  | "lockSeconds" => some { l with lockSeconds := n }
  | "gitBytes" => some { l with gitBytes := n }
  | "treeEntries" => some { l with caps := { l.caps with entries := n } }
  | "snapshotBytes" => some { l with caps := { l.caps with totalBytes := n } }
  | _ => none

/-- L3's `-c` settings, in order. -/
def fetchConfig : List String :=
  ["fetch.fsckObjects=true", "fetch.fsck.badFilemode=error",
    "fetch.fsck.gitattributesSymlink=error", "fetch.fsck.gitignoreSymlink=error",
    "fetch.fsck.gitmodulesParse=error", "core.hooksPath=/dev/null", "core.fsmonitor=false",
    "credential.helper=", "credential.interactive=false", "core.sshCommand=ssh -o BatchMode=yes",
    "http.followRedirects=false", "transfer.bundleURI=false", "promisor.acceptFromServer=none",
    "gc.auto=0"]

/-- L3: the fixed ref of a head fetch (`none`) or a pin's. -/
def refOf : Option String → String
  | none => "refs/fvdep/head"
  | some _ => "refs/fvdep/pin"

def refspec : Option String → String
  | none => "+refs/heads/main:refs/fvdep/head"
  | some pin => s!"+{pin}:refs/fvdep/pin"

/-- L3: `git init` of the private repository `repo`. -/
def initArgs (repo : String) : List String := ["init", "--bare", "-q", "--template=", repo]

/-- L3: the fetch (each `-c` value its own element; the source + refspec last). -/
def fetchArgs (repo source : String) (pin : Option String) : List String :=
  fetchConfig.flatMap (fun c => ["-c", c]) ++
    ["-C", repo, "fetch", "--depth=1", "--atomic", "--no-tags", "--no-prune",
      "--no-recurse-submodules", "--no-auto-maintenance", "--no-write-commit-graph",
      "--no-write-fetch-head", "--refmap=", "--", source, refspec pin]

/-- L3–L4: a read of the private repository (no replacement objects, no lazy fetch). -/
def readArgs (repo : String) (rest : List String) : List String :=
  ["--no-replace-objects", "--no-lazy-fetch", "-C", repo] ++ rest

/-- L3: the fixed ref's direct type (`commit` required: a tag is refused) + its object. -/
def typeArgs (repo ref : String) : List String := readArgs repo ["cat-file", "-t", ref]

def revArgs (repo ref : String) : List String := readArgs repo ["rev-parse", "--verify", ref]

/-- L4: the top listing over the roots. -/
def topArgs (repo commit : String) : List String :=
  readArgs repo
    (["ls-tree", "-t", "-l", "-z", "--full-tree", commit, "--"] ++ rootFiles ++ rootDirs)

/-- L4: one root directory's recursive listing (the root = the last element). -/
def subArgs (repo commit root : String) : List String :=
  readArgs repo ["ls-tree", "-r", "-t", "-l", "-z", "--full-tree", commit, "--", root]

/-- L4: the blob batch (its requests on stdin). -/
def batchArgs (repo : String) : List String := readArgs repo ["cat-file", "--batch", "-Z"]

/-- A URL in `scheme://` form (the first `:` opens `://`). -/
def schemeForm (s : String) : Bool := (s.toList.dropWhile (· != ':')).take 3 == [':', '/', '/']

/-- L3: an SSH source (`ssh://`, `git+ssh://`, `ssh+git://`, the scp-like `host:path`). -/
def isSsh (s : String) : Bool :=
  isUrl s &&
    (!schemeForm s || s.startsWith "ssh://" || s.startsWith "git+ssh://" ||
      s.startsWith "ssh+git://")

/-- L3: git's whole environment: `PATH` (the caller's, when set), `LC_ALL=C`, no system or global
config, no prompt or askpass; `HOME` = the private repository `repo` (no ambient `.netrc` or
credentials), except an SSH source: the caller's `HOME` + `SSH_AUTH_SOCK` (its deliberate SSH
authentication). -/
def gitEnv (source repo : String) (path home sock : Option String) : List String :=
  (path.map fun p => "PATH=" ++ p).toList ++
    ["LC_ALL=C", "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=/dev/null", "GIT_TERMINAL_PROMPT=0",
      "GIT_ASKPASS=", "SSH_ASKPASS="] ++
    (if isSsh source then
      (home.map fun h => "HOME=" ++ h).toList ++ (sock.map fun k => "SSH_AUTH_SOCK=" ++ k).toList
    else ["HOME=" ++ repo])

/-- `l` without its trailing CR, space + tab. -/
def trimEnd (l : String) : String :=
  String.ofList (l.toList.reverse.dropWhile fun c => c == '\r' || c == ' ' || c == '\t').reverse

/-- L6's transport class, per stderr line: a line git itself prints before any object of the
candidate arrives (measured, git 2.53.0: a missing repository or ref, a failed name lookup,
connection or authentication); server text (`remote: …`, `remote error: …`) never counts. -/
def transportLine (raw : String) : Bool :=
  let l := trimEnd raw
  !l.startsWith "remote:" && (l.splitOn "remote error:").length == 1 &&
    (l.startsWith "fatal: '" && l.endsWith "' does not appear to be a git repository" ||
      l == "fatal: Could not read from remote repository." ||
      l.startsWith "fatal: unable to access '" ||
      l.startsWith "fatal: couldn't find remote ref " ||
      l.startsWith "fatal: unable to look up " ||
      l.startsWith "fatal: unable to connect to " ||
      l.startsWith "ssh: " ||
      l.startsWith "fatal: repository '" && l.endsWith "' not found" ||
      l == "fatal: unable to get password from user" ||
      l.startsWith "fatal: could not read Username" ||
      l.startsWith "fatal: could not read Password" ||
      l.startsWith "fatal: Authentication failed for '")

/-- L6: a failed fetch's class from its kept stderr: transport when any line is; else the residue
cannot tell (no fallback). -/
def transport (err : ByteArray) : Bool :=
  ((FvdepCore.Index.Command.textOfBytes err).splitOn "\n").any transportLine

/-- `s` with each occurrence of the nonempty `pat` replaced by `r`. -/
def replaceAll (s pat r : String) : String :=
  if pat.isEmpty then s else r.intercalate (s.splitOn pat)

/-- A URL source's userinfo (its authority's part before the last `@`), when nonempty. -/
def userinfo (s : String) : Option String :=
  let auth : List Char :=
    match s.splitOn "://" with
    | _ :: rest@(_ :: _) => ("://".intercalate rest).toList.takeWhile (· != '/')
    | _ => if scpLike s.toList then s.toList.takeWhile (· != ':') else []
  let u := (auth.reverse.dropWhile (· != '@')).reverse.dropLast
  if u.isEmpty then none else some (String.ofList u)

/-- L1: git's text about `source`: its spelling replaced by `redact source`, each other copy of its
userinfo by `***` (a credential never reaches a diagnostic). -/
def scrub (source line : String) : String :=
  let l := replaceAll line source (redact source)
  match userinfo source with
  | some u => replaceAll l u "***"
  | none => l

/-- L3: what a failed git command leaves: the first nonblank line of its kept stderr (`none`: no
such line), its trailing CR + blanks dropped, scrubbed + through §1's line rule. -/
def firstLine (source : String) (err : ByteArray) : Option String :=
  let lines := (FvdepCore.Index.Command.textOfBytes err).splitOn "\n"
  (lines.find? fun l => (trimEnd l).any fun c => !c.isWhitespace).map fun l =>
    FvdepCore.Doc.escapeControls (scrub source (trimEnd l))

/-- A failed git command's reason: `what` + its first line, else its exit. -/
def gitFailure (source what : String) (exit : Option Nat) (err : ByteArray) : String :=
  match firstLine source err, exit with
  | some l, _ => s!"{what}: {l}"
  | none, some c => s!"{what}: git exited with {c}"
  | none, none => s!"{what}: git died by a signal"

/-- L2 + L5: a store fault (`infra io`, exit 2). -/
def damaged (source why : String) : String :=
  s!"infra io: the library store of {redact source} is damaged: {why}"

def stayedLocked (source : String) : String :=
  s!"infra io: the library store of {redact source} stayed locked"

/-- L5: `head.json`'s record for the store of `key`: a record of another source = damaged. -/
def recordOf (key : String) (b : ByteArray) : Except String Head :=
  match headOf b with
  | none => .error "head.json is no head record"
  | some h => if h.source == key then .ok h else .error "head.json names another source"

/-- L4: a root directory's record (its own listing follows). -/
def isRootDir (e : TreeEntry) : Bool := rootDirs.contains e.path && isDir e

/-- L4: the snapshot's entries = the top listing's records in order, each root directory's record
replaced by its own listing (`subs`; git's `-r -t` listing opens with that record) = one
`ls-tree -r -t` over the roots: each entry once. -/
def combine (top : List TreeEntry) (subs : List (String × List TreeEntry)) : List TreeEntry :=
  top.flatMap fun e => if isRootDir e then (subs.lookup e.path).getD [e] else [e]

/-- L4: the cumulative path bytes over every record git printed (the top listing + each root
directory's: a root directory's name counts in both): the first record past `pathTotal` → its
refusal. -/
def listedRefusal (caps : Caps) (records : List TreeEntry) : Option String := go 0 records
where go (n : Nat) : List TreeEntry → Option String
    | [] => none
    | e :: es =>
      if caps.pathTotal < n + e.path.utf8ByteSize then
        some s!"exceeds the limit of {caps.pathTotal} path bytes at {e.path}"
      else go (n + e.path.utf8ByteSize) es

/-- L4: a listing's stdout cap: a record = at most 77 bytes + its path. -/
def listingCap (caps : Caps) : Nat := caps.entries * 80 + caps.pathTotal

/-- Why `parseTree` refused a listing (presentation): a path that is not UTF-8 (a record's other
fields are ASCII), else output outside git's format. -/
def listingReason (b : ByteArray) : String :=
  if (String.fromUTF8? b).isNone then "holds a path that is not valid UTF-8"
  else "printed a tree listing outside git's ls-tree format"

/-- L4: `cat-file --batch -Z`'s requests: each planned object name, NUL-terminated. -/
def batchInput (plan : List Blob) : ByteArray := (plan.flatMap fun x => x.oid ++ [0]).toByteArray

/-- The length of the replies `parseBatch` accepts for `plan` (the stdout cap). -/
def batchBytes (plan : List Blob) : Nat :=
  plan.foldl (fun n x => n + (batchHeader x.oid x.size).length + x.size + 1) 0

/-- `n` as at least `w` decimal digits, zero-padded. -/
def padNat (w n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- L5: `Doc.isUtc`'s text of `secs` seconds after 1970-01-01T00:00:00Z (the proleptic Gregorian
calendar: H. Hinnant's days-to-civil). -/
def utcText (secs : Nat) : String :=
  let days := secs / 86400
  let rem := secs % 86400
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
  s!"{padNat 4 y}-{padNat 2 m}-{padNat 2 d}T{padNat 2 (rem / 3600)}:" ++
    s!"{padNat 2 (rem % 3600 / 60)}:{padNat 2 (rem % 60)}Z"

end FvdepCore.Library
