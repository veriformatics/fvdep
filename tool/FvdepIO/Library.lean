import FvdepCore.Library
import FvdepIO.Cache
import FvdepIO.Git
import Std.Time.DateTime.Timestamp

/-! Library snapshots, the residue (contract `docs/contracts/U5b-oracle.md` L2–L6; ledger residues
`git` (the runs) + `library-store` (the store's filesystem effects)): one source's store under its
lock, at most one fetch into a fresh private bare repository, the reads through the proved readers,
durable publication + `head.json`. Every decision = `FvdepCore.Library` (`start`, `afterPin`,
`afterHead`, `parseTree`, `planTree`, `parseBatch`, the texts). Layout `FVDEP_CACHE/library/v1/
<key>/`: `trees/<commit>/` (published: `.complete` last), `head.json`, `lock` (never deleted),
`tmp/` (an attempt's private repository `<pid>.<n>.git`, its requests file + the tree under
construction `<commit>.<pid>.<n>`: removed after the attempt; every entry stale once the lock is
held). -/

namespace FvdepIO.Library

open FvdepCore.Library
open FvdepCore.Doc (escapeControls)

/-- One source's store (L2) + its settings: the anchored source + its key, the limits, git's
program (`"git"` = through `PATH`), the caller's `PATH`, `HOME` + `SSH_AUTH_SOCK` (git's
environment, L3), the temp-name counter. -/
structure Store where
  dir : System.FilePath
  source : String
  key : String
  limits : Limits
  program : String
  path : Option String
  home : Option String
  sock : Option String
  counter : IO.Ref Nat

/-- The store of the anchored `source` under the cache root `cache`. -/
def Store.of (cache : System.FilePath) (source : String) (limits : Limits)
    (program : String := "git") : IO Store := do
  let key := sourceKey FvdepIO.Hash.sha256Hex source
  return {
      dir := cache / "library" / "v1" / key
      source
      key
      limits
      program
      path := ← IO.getEnv "PATH"
      home := ← IO.getEnv "HOME"
      sock := ← IO.getEnv "SSH_AUTH_SOCK"
      counter := ← IO.mkRef 0 }

def Store.trees (s : Store) : System.FilePath := s.dir / "trees"

def Store.tmp (s : Store) : System.FilePath := s.dir / "tmp"

/-- L6: what is served: the commit, its published tree, the notice (a head served after a
transport failure). -/
structure Served where
  commit : String
  tree : System.FilePath
  notice : Option String

/-- `p`'s type without following a link (`none` = absent or unreadable). -/
def kind (p : System.FilePath) : IO (Option IO.FS.FileType) :=
  tryCatch (some <$> (·.type) <$> p.symlinkMetadata) fun _ => pure none

/-- `p` removed whatever it is, never through a link (a link is removed itself). -/
partial def removeAll (p : System.FilePath) : IO Unit := do
  match ← kind p with
  | some .dir =>
    for d in ← p.readDir do
      removeAll d.path
    IO.FS.removeDir p
  | some _ =>
    IO.FS.removeFile p
  | none =>
    pure ()

/-- L2: `trees/<commit>/` published = a directory holding its regular `.complete` marker. -/
def published (s : Store) (commit : String) : IO Bool := do
  return (← kind (s.trees / commit)) matches some .dir &&
      (← kind (s.trees / commit / ".complete")) matches some .file

/-- One git run of the store in the private repository `repo` (L3's environment), stdin from
`stdinPath`, stdout kept to `outCap` bytes, under the deadline `fetchSeconds`. -/
def Store.run (s : Store) (repo : String) (args : List String) (outCap : Nat)
    (stdinPath : String := "") : IO (Except String FvdepIO.Git.Run) := do
  let deadline := (← IO.monoMsNow) + s.limits.fetchSeconds * 1000
  FvdepIO.Git.run s.program (gitEnv s.source repo s.path s.home s.sock) args stdinPath deadline
      outCap s.limits.gitBytes

/-- A failed git run's reason: its first stderr line, else its end. -/
def reason (s : Store) (r : FvdepIO.Git.Run) : String :=
  match firstLine s.source r.err, r.exit with
  | some l, _ => l
  | none, some c => s!"git exited with {c}"
  | none, none => if r.timedOut then "git passed its deadline" else "git died by a signal"

/-- A run's stdout as text, its final LF dropped. -/
def outText (r : FvdepIO.Git.Run) : String :=
  FvdepCore.Index.Command.textOfBytes (FvdepCore.Index.dropFinalLF r.out)

/-- L3: init + fetch + the fixed ref's check → the fetched commit. -/
def fetchStep (s : Store) (repo : String) (pin : Option String) : IO (Except Fetch String) := do
  match ← s.run repo (initArgs repo) s.limits.gitBytes with
  | .error why =>
    return .error (.localFault why)
  | .ok r =>
    unless r.exit == some 0 do
      return .error (.localFault s!"git init failed: {reason s r}")
  match ← s.run repo (fetchArgs repo s.source pin) s.limits.gitBytes with
  | .error why =>
    return .error (.localFault why)
  | .ok r =>
    if r.timedOut then
      return .error
          (.unclassified s!"git fetch passed its deadline of {s.limits.fetchSeconds} seconds")
    unless r.exit == some 0 do
      return .error
          (if transport r.err then .transport (reason s r) else .unclassified (reason s r))
  let ref := refOf pin
  match ← s.run repo (typeArgs repo ref) 64 with
  | .error why =>
    return .error (.localFault why)
  | .ok r =>
    unless r.exit == some 0 do
      return .error (.received s!"the fetched ref could not be read: {reason s r}")
    unless outText r == "commit" do
      return .error
          (.received
            s!"the fetched ref names a {FvdepCore.Doc.escapeControls (outText r)}, not a commit")
  match ← s.run repo (revArgs repo ref) 64 with
  | .error why =>
    return .error (.localFault why)
  | .ok r =>
    let c := outText r
    unless r.exit == some 0 && FvdepCore.Manifest.isCommit c do
      return .error (.received s!"the fetched ref names no commit: {reason s r}")
    if let some p := pin then
      unless c == p do
        return .error (.received s!"the fetched pin is commit {c}, not {p}")
    return .ok c

/-- L4: the listings (top + each root directory's) → the path-bytes cap over every record →
`planTree` → the blob batch through `parseBatch` → each planned blob with its bytes. -/
def readStep (s : Store) (repo commit : String) (requests : System.FilePath) :
    IO (Except Fetch (List (Blob × ByteArray))) := do
  let snap := s!"the library snapshot {commit}"
  let caps := s.limits.caps
  let over :=
    s!"{snap} lists more than its limits allow ({caps.entries} tree entries, " ++
      s!"{caps.pathTotal} path bytes)"
  let list (args : List String) : IO (Except Fetch (List TreeEntry)) := do
    match ← s.run repo args (listingCap caps) with
    | .error why =>
      return .error (.localFault why)
    | .ok r =>
      if r.outOver then
        return .error (.received over)
      unless r.exit == some 0 do
        return .error (.received s!"{snap} could not be listed: {reason s r}")
      match parseTree r.out with
      | some es =>
        return .ok es
      | none =>
        return .error (.received s!"{snap} {listingReason r.out}")
  let top ←
    match ← list (topArgs repo commit) with
    | .ok es =>
      pure es
    | .error f =>
      return .error f
  let mut subs := []
  for e in top.filter isRootDir do
    match ← list (subArgs repo commit e.path) with
    | .ok es =>
      subs := subs ++ [(e.path, es)]
    | .error f =>
      return .error f
  if let some why := listedRefusal caps (top ++ subs.flatMap (·.2)) then
    return .error (.received s!"{snap} {why}")
  match planTree caps (combine top subs) with
  | .error why =>
    return .error (.received s!"{snap} {why}")
  | .ok plan =>
    IO.FS.writeBinFile requests (batchInput plan)
    match ← s.run repo (batchArgs repo) (batchBytes plan) requests.toString with
    | .error why =>
      return .error (.localFault why)
    | .ok r =>
      unless r.exit == some 0 && !r.outOver do
        return .error (.received s!"{snap}'s blobs could not be read: {reason s r}")
      match parseBatch plan r.out with
      | some cs =>
        return .ok (plan.zip cs)
      | none =>
        return .error (.received s!"{snap}'s blob batch is not the planned blobs")

/-- L5: the tree staged at `stage` (every file 0644 + fsynced, every directory fsynced, then the
`.complete` marker + the staging directory), an incomplete `trees/<commit>/` removed, the rename,
`trees/` fsynced. -/
def publish (s : Store) (commit : String) (files : List (Blob × ByteArray))
    (stage : System.FilePath) : IO (Except String Unit) := do
  let fail (why : String) : Except String Unit :=
    .error s!"the library store of {redact s.source} could not be written: {why}"
  IO.FS.createDirAll stage
  let mut dirs : List System.FilePath := []
  for (b, bytes) in files do
    let p := stage / b.path
    for d in (FvdepIO.Cache.parents stage b.path).reverse do
      unless dirs.contains d do
        IO.FS.createDirAll d
        dirs := d :: dirs
    if let .error why← FvdepIO.Cache.writeDurable p bytes then
      return fail why
    IO.setAccessRights p
        { user := { read := true, write := true }
          group := { read := true }
          other := { read := true } }
  if let .error why← FvdepIO.Cache.syncDirs dirs then
    return fail why
  if let .error why← FvdepIO.Cache.writeDurable (stage / ".complete") .empty then
    return fail why
  if let .error why← FvdepIO.Cache.syncDirs [stage] then
    return fail why
  removeAll (s.trees / commit)
  IO.FS.rename stage (s.trees / commit)
  if let .error why← FvdepIO.Cache.syncDirs [s.trees] then
    return fail why
  return .ok ()

/-- L5: `head.json` ← the head `commit` fetched now (F2's replace). -/
def recordHead (s : Store) (commit : String) : IO (Except String Unit) := do
  let secs := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat
  match FvdepIO.Sys.Path.ofString? s.dir.toString, FvdepIO.Sys.Name.ofString? "head.json" with
  | some dir, some name =>
    match ← FvdepIO.Sys.replace dir name (headText ⟨commit, utcText secs, s.key⟩) with
    | .ok () =>
      return .ok ()
    | .error e =>
      return .error s!"the library store of {redact s.source} could not be written: {e.reason}"
  | _, _ =>
    return .error s!"the library store of {redact s.source} has a path with NUL"

/-- L3–L5: one attempt (`pin`, else the head) in a fresh private bare repository: fetch + ref check,
then — unless `trees/<commit>/` is published — the reads, staging + publication; a head's success
replaces `head.json`. The repository, the requests + the staged tree are removed afterwards whatever
the result (after the runs: each run ends only once its pipes did). -/
def attempt (s : Store) (pin : Option String) : IO Fetch := do
  let n ← s.counter.modifyGet fun n => (n, n + 1)
  let pid ← IO.Process.getPID
  let repo := s.tmp / s!"{pid}.{n}.git"
  let requests := s.tmp / s!"{pid}.{n}.requests"
  let stage ← IO.mkRef (none : Option System.FilePath)
  let body : IO Fetch := do
    let commit ←
      match ← fetchStep s repo.toString pin with
      | .ok c =>
        pure c
      | .error f =>
        return f
    unless ← published s commit do
      let files ←
        match ← readStep s repo.toString commit requests with
        | .ok fs =>
          pure fs
        | .error f =>
          return f
      let dir := s.tmp / s!"{commit}.{pid}.{n}"
      stage.set (some dir)
      if let .error why← publish s commit files dir then
        return .localFault why
    if pin.isNone then
      if let .error why← recordHead s commit then
        return .localFault why
    return .ok commit
  let cleanup : IO Unit := do
    removeAll repo
    removeAll requests
    if let some d← stage.get then
      removeAll d
  let fault (e : IO.Error) : Fetch :=
    .localFault s!"the library store of {redact s.source}: {escapeControls (toString e)}"
  tryFinally (tryCatch body fun e => pure (fault e)) cleanup

/-- L5 + L6: the head record, read after a transport failure: absent, valid (this source's, its
tree published) or damaged. -/
def headState (s : Store) : IO HeadState := do
  match FvdepIO.Sys.Path.ofString? s.dir.toString, FvdepIO.Sys.Name.ofString? "head.json" with
  | some dir, some name =>
    match ← FvdepIO.Sys.readFile dir name 65536 with
    | .error e =>
      return .damaged (damaged s.source s!"head.json could not be read: {e.reason}")
    | .ok none =>
      return .absent
    | .ok (some b) =>
      match recordOf s.key b with
      | .error why =>
        return .damaged (damaged s.source why)
      | .ok h =>
        if ← published s h.commit then
          return .valid h
        return .damaged
            (damaged s.source
              s!"the snapshot {h.commit} that head.json names is missing or incomplete")
  | _, _ =>
    return .damaged (damaged s.source "its path holds a NUL")

/-- L2–L6: the snapshot for `pin` (a project's) or the head: a published pin served at once (no
lock); else the store locked within `lockSeconds` (else `stayedLocked`), stale temps removed,
`start` again → at most one `attempt` → `afterPin` | `afterHead` (the head record read only after a
transport failure) → served | the refusal (exit 2). -/
def snapshot (s : Store) (pin : Option String) : IO (Except String Served) := do
  let ready (pin : Option String) : IO Bool :=
    match pin with
    | some p => published s p
    | none => pure false
  -- A published tree is complete + never removed (L2): a pin served there takes no lock.
  if let .serve c := start pin (← ready pin) then
    return .ok ⟨c, s.trees / c, none⟩
  let locked : IO (Except String Served) := do
    for d in ← s.tmp.readDir do
      removeAll d.path
    let serve (c : String) (notice : Option String) : Except String Served :=
      .ok ⟨c, s.trees / c, notice⟩
    match start pin (← ready pin) with
    | .serve c =>
      return serve c none
    | .fetchPin p =>
      match afterPin p (← attempt s pin) with
      | .serve c n =>
        return serve c n
      | .refuse r =>
        return .error r
    | .fetchHead =>
      let f ← attempt s none
      let hs ←
        if f matches .transport _ then
          headState s
        else
          pure .absent
      match afterHead hs f with
      | .serve c n =>
        return serve c n
      | .refuse r =>
        return .error r
  tryCatch
      (do
        IO.FS.createDirAll s.trees
        IO.FS.createDirAll s.tmp
        let h ← IO.FS.Handle.mk (s.dir / "lock") .append
        unless ← FvdepIO.Cache.exclusive h ((← IO.monoMsNow) + s.limits.lockSeconds * 1000) do
          return .error (stayedLocked s.source)
        tryFinally locked h.unlock)
      fun e => do
      let why := escapeControls (toString e)
      return .error s!"infra io: the library store of {redact s.source}: {why}"

end FvdepIO.Library
