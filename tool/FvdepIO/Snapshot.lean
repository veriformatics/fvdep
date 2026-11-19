import FvdepCore.Phase
import FvdepIO.Spawn
import FvdepIO.Sys

/-! S1's project snapshot (contract `docs/contracts/U5-sandbox.md` S1; residue `project-snapshot`):
each listed module's `A/B.lean` under the project directory, read once — every path component
opened by `openat` without following a link + `fstat`ed on its descriptor (`c/fvdep_snapshot.c`),
each step decided by the pure `FvdepCore.Phase.snapDecide` + `snapRead`, the names first by
`snapNames`. A refusal's detail (the caller's `Obs.infra io`) names the file, the component + the
cause. -/

namespace FvdepIO.Snapshot

open FvdepCore.Phase

/-- S1: `openat(dir, name, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_NOCTTY | O_CLOEXEC)` + `fstat` →
`#[fd, st_mode & S_IFMT, st_size]`; a name other than one plain path component → `EINVAL`. -/
@[extern "fvdep_snapshot_open"]
opaque openAt (dir : UInt32) (name : @& String) : IO (Except Nat (Array Nat))

/-- The project's implementation + proof modules with their bytes, in the listed order. -/
structure Sources where
  impl : List (String × ByteArray)
  proof : List (String × ByteArray)

/-- A descriptor's bytes to its end or until more than `limit` arrived (`EINTR` retried). -/
partial def readCapped (fd : UInt32) (limit : Nat) (acc : ByteArray := .empty) :
    IO (Except Nat ByteArray) := do
  if limit < acc.size then
    return .ok acc
  match ← FvdepIO.Sys.Native.read fd (min 65536 (limit + 1 - acc.size)).toUSize with
  | .error 4 =>
    readCapped fd limit acc
  | .error e =>
    return .error e
  | .ok chunk =>
    if chunk.isEmpty then
      return .ok acc
    else
      readCapped fd limit (acc ++ chunk)

/-- A refusal's cause as text (presentation; ENXIO under `O_RDONLY` = a socket or a device without
a driver, open(2)). -/
def causeText : Refusal → String
  | .notModuleName => "is not a module name"
  | .listedTwice => "is listed twice"
  | .unopened 2 => "does not exist"
  | .unopened 6 => "is a socket or a device without a driver"
  | .unopened 40 => "is a symbolic link"
  | .unopened n => s!"could not be opened ({FvdepIO.Spawn.errnoText n})"
  | .unread n => s!"could not be read ({FvdepIO.Spawn.errnoText n})"
  | .kind .directory => "is a directory"
  | .kind .regular => "is not a directory"
  | .kind .fifo => "is a named pipe (FIFO)"
  | .kind .socket => "is a socket"
  | .kind .charDevice => "is a character device"
  | .kind .blockDevice => "is a block device"
  | .kind .link => "is a symbolic link"
  | .kind (.other m) => s!"has an unsupported file type (mode {m})"
  | .fileOver size cap => s!"has {size} bytes, over the limit of {cap} bytes per source file"
  | .totalOver total cap =>
    s!"brings the sources to {total} bytes, over the limit of {cap} bytes per project snapshot"
  | .grewFile cap => s!"grew past the limit of {cap} bytes per source file while being read"
  | .grewTotal cap => s!"grew while being read, past the limit of {cap} bytes per project snapshot"

/-- A refusal's detail at component path `here` while reading `file`. -/
def detail (file here : String) (r : Refusal) : String :=
  if here == file then s!"{file} {causeText r}" else s!"{file}: {here} {causeText r}"

/-- S1: the file the components `names` lead to from directory `dir` (`seen` = the components
above it): each opened + decided (`snapDecide`), a directory on the way descended into, the leaf
read under its cap (`snapRead`), every descriptor opened here closed on every path → its bytes + the
snapshot's new total. -/
def walk (l : SourceLimits) (used : Nat) (file : String) :
    UInt32 → List String → List String → IO (Except String (ByteArray × Nat))
  | _, _, [] => return .error s!"{file}: no path component"
  | dir, seen, name :: rest => do
    let here := "/".intercalate (seen ++ [name])
    let (opened, fd) ←
      do
        match ← openAt dir name with
        | .error n =>
          pure (Opened.error n, none)
        | .ok #[fd, mode, size] =>
          pure (Opened.file (Kind.ofMode mode) size, some fd.toUInt32)
        | .ok _ =>
          pure (Opened.error 5, none)
    let close : IO Unit :=
      match fd with
      | some fd => discard <| FvdepIO.Sys.Native.close fd
      | none => pure ()
    tryFinally
        (do
          match snapDecide l used rest.isEmpty opened, fd with
          | .refuse r, _ =>
            return .error (detail file here r)
          | .descend, some fd =>
            walk l used file fd (seen ++ [name]) rest
          | .read cap, some fd =>
            match ← readCapped fd cap with
            | .error n =>
              return .error (detail file here (.unread n))
            | .ok bytes =>
              match snapRead l used cap bytes.size with
              | .error r =>
                return .error (detail file here r)
              | .ok total =>
                return .ok (bytes, total)
          | _, none =>
            return .error (detail file here (.unopened 5)))
        close

/-- S1: the snapshot of `impl` + `proof` under the project directory `root` (a link at the root
itself is the user's chosen directory, followed): the names checked first (`snapNames`), then each
module's `A/B.lean` read once (`walk`), the total counted over both lists in order → the first
refusal's detail, else the bytes. -/
def read (root : System.FilePath) (impl proof : List String) (l : SourceLimits := {}) :
    IO (Except String Sources) := do
  if let some (m, r) := snapNames (impl ++ proof) then
    return .error s!"{m} {causeText r}"
  let some p := FvdepIO.Sys.Path.ofString? root.toString
    | return .error s!"the project directory {root.toString.quote} holds a NUL character"
  match ← FvdepIO.Sys.Native.openDir p.toString with
  | .error n =>
    return .error s!"the project directory {root} could not be opened ({FvdepIO.Spawn.errnoText n})"
  | .ok rootFd =>
    tryFinally
        (do
          let mut used := 0
          let mut got : Array (String × ByteArray) := #[]
          for m in impl ++ proof do
            match ← walk l used (stem m ++ ".lean") rootFd.toUInt32 [] (snapPath m) with
            | .error d =>
              return .error d
            | .ok (bytes, total) =>
              used := total
              got := got.push (m, bytes)
          return .ok ⟨got.toList.take impl.length, got.toList.drop impl.length⟩)
        (discard <| FvdepIO.Sys.Native.close rootFd.toUInt32)

end FvdepIO.Snapshot
