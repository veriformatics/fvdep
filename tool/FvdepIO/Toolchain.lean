import FvdepCore.Build
import FvdepIO.Sha256
import FvdepIO.Sys

/-! T1's toolchain fingerprint (contract `docs/contracts/U5-sandbox.md` T1; residue `cache-fs`): the
SHA-256 of `fingerprintText` over `bin/lean`, `bin/leanexport` + every file under `lib/lean`,
computed once per install + kept in `FVDEP_CACHE/toolchains/v1/<release>.json` while the tree's
stat stamp holds. -/

namespace FvdepIO.Toolchain

open FvdepCore.Build

/-- I1: the Lean release fvdep was built against (version + githash: build-time constants; never
`/` or `:`, so it names the record's file). -/
def release : String := Lean.versionString ++ "+" ++ Lean.githash

/-- Every regular file under `root / rel` (relative paths `rel/…`); a link or special file → its
path as the error (T1 hashes contents alone: 4.35.0's `lib/lean` holds none). -/
partial def walk (root : System.FilePath) (rel : String) (acc : Array (String × IO.FS.Metadata)) :
    IO (Except String (Array (String × IO.FS.Metadata))) := do
  let mut acc := acc
  for e in ← (root / rel).readDir do
    let r := rel ++ "/" ++ e.fileName
    let md ← e.path.symlinkMetadata
    match md.type with
    | .dir =>
      match ← walk root r acc with
      | .ok a =>
        acc := a
      | .error p =>
        return .error p
    | .file =>
      acc := acc.push (r, md)
    | _ =>
      return .error r
  return .ok acc

/-- T1's files with their metadata. -/
def files (sys : System.FilePath) : IO (Except String (Array (String × IO.FS.Metadata))) := do
  let mut acc := #[]
  for tool in ["bin/lean", "bin/leanexport"] do
    let md ← (sys / tool).symlinkMetadata
    unless md.type == .file do
      return .error tool
    acc := acc.push (tool, md)
  walk sys "lib/lean" acc

/-- T1's stat stamp: file count, total bytes, newest modification time. -/
def stampOf (fs : Array (String × IO.FS.Metadata)) : Stamp :=
  fs.foldl
    (fun s f =>
      let t := f.2.modified
      let sec := t.sec.toNat
      let nsec := t.nsec.toNat
      { files := s.files + 1
        bytes := s.bytes + f.2.byteSize.toNat
        sec := if s.sec < sec || (s.sec == sec && s.nsec < nsec) then sec else s.sec
        nsec := if s.sec < sec || (s.sec == sec && s.nsec < nsec) then nsec else s.nsec })
    { files := 0, bytes := 0, sec := 0, nsec := 0 }

/-- T1: the fingerprint of the toolchain at `sys`, from the record under `cache` while its stamp +
release hold, else recomputed + recorded (`replace`: concurrent computations race to the same
bytes). -/
def fingerprint (cache sys : System.FilePath) : IO (Except String String) := do
  let fs ←
    match ← files sys with
    | .ok fs =>
      pure fs
    | .error p =>
      return .error s!"{sys / p} is a link or special file, not a regular file"
  let stamp := stampOf fs
  let dir := cache / "toolchains" / "v1"
  let name := release ++ ".json"
  let stored ← tryCatch (some <$> IO.FS.readBinFile (dir / name)) fun _ => pure none
  if let some f := stored.bind fingerprintOf then
    if f.release == release && f.stamp == stamp then
      return .ok f.value
  let mut recs := #[]
  for (p, md) in fs do
    recs :=
      recs.push
        { path := p
          size := md.byteSize.toNat
          sha256 := FvdepCore.Hash.hex (← FvdepIO.Hash.sha256File (sys / p)) }
  let value := FvdepIO.Hash.sha256Hex (fingerprintText recs.toList)
  IO.FS.createDirAll dir
  match FvdepIO.Sys.Path.ofString? dir.toString, FvdepIO.Sys.Name.ofString? name with
  | some d, some n =>
    match ← FvdepIO.Sys.replace d n (fingerprintRecord { release, value, stamp }) with
    | .ok () =>
      return .ok value
    | .error e =>
      return .error e.reason
  | _, _ =>
    return .error s!"{dir / name} cannot be written"

end FvdepIO.Toolchain
