import FvdepCore.Bundle
import FvdepIO.Phase

/-! B2's failure bundle (contract `docs/contracts/U5-sandbox.md` B2; residue `failure-bundle`): a
failing step's record (`bundle.json`) + copies of its required inputs + its kept streams under
`FVDEP_CACHE/bundles/v1/<recipe digest>-<phase>-<module|step>-<attempt>/`, staged under
`bundles/tmp/` + renamed in under `bundles/lock`; one bound over everything (inputs omitted largest
first: `omitOrder`), the newest 16 kept (`retainPick`). The caller turns a failure here into a
warning: a bundle never changes the observation. -/

namespace FvdepIO.Bundle

open FvdepCore.Bundle FvdepCore.Build FvdepCore.Json

/-- B2's bound over a bundle (metadata + streams + copies): 32 MiB. -/
def cap : Nat := 33554432

/-- B2: the bundles retention keeps. -/
def keep : Nat := 16

/-- The attempt after the highest one `names` hold for `base` (`<base>-<attempt>`). -/
def nextAttempt (base : String) (names : List String) : Nat :=
  1 +
    names.foldl
      (fun acc s =>
        if s.startsWith (base ++ "-") then
          max acc ((String.ofList (s.toList.drop (base.length + 1))).toNat?.getD 0)
        else acc)
      0

/-- A bundle directory's age: its `bundle.json`'s modification time (ns), 0 when unreadable. -/
def age (d : System.FilePath) : IO Nat := do
  try
    let t := (← (d / "bundle.json").symlinkMetadata).modified
    return t.sec.toNat * 1000000000 + t.nsec.toNat
  catch _ =>
    return 0

/-- B2: `c`'s bundle written + the store trimmed to the newest `keep` → its directory + whether it
is complete (every required input kept). -/
def write (root : System.FilePath) (recipe : Recipe) (lim : FvdepCore.Sandbox.Limits)
    (c : FvdepIO.Phase.Capture) : IO (Except String (System.FilePath × Bool)) := do
  let store := root / "bundles" / "v1"
  let staging := root / "bundles" / "tmp"
  IO.FS.createDirAll store
  IO.FS.createDirAll staging
  let lk ← IO.FS.Handle.mk (root / "bundles" / "lock") .append
  lk.lock (exclusive := true)
  try
    let mut files : Array (String × System.FilePath × FileRec) := #[]
    for (role, d) in c.inputs do
      if ← d.pathExists then
        match ← FvdepIO.Cache.listing d true with
        | some recs =>
          for x in recs.qsort (fun a b => a.path < b.path) do
            files := files.push (role, d / x.path, x)
        | none =>
          return .error s!"the {role} input {d} holds a link or a special file"
    let streams := c.stdout.size + c.stderr.size
    let draft : Record :=
      { recipe
        limits := lim
        phase := c.phase
        step := c.step
        module := c.module
        imports := c.imports
        roots := c.roots
        presence := c.presence
        inputs :=
          files.toList.map fun f =>
            { role := f.1, path := f.2.2.path, size := f.2.2.size, sha256 := f.2.2.sha256,
              kept := false } }
    let budget := cap - min cap (streams + (print draft.value).size)
    let omitted :=
      omitOrder (files.toList.map fun f => (f.1 ++ "/" ++ f.2.2.path, f.2.2.size)) budget
    let record : Record :=
      { draft with
        inputs :=
          draft.inputs.map fun i => { i with kept := !omitted.contains (i.role ++ "/" ++ i.path) } }
    let base :=
      s!"{String.ofList ((FvdepIO.Hash.sha256Hex (print (recipeValue recipe))).toList.take 16)}-" ++
        s!"{c.phase}-" ++
        (if c.module.isEmpty then c.step else c.module)
    let names := (← store.readDir).toList.map (·.fileName)
    let name := s!"{base}-{nextAttempt base names}"
    let tmp := staging / s!"{name}.{← IO.Process.getPID}"
    if ← tmp.pathExists then
      IO.FS.removeDirAll tmp
    IO.FS.createDirAll tmp
    for (role, src, x) in files do
      unless omitted.contains (role ++ "/" ++ x.path) do
        let dst := tmp / "inputs" / role / x.path
        if let some p := dst.parent then
          IO.FS.createDirAll p
        IO.FS.writeBinFile dst (← IO.FS.readBinFile src)
    IO.FS.writeBinFile (tmp / "stdout.txt") c.stdout
    IO.FS.writeBinFile (tmp / "stderr.txt") c.stderr
    IO.FS.writeBinFile (tmp / "bundle.json") (print record.value)
    IO.FS.rename tmp (store / name)
    let mut aged := #[]
    for d in ← store.readDir do
      if (← d.path.symlinkMetadata).type == .dir then
        aged := aged.push (d.fileName, ← age d.path)
    for old in retainPick aged.toList keep do
      IO.FS.removeDirAll (store / old)
    return .ok (store / name, record.complete)
  catch ex =>
    return .error s!"the failure bundle could not be written: {ex}"
  finally
    lk.unlock

end FvdepIO.Bundle
