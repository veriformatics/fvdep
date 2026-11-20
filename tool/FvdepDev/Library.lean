import FvdepCore.Library

/-! `fvdep-dev library tree|plan <file>` (contract U5b L4; never shipped): a saved `git ls-tree
-r -t -l -z` output through `FvdepCore.Library.parseTree` → one line per entry (mode, type, object,
size, path), or through `planTree` (default caps) → one line per planned blob + the count;
`library batch <tree> <replies>` → the planned blobs' `cat-file --batch -Z` replies through
`parseBatch` → their count + bytes; a refusal → its reason, exit 1. -/

namespace FvdepDev.Library

open FvdepCore.Library

def usage : String :=
  "usage: fvdep-dev library (tree|plan) <file> | library batch <tree> <replies>\n"

def bytesText (bs : List UInt8) : String := String.ofList (bs.map charOf)

def run : List String → IO UInt32
  | ["batch", tree, replies] => do
    let some es := parseTree (← IO.FS.readBinFile tree) |
      do
        IO.println "refused: not an ls-tree -z -l listing"
        return 1
    let .ok plan := planTree {} es |
      do
        IO.println "refused: the listing's plan"
        return 1
    match parseBatch plan (← IO.FS.readBinFile replies) with
    | none =>
      IO.println "refused: not the planned batch replies"
      return 1
    | some cs =>
      IO.println s!"blobs {cs.length} bytes {cs.foldl (· + ·.size) 0}"
      return 0
  | [cmd, file] => do
    let b ← IO.FS.readBinFile file
    match parseTree b, cmd with
    | none, _ =>
      IO.println "refused: not an ls-tree -z -l listing"
      return 1
    | some es, "tree" =>
      for e in es do
        let size :=
          match e.size with
          | some n => toString n
          | none => "-"
        IO.println s!"{bytesText e.mode} {repr e.kind} {bytesText e.oid} {size} {e.path}"
      IO.println s!"entries {es.length}"
      return 0
    | some es, "plan" =>
      match planTree {} es with
      | .error why =>
        IO.println s!"refused: the library snapshot {why}"
        return 1
      | .ok bs =>
        for x in bs do
          IO.println s!"{x.path} {bytesText x.oid} {x.size}"
        IO.println s!"blobs {bs.length}"
        return 0
    | _, _ =>
      do
        IO.eprint usage
        return 2
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Library
