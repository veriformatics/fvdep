import FvdepDev.Parse

/-! Never shipped. `fvdep-dev profile kinds <file>…` (contract U6 Q: the corpus dump the allowlist
is read from): each file parsed in the trusted grammar (`Init` + `Std`), then one line per node
kind, per atom (with its parent's kind) + per identifier under a kind whose names the profile checks
(attributes, options, namespaces, opens); a refusal → its line on stderr, exit 1. -/

namespace FvdepDev.Profile

open FvdepDev.ProfileTree

def usage : String := "usage: fvdep-dev profile (kinds|idents|parse) <file>... | profile scoped\n"

def dotted (xs : List String) : String := ".".intercalate xs

/-- Kinds whose identifier leaves the profile checks by name. -/
def named (k : String) : Bool :=
  ["Attr", "set_option", "namespace", "open", "section", "end", "deriving"].any fun p =>
    (k.splitOn p).length > 1

/-- The dump lines of `t` under the parent kind `parent`. -/
partial def dump (parent : String) : Tree → List String
  | .node k _ kids =>
    let kk := dotted k
    s!"node\t{kk}" :: kids.flatMap (dump kk)
  | .atom t _ => [s!"atom\t{parent}\t{t}"]
  | .ident n _ => if named parent then [s!"ident\t{parent}\t{dotted n}"] else []
  | .missing => [s!"missing\t{parent}"]

/-- Every identifier leaf's components. -/
partial def idents : Tree → List (List String)
  | .node _ _ kids => kids.flatMap idents
  | .ident n _ => [n]
  | _ => []

def run : List String → IO UInt32
  | "kinds" :: files@(_ :: _) => do
    let env ← FvdepDev.Parse.grammar [`Init, `Std]
    let mut rc : UInt32 := 0
    for f in files do
      let text ← IO.FS.readFile f
      match ← FvdepDev.Parse.parseModule env {} f text with
      | .ok ts =>
        for t in ts do
          for l in dump "" t do
            IO.println l
      | .error why =>
        IO.eprintln why
        rc := 1
    return rc
  | "idents" :: files@(_ :: _) => do
    let env ← FvdepDev.Parse.grammar [`Init, `Std]
    for f in files do
      match ← FvdepDev.Parse.parseModule env {} f (← IO.FS.readFile f) with
      | .ok ts =>
        for t in ts do
          for n in idents t do
            IO.println (dotted n)
      | .error why =>
        IO.eprintln why
    return 0
  | ["scoped"] => do
    for mods in [[`Init], [`Init, `Std]] do
      let env ← FvdepDev.Parse.grammar mods
      let st := Lean.Parser.parserExtension.ext.getState env
      let keys := st.scopedEntries.map.toList.map fun e => (e.1, e.2.size)
      IO.println s!"grammar {mods}: {keys.length} namespaces with scoped parser entries"
      for (ns, n) in keys do
        IO.println s!"  {ns} {n}"
    return 0
  | "parse" :: files@(_ :: _) => do
    let env ← FvdepDev.Parse.grammar [`Init, `Std]
    for f in files do
      let text ← IO.FS.readFile f
      let t0 ← IO.monoMsNow
      let r ← FvdepDev.Parse.parseModule env {} f text
      let t1 ← IO.monoMsNow
      match r with
      | .ok ts =>
        IO.println s!"{f}: {ts.length} trees, {t1 - t0} ms"
      | .error why =>
        IO.println s!"{f}: refused ({why.take 80}), {t1 - t0} ms"
    return 0
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Profile
