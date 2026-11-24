import FvdepCore.Profile.Barrier
import FvdepDev.Parse
import FvdepIO.Parse

/-! Never shipped. `fvdep-dev profile walk` (contract `docs/contracts/U6-profile.md` C1, I, P3–P6):
the shipped child's observation + decision (`FvdepIO.Parse.observe`, `conclude`) in this process —
no step, no request digest, the grammars loaded from the toolchain Lean finds. Prints D1's tail
lines: `grammar <M> <G>…`, then `accepted` | `refused <M> <line>:<column> <cause>` | `over`. -/

namespace FvdepDev.Walk

open FvdepCore.Profile

/-- `fvdep-dev profile walk [--library] [--lib=<M>=<I>,…]… [--limit=<name>=<n>]… <file>…`: module =
the file's stem; `--limit` = P6's `depth`, `nodes`, `batchNodes`. -/
def run (args : List String) : IO UInt32 := do
  let mut role : Role := .consumer
  let mut rows : List LibModule := []
  let mut files : List String := []
  let mut lim : Limits := {}
  for a in args do
    if a == "--library" then
      role := .library
    else
      if a.startsWith "--lib=" then
        match (String.ofList (a.toList.drop 6)).splitOn "=" with
        | [m, is] =>
          rows := rows ++ [⟨m, if is.isEmpty then [] else is.splitOn ","⟩]
        | _ =>
          IO.eprintln "usage: --lib=<M>=<I>,…"
          return 2
      else
        if a.startsWith "--limit=" then
          match (String.ofList (a.toList.drop 8)).splitOn "=" with
          | ["depth", n] =>
            lim := { lim with depth := n.toNat?.getD lim.depth }
          | ["nodes", n] =>
            lim := { lim with nodes := n.toNat?.getD lim.nodes }
          | ["batchNodes", n] =>
            lim := { lim with batchNodes := n.toNat?.getD lim.batchNodes }
          | _ =>
            IO.eprintln "usage: --limit=depth|nodes|batchNodes=<n>"
            return 2
        else
          files := files ++ [a]
  let stem := fun (f : String) =>
    let b := ((f.splitOn "/").getLast?.getD f).toList
    String.ofList (b.take (b.length - 5))
  let named := files.map fun f => (stem f, f)
  let req :=
    requestOf role rows lim (named.map fun x => (x.1, "")) (String.ofList (List.replicate 64 '0'))
  let mut texts := #[]
  for m in req.modules do
    let f := ((named.lookup m.module).getD m.module)
    texts := texts.push ({ m with path := f }, ← IO.FS.readBinFile f)
  let obs ←
    FvdepIO.Parse.observe (fun g => FvdepDev.Parse.grammar (g.map FvdepIO.Parse.nameOf)) req
        texts.toList
  let some (o, gs) := conclude req obs |
    do
      IO.println "short: the observations do not cover the batch"
      return 2
  for (m, g) in req.modules.zip gs do
    unless g.isEmpty do
      IO.println s!"grammar {m.module} {" ".intercalate g}"
  match o with
  | .accepted =>
    IO.println "accepted"
    return 0
  | .refused f =>
    IO.println s!"refused {f.module} {f.line}:{f.column} {" ".intercalate (f.rule :: f.detail)}"
    return 1
  | .over =>
    IO.println "over"
    return 2

end FvdepDev.Walk
