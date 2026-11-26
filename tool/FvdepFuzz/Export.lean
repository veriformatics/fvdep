import FvdepCore.Export
import FvdepCore.Judge.Compare

/-! Fuzz target `export-decode` (contract U5b X6 + U7 X6/X7): any bytes through the export reader
against fvdep's own Lean (no panic, no hang) + its line rule: an accepted export reads the same with
or without its final LF; + the judge's comparisons on it: every expression + every constant of an
accepted export equals itself (one memo for the run; a budget past the walk's need). A violation
panics. -/

namespace FvdepFuzz

open FvdepCore.Export FvdepCore.Judge

def sameDecls (a b : List Decl) : Bool :=
  a.length == b.length &&
    (a.zip b).all fun (x, y) =>
      x.name == y.name && x.kind == y.kind && x.levelParams == y.levelParams && x.type == y.type &&
        x.value == y.value

/-- U7 X7's reflexivity over one memo: `.differ` = a violation (`.exhausted` is no verdict). -/
def selfEqual (t : Tables) : Bool :=
  Id.run do
    let fuel := 16 * (t.rawNames.size + t.rawLevels.size + t.rawExprs.size) + 64
    let mut seen : Std.HashSet Pair := {}
    for i in [0:t.rawExprs.size] do
      let (c, _, s) := eqExpr t i t i fuel seen
      if c == .differ then
        return false
      seen := s
    for e in t.rawDecls.toList.flatMap entries do
      let (c, _, s) := declEq t e t e fuel seen
      if c == .differ then
        return false
      seen := s
    return true

@[export fvdep_fuzz_export]
def exportTarget (b : ByteArray) : UInt8 :=
  match readTables Lean.githash Lean.versionString b with
  | .error _ => 0
  | .ok t =>
    let ds := t.decls.toList
    let other := if b.size > 0 && b[b.size - 1]! == 10 then b.extract 0 (b.size - 1) else b.push 10
    match read Lean.githash Lean.versionString other with
    | .ok ds' =>
      if !sameDecls ds ds' then panic! "export: the final LF changed the decls"
      else
        if !selfEqual t then panic! "export: a judge comparison found an export unequal to itself"
        else 0
    | .error _ => panic! "export: the final LF changed acceptance"

end FvdepFuzz
