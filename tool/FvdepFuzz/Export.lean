import FvdepCore.Export

/-! Fuzz target `export-decode` (contract U5b X6): any bytes through the export reader against
fvdep's own Lean (no panic, no hang) + its line rule: an accepted export reads the same with or
without its final LF; a violation panics. -/

namespace FvdepFuzz

open FvdepCore.Export

def sameDecls (a b : List Decl) : Bool :=
  a.length == b.length &&
    (a.zip b).all fun (x, y) =>
      x.name == y.name && x.kind == y.kind && x.levelParams == y.levelParams && x.type == y.type &&
        x.value == y.value

@[export fvdep_fuzz_export]
def exportTarget (b : ByteArray) : UInt8 :=
  match read Lean.githash Lean.versionString b with
  | .error _ => 0
  | .ok ds =>
    let other := if b.size > 0 && b[b.size - 1]! == 10 then b.extract 0 (b.size - 1) else b.push 10
    match read Lean.githash Lean.versionString other with
    | .ok ds' => if sameDecls ds ds' then 0 else panic! "export: the final LF changed the decls"
    | .error _ => panic! "export: the final LF changed acceptance"

end FvdepFuzz
