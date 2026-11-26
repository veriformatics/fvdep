import FvdepCore.Export
import FvdepCore.Judge.Compare
import FvdepIO.Toolchain
import LeanExport.Parse

/-! `fvdep-dev export read <file> [<constant>]` (contract U5b X; never shipped): one `leanexport`
output through `FvdepCore.Export.read` against fvdep's own Lean (version + githash) → the
declaration count, + the named declaration's kind, value presence + type; a refusal → its line,
class + reason, exit 1.

`fvdep-dev export compare <file>…` (contract U7 X9): each export fvdep's reader accepts vs Lean's
own reader (`LeanExport.parseStream`, the one Lake's comparator + leanchecker read with) — the same
constants in the same order, every field equal (expressions by `Expr.equal`: binder names + info
included) — one line per file: `same <path> <constants>`, `outside <path> line <n>` (fvdep refuses
it: nothing to compare) or `differ <path> <why>`; exit 1 when any file differs. -/

namespace FvdepDev.Export

open FvdepCore.Export FvdepCore.Judge

def usage : String :=
  "usage: fvdep-dev export read <file> [<constant>]\n" ++
    "       fvdep-dev export compare <file>…\n"

def nm (t : Tables) (i : Nat) : Option Lean.Name := t.names[i]?

def nms (t : Tables) (is : List Nat) : Option (List Lean.Name) := is.mapM (nm t)

def ex (t : Tables) (i : Nat) : Option Lean.Expr := t.exprs[i]?

def hintsOf : Hints → Lean.ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular k => .regular k

def safetyOf : Safety → Lean.DefinitionSafety
  | .safe => .safe
  | .unsafe => .unsafe
  | .partial => .partial

def quotTag : Lean.QuotKind → Nat
  | .type => 0
  | .ctor => 1
  | .lift => 2
  | .ind => 3

def quotOf : QuotKind → Lean.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- Lean's `ConstantInfo` of one of fvdep's constants, every field denoted under the tables. -/
def constantOf (t : Tables) : Entry → Option Lean.ConstantInfo
  | .axiom u lps n ty => do
    return .axiomInfo
        { name := ← nm t n, levelParams := ← nms t lps, type := ← ex t ty, isUnsafe := u }
  | .defn all h lps n s ty v => do
    return .defnInfo
        { name := ← nm t n
          levelParams := ← nms t lps
          type := ← ex t ty
          value := ← ex t v
          hints := hintsOf h
          safety := safetyOf s
          all := ← nms t all }
  | .thm all lps n ty v => do
    return .thmInfo
        { name := ← nm t n
          levelParams := ← nms t lps
          type := ← ex t ty
          value := ← ex t v
          all := ← nms t all }
  | .opaque all u lps n ty v => do
    return .opaqueInfo
        { name := ← nm t n
          levelParams := ← nms t lps
          type := ← ex t ty
          value := ← ex t v
          isUnsafe := u
          all := ← nms t all }
  | .quot q lps n ty => do
    return .quotInfo
        { name := ← nm t n, levelParams := ← nms t lps, type := ← ex t ty, kind := quotOf q }
  | .induct x => do
    return .inductInfo
        { name := ← nm t x.name
          levelParams := ← nms t x.levelParams
          type := ← ex t x.type
          numParams := x.numParams
          numIndices := x.numIndices
          all := ← nms t x.all
          ctors := ← nms t x.ctors
          numNested := x.numNested
          isRec := x.isRec
          isUnsafe := x.isUnsafe
          isReflexive := x.isReflexive }
  | .ctor c => do
    return .ctorInfo
        { name := ← nm t c.name
          levelParams := ← nms t c.levelParams
          type := ← ex t c.type
          induct := ← nm t c.induct
          cidx := c.cidx
          numParams := c.numParams
          numFields := c.numFields
          isUnsafe := c.isUnsafe }
  | .recursor r => do
    let rules ←
      r.rules.mapM fun x => do
          return ({ ctor := ← nm t x.ctor, nfields := x.nfields, rhs := ← ex t x.rhs } :
              Lean.RecursorRule)
    return .recInfo
        { name := ← nm t r.name
          levelParams := ← nms t r.levelParams
          type := ← ex t r.type
          all := ← nms t r.all
          numParams := r.numParams
          numIndices := r.numIndices
          numMotives := r.numMotives
          numMinors := r.numMinors
          rules
          k := r.k
          isUnsafe := r.isUnsafe }

/-- The first field two constant records disagree on (`none` = every field equal). -/
def differ (a b : Lean.ConstantInfo) : Option String :=
  let base :=
    if a.name != b.name then some "name"
    else
      if a.levelParams != b.levelParams then some "levelParams"
      else if !a.type.equal b.type then some "type" else none
  base.orElse fun _ =>
    match a, b with
    | .axiomInfo x, .axiomInfo y => if x.isUnsafe != y.isUnsafe then some "isUnsafe" else none
    | .defnInfo x, .defnInfo y =>
      if !x.value.equal y.value then some "value"
      else
        if x.hints != y.hints then some "hints"
        else
          if x.safety != y.safety then some "safety"
          else if x.all != y.all then some "all" else none
    | .thmInfo x, .thmInfo y =>
      if !x.value.equal y.value then some "value" else if x.all != y.all then some "all" else none
    | .opaqueInfo x, .opaqueInfo y =>
      if !x.value.equal y.value then some "value"
      else
        if x.isUnsafe != y.isUnsafe then some "isUnsafe"
        else if x.all != y.all then some "all" else none
    | .quotInfo x, .quotInfo y => if quotTag x.kind != quotTag y.kind then some "kind" else none
    | .inductInfo x, .inductInfo y =>
      if x.numParams != y.numParams then some "numParams"
      else
        if x.numIndices != y.numIndices then some "numIndices"
        else
          if x.all != y.all then some "all"
          else
            if x.ctors != y.ctors then some "ctors"
            else
              if x.numNested != y.numNested then some "numNested"
              else
                if x.isRec != y.isRec then some "isRec"
                else
                  if x.isUnsafe != y.isUnsafe then some "isUnsafe"
                  else if x.isReflexive != y.isReflexive then some "isReflexive" else none
    | .ctorInfo x, .ctorInfo y =>
      if x.induct != y.induct then some "induct"
      else
        if x.cidx != y.cidx then some "cidx"
        else
          if x.numParams != y.numParams then some "numParams"
          else
            if x.numFields != y.numFields then some "numFields"
            else if x.isUnsafe != y.isUnsafe then some "isUnsafe" else none
    | .recInfo x, .recInfo y =>
      if x.all != y.all then some "all"
      else
        if x.numParams != y.numParams then some "numParams"
        else
          if x.numIndices != y.numIndices then some "numIndices"
          else
            if x.numMotives != y.numMotives then some "numMotives"
            else
              if x.numMinors != y.numMinors then some "numMinors"
              else
                if x.k != y.k then some "k"
                else
                  if x.isUnsafe != y.isUnsafe then some "isUnsafe"
                  else
                    if x.rules.length != y.rules.length then some "rules"
                    else
                      if
                          (x.rules.zip y.rules).all fun (p, q) =>
                            p.ctor == q.ctor && p.nfields == q.nfields && p.rhs.equal q.rhs then
                        none
                      else some "rules"
    | _, _ => some "kind"

/-- X9 on one file: the line it prints + whether the two readers agree. -/
def compareFile (file : String) : IO (String × Bool) := do
  let b ← IO.FS.readBinFile file
  match readTables Lean.githash Lean.versionString b with
  | .error r =>
    return (s!"outside {file} line {r.line}", true)
  | .ok t =>
    let h ← IO.FS.Handle.mk file .read
    let lean : Except String LeanExport.ExportedEnv ←
      tryCatch (Except.ok <$> LeanExport.parseStream (.ofHandle h)) fun e =>
          pure (Except.error (toString e))
    match lean with
    | .error e =>
      return (s!"differ {file} Lean's reader refuses: {e}", false)
    | .ok env =>
      let mine := t.rawDecls.toList.flatMap entries
      if mine.length != env.constOrder.size then
        return (s!"differ {file} {mine.length} constants vs Lean's {env.constOrder.size}", false)
      for (e, n) in mine.zip env.constOrder.toList do
        match constantOf t e, env.constMap[n]? with
        | some c, some d =>
          if c.name != n then
            return (s!"differ {file} order at {n}", false)
          if let some why := differ c d then
            return (s!"differ {file} {n} {why}", false)
        | none, _ =>
          return (s!"differ {file} {n} unbound in fvdep's tables", false)
        | _, none =>
          return (s!"differ {file} {n} absent in Lean's map", false)
      return (s!"same {file} {mine.length}", true)

def run : List String → IO UInt32
  | "read" :: file :: rest => do
    let b ← IO.FS.readBinFile file
    match FvdepCore.Export.read Lean.githash Lean.versionString b with
    | .error r =>
      IO.println s!"refused line {r.line} {repr r.cls}: {r.reason}"
      return 1
    | .ok ds =>
      IO.println s!"decls {ds.length}"
      if let [c] := rest then
        match ds.find? (·.name == c.toName) with
        | some d =>
          IO.println s!"{d.name} {repr d.kind} value={d.value.isSome} type {d.type}"
        | none =>
          IO.println s!"{c} absent"
      return 0
  | "compare" :: files@(_ :: _) => do
    let mut ok := true
    for f in files do
      let (line, same) ← compareFile f
      IO.println line
      ok := ok && same
    return if ok then 0 else 1
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Export
