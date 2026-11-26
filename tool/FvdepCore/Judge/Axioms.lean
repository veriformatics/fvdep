import FvdepCore.Index.Statuses

/-! U7 A (contract `docs/contracts/U7-judge.md` A1–A2): the axioms G6 recorded → `Obs.axioms`'
strings — an allowlisted axiom (U4's `std`: the standard three, structured names) by its plain
name, every other by a quoted, escaped, bounded rendering that no allowlisted string equals (NanoDa
#37 flattens names: membership is decided on the structured name, never on text). Pure. -/

namespace FvdepCore.Judge

/-- One component's text: `\`, `«`, `»` + `.` escaped with `\`. -/
def escapeComponent (s : String) : String :=
  String.ofList
    (s.toList.flatMap fun c =>
      if c == '\\' || c == '«' || c == '»' || c == '.' then ['\\', c] else [c])

/-- A name's components, outermost first. -/
def componentTexts : Lean.Name → List String
  | .anonymous => []
  | .str p s => componentTexts p ++ [escapeComponent s]
  | .num p k => componentTexts p ++ [toString k]

/-- A2: an axiom's text — its plain name when allowlisted, else `«…»` over its escaped components
(at most 255 characters inside: at most 1,024 UTF-8 bytes in all). -/
def axiomText (n : Lean.Name) : String :=
  if n == ``propext then "propext"
  else
    if n == ``Classical.choice then "Classical.choice"
    else
      if n == ``Quot.sound then "Quot.sound"
      else "«" ++ String.ofList ((".".intercalate (componentTexts n)).toList.take 255) ++ "»"

end FvdepCore.Judge
