import FvdepAudit.Profile.Walk.Spec

/-! U6 C1 + I1 + I2 + I3 (a) + K0''s spec of a module's two stages, written apart from
`FvdepCore.Profile.step` + `header`: the body = its items in source order, each command's findings
(`Walk.Spec.findings`) under the namespace of the scope stack the earlier clean commands built, a
parse or cap stop = the event at its item; the header = its findings in C1's order (the module's
name, the header's layout, `module`, `prelude`, then each import: its layout, its modifier, its
name, I3 (a) on the name). Shared with the implementation + read as spec text: the layout readers
`headerParts`, `optSlot`, `importParts` + `identAt` (K0''s layouts). -/

namespace FvdepAudit.Profile.Stage.Spec

open FvdepCore.Profile FvdepAudit.Profile.Walk.Spec

/-- C1's scope transition after a clean top-level command: `namespace A.B` pushes one namespace
scope per component (its name = its identifier, child 1), `section` one unnamed scope (`section
A.B` one per component), `end` pops one (`end A.B` one per component), never below empty; a
section's or end's name = the first child of its optional node (child 2, child 1). -/
def nextScopes (sc : List (List String)) : Tree → List (List String)
  | .node k kids =>
    if k == kindNamespace then
      match identAt kids 1 with
      | some n => sc ++ n.map fun c => [c]
      | none => sc
    else
      if k == kindSection then
        match (kids[2]? : Option Tree) with
        | some (.node _ (.ident n _ :: _)) => sc ++ n.map fun _ => []
        | _ => sc ++ [[]]
      else
        if k == kindEnd then
          match (kids[1]? : Option Tree) with
          | some (.node _ (.ident n _ :: _)) => sc.take (sc.length - n.length)
          | _ => sc.take (sc.length - 1)
        else sc
  | _ => sc

/-- C1's body stage: the first event over the items in source order — a command's first finding
under the namespace of the scope stack so far (its namespace scopes' components in stack order),
else the stack moves by the command; a parse or cap stop = the event at its item. -/
def bodyEvent (s : Subject) : List (List String) → List Item → Option Event
  | _, [] => none
  | sc, .tree t start :: rest =>
    match (findings s sc.flatten start t).head? with
    | some f => some (.finding f)
    | none => bodyEvent s (nextScopes sc t) rest
  | _, .stop e :: _ => some e

/-- I2: the module's own name — no component beginning with `_`; consumer: a first component none
of `Init`, `Std`, `Lean`, `Lake` + not starting with `Fvdep`; library: a first component `Fvdep` or
`FvdepPreview`. -/
def nameAdmitted (role : Role) (m : String) : Bool :=
  !((m.splitOn ".").any fun c => c.startsWith "_") &&
    match (m.splitOn ".").head?, role with
    | some c, .consumer => !["Init", "Std", "Lean", "Lake"].contains c && !c.startsWith "Fvdep"
    | some c, .library => c == "Fvdep" || c == "FvdepPreview"
    | none, _ => false

/-- I1: an import `m` of module `self` (`lib` = the pinned library's modules, `batch` = the
batch's) — `Init` alone, `Std` + every `Std.*`; consumer: a library module whose first component is
exactly `Fvdep`, or a batch module; library: a batch module whose first component is `Fvdep`, or —
`self`'s first component `FvdepPreview` — one whose first component is `FvdepPreview`. -/
def importAdmitted (role : Role) (lib batch : List String) (self m : String) : Bool :=
  let first := fun (x : String) => (x.splitOn ".").headD ""
  match role with
  | .consumer =>
    m == "Init" || first m == "Std" || (lib.contains m && first m == "Fvdep") || batch.contains m
  | .library =>
    m == "Init" || first m == "Std" ||
      (batch.contains m &&
        (first m == "Fvdep" || (first self == "FvdepPreview" && first m == "FvdepPreview")))

/-- K0' + C1: an optional header slot (`module`, `prelude`): another layout → `shape` (at 1:0), its
keyword present → `header <rule>` at the keyword's first positioned leaf. -/
def slotRules (rule : String) (t : Tree) : List Finding :=
  match optSlot t with
  | none => [mk ⟨1, 0⟩ "shape" ["Lean.Parser.Module.header"]]
  | some (some u) => [mk ((leafPos u).getD ⟨1, 0⟩) "header" [rule]]
  | some none => []

/-- K0' + I1 + I3 (a) + C1: one import's findings in order — its layout (`shape`), its modifier
(`header modifier`), its name (`header import`), then I3 (a) on the name (`reserved`, at the
identifier, else at the import); the rest at the import's first positioned leaf. -/
def importRules (role : Role) (lib batch : List String) (self : String) (t : Tree) : List Finding :=
  let here := (leafPos t).getD ⟨1, 0⟩
  match importParts t with
  | none => [mk here "shape" ["Lean.Parser.Module.import"]]
  | some (md, n, q) =>
    (match md with
      | some a => [mk here "header" ["modifier", a]]
      | none => []) ++
      (if importAdmitted role lib batch self (dotted n) then []
      else [mk here "header" ["import", dotted n]]) ++
      match firstReserved false n with
      | some c => [mk (q.getD here) "reserved" [c]]
      | none => []

/-- C1 + I1 + I2 + K0': a module's header findings in order — its own name (`header name`, at 1:0),
the header's layout (`shape`), `module`, `prelude`, then each import in source order. -/
def headerRules (role : Role) (lib batch : List String) (self : String) (h : Tree) : List Finding :=
  (if nameAdmitted role self then [] else [mk ⟨1, 0⟩ "header" ["name", self]]) ++
    match headerParts h with
    | some (m, p, imps) =>
      slotRules "module" m ++ slotRules "prelude" p ++
        imps.flatMap (importRules role lib batch self)
    | none => [mk ⟨1, 0⟩ "shape" ["Lean.Parser.Module.header"]]

end FvdepAudit.Profile.Stage.Spec
