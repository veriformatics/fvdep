import FvdepCore.Oracle.Wire

/-! The evaluation step's source (contract `docs/contracts/U5b-oracle.md` W0, W5, V3; residue
`oracle-driver`): the entry module + version imports, then `Protocol/Types.lean` + `Wire.lean`
after their import lines — their text as fvdep was built (`include_str`; this module imports Wire,
so an edit of either file rebuilds it; `lake test` checks the embedded text = the files' bytes:
Q4) — then a `main` answering `requests.txt` line by line into `/fvdep/work/out/replies.txt`. -/

namespace FvdepCore.Oracle.Driver

/-- `FvdepCore/Protocol/Types.lean` as fvdep was built with it. -/
def typesText : String := include_str ".." / "Protocol" / "Types.lean"

/-- `FvdepCore/Oracle/Wire.lean` as fvdep was built with it. -/
def wireText : String := include_str "Wire.lean"

/-- `t` after its leading `import` lines (W0: the driver states its own imports). -/
def afterImports (t : String) : String :=
  "\n".intercalate ((t.splitOn "\n").dropWhile fun l => l.startsWith "import ")

/-- A name's string components, in order. -/
def parts : Lean.Name → List String
  | .str p s => parts p ++ [s]
  | .num p _ => parts p
  | .anonymous => []

/-- A name as Lean source: each component `«»`-quoted (plain components hold no `»`), so a keyword
component stays an identifier. -/
def quoted (n : Lean.Name) : String := ".".intercalate ((parts n).map fun c => "«" ++ c ++ "»")

/-- W5: `main` = each line of `requests.txt` (cwd `/fvdep/src`) answered by `answer (@spec)`, one
result line each, into `/fvdep/work/out/replies.txt`. -/
def mainText (spec : Lean.Name) : String :=
  "def main : IO Unit := do\n" ++ "  let input ← IO.FS.readFile \"requests.txt\"\n" ++
    "  let out ← IO.FS.Handle.mk \"/fvdep/work/out/replies.txt\" .write\n" ++
    "  for line in (input.splitOn \"\\n\").dropLast do\n" ++
    "    out.putStr (FvdepCore.Oracle.Wire.answer (@" ++
    quoted spec ++
    ") line ++ \"\\n\")\n" ++
    "  out.flush\n"

/-- V3: the driver for entry module `M` + spec constant `spec`. -/
def driverText (M spec : Lean.Name) : String :=
  "import " ++ quoted M ++ "\nimport Fvdep.Semver.Version.V1_0_0\n" ++ afterImports typesText ++
    "\n" ++
    afterImports wireText ++
    "\n" ++
    mainText spec

end FvdepCore.Oracle.Driver
