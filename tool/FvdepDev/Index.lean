import FvdepCore.Index.Doc

/-! `fvdep-dev index decode <file>` (contract U4 C9; never shipped): `decodeIndex` over a file —
stdout the canonical encoding of the decoded index, exit 0; else stdout `refused: <reason>`, exit 1;
usage or an unreadable file, exit 2. Every message line takes the line rule (`escapeControls`). -/

namespace FvdepDev.Index

open FvdepCore.Doc FvdepCore.Index

def usage : String := "usage: fvdep-dev index decode <file>\n"

def decodeFile (file : String) : IO UInt32 := do
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .error e =>
    IO.eprintln (escapeControls s!"fvdep-dev index: cannot read {file}: {e}")
    return 2
  | .ok bytes =>
    match decodeIndex bytes with
    | .error e =>
      IO.println (escapeControls s!"refused: {e.render}")
      return 1
    | .ok i =>
      match encodeIndex i with
      | .ok out =>
        (← IO.getStdout).write out
        return 0
      | .error e =>
        IO.eprintln
            (escapeControls s!"fvdep-dev index: an accepted index does not re-encode: {e.render}")
        return 2

def run : List String → IO UInt32
  | ["decode", file] => decodeFile file
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Index
