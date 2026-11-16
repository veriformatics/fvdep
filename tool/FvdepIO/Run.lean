import FvdepIO.Index

/-! The interpreter (contract `docs/contracts/U2-core.md` X6; ledger residue `interpreter`): each
effect → its IO primitive. Tested, never proved: the U1 K2 smoke cases cover the output mapping;
`fvdep index`'s observation effects + `index.json`'s read/replace = `FvdepIO.Index` (residue
`lean-env`; F2 for the file). -/

namespace FvdepIO

open FvdepCore

/-- One effect against the real streams, the working directory's `index.json` + the library
observations. `fvdep.lock` + `fvdep.toml` arrive with U8: their effects answer an error + write
nothing (no command emits them yet). -/
def perform (st : IO.Ref Index.State) : Eff → IO Response
  | .out s => do
    let h ← IO.getStdout
    h.putStr s
    h.flush
    pure .done
  | .err s => do
    let h ← IO.getStderr
    h.putStr s
    h.flush
    pure .done
  | .read .index => Index.readIndex
  | .read _ => pure (.read (.error "file reads of the project files arrive with U8"))
  | .replace .index b => Index.replaceIndex b
  | .replace _ _ => pure (.replace (.error "file writes of the project files arrive with U8"))
  | .probe => Index.probe
  | .libraryFacts => Index.libraryFacts st
  | .replay => Index.replay st

def runPlan {α : Type} (st : IO.Ref Index.State) : Plan α → IO α
  | .pure a => pure a
  | .step e k => do
    let r ← perform st e
    runPlan st (k r)

/-- `main`'s interpreter. A failed write of fvdep's own output = I/O failure (`docs/interface.md`
§2): exit 2, the reason on stderr while stderr accepts it; uncaught, the runtime would exit 1 (= a
negative verdict). A broken pipe (the reader stopped reading, `fvdep … | head -1`) stays quiet, as
standard tools do. The index run directory goes in every case (C1). -/
def execute (p : Plan UInt32) : IO UInt32 := do
  let st ← IO.mkRef ({} : Index.State)
  tryFinally (outputFailure (runPlan st p)) (Index.cleanup st)
where outputFailure (run : IO UInt32) : IO UInt32 := do
    try
      run
    catch e =>
      match e with
      | .resourceVanished .. =>
        pure ()
      | _ =>
        try
          let err ← IO.getStderr
          err.putStr s!"Could not write the output: {e}.\n"
          err.flush
        catch _ =>
          pure ()
      return 2

end FvdepIO
