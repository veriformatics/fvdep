import FvdepIO.Index
import FvdepIO.Oracle

/-! The interpreter (contract `docs/contracts/U2-core.md` X6; ledger residue `interpreter`): each
effect → its IO primitive. Tested, never proved: the U1 K2 smoke cases cover the output mapping;
`fvdep index`'s observation effects + `index.json`'s read/replace = `FvdepIO.Index` (residue
`lean-env`; F2 for the file). -/

namespace FvdepIO

open FvdepCore

/-- One effect against the real streams, the working directory's `index.json`, the library
observations + the oracle's (`FvdepIO.Oracle`). `fvdep.lock` + `fvdep.toml` reads + writes arrive
with U8: their effects answer an error + write nothing (no command emits them yet). -/
def perform (st : IO.Ref Index.State) (os : IO.Ref Oracle.State) : Eff → IO Response
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
  | .project explicit => Oracle.project explicit
  | .manifest dir => Oracle.manifest dir
  | .parse text => Oracle.parse text
  | .snapshot pin lim => Oracle.snapshot pin lim
  | .closure tree roots => Oracle.closure os tree roots
  | .view tree roots => Oracle.view os tree roots
  | .leanexport view imports roots => Oracle.leanexport os view imports roots
  | .stdin cap => Oracle.stdin cap
  | .evaluate view driver requests seconds => Oracle.evaluate os view driver requests seconds
  | .outBytes b => do
    let h ← IO.getStdout
    h.write b
    h.flush
    pure .done

def runPlan {α : Type} (st : IO.Ref Index.State) (os : IO.Ref Oracle.State) : Plan α → IO α
  | .pure a => pure a
  | .step e k => do
    let r ← perform st os e
    runPlan st os (k r)

/-- The interpreter; `replies` = the dev seam's substitute evaluation replies (`none` = the step
runs, U5b Q3). A failed write of fvdep's own output = I/O failure (`docs/interface.md` §2): exit 2,
the reason on stderr while stderr accepts it; uncaught, the runtime would exit 1 (= a negative
verdict). A broken pipe (the reader stopped reading, `fvdep … | head -1`) stays quiet, as standard
tools do. The run directories go in every case (U4 C1, U5b O). -/
def executeWith (replies : Option ByteArray) (p : Plan UInt32) : IO UInt32 := do
  let st ← IO.mkRef ({} : Index.State)
  let os ← IO.mkRef ({ replies } : Oracle.State)
  tryFinally (outputFailure (runPlan st os p))
      (do
        Index.cleanup st;
        Oracle.cleanup os)
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

/-- `main`'s interpreter. -/
def execute (p : Plan UInt32) : IO UInt32 := executeWith none p

end FvdepIO
