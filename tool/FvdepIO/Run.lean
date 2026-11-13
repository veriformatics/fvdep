import FvdepCore.Plan

/-! The interpreter (contract `docs/contracts/U2-core.md` X6; ledger residue `interpreter`): each
effect → its IO primitive. Tested, never proved: the U1 K2 smoke cases cover the output mapping. -/

namespace FvdepIO

open FvdepCore

/-- One effect against the real streams. File effects arrive with U3 (durable replace + fsync FFI);
until then they answer an error + write nothing (no U2 command emits them). -/
def perform : Eff → IO Response
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
  | .read _ => pure (.read (.error "file reads arrive with U3"))
  | .replace _ _ => pure (.replace (.error "file writes arrive with U3"))

def runPlan {α : Type} : Plan α → IO α
  | .pure a => pure a
  | .step e k => do
    let r ← perform e
    runPlan (k r)

/-- `main`'s interpreter. A failed write of fvdep's own output = I/O failure (`docs/interface.md`
§2): exit 2, the reason on stderr while stderr accepts it; uncaught, the runtime would exit 1 (= a
negative verdict). A broken pipe (the reader stopped reading, `fvdep … | head -1`) stays quiet, as
standard tools do. -/
def execute (p : Plan UInt32) : IO UInt32 := do
  try
    runPlan p
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
