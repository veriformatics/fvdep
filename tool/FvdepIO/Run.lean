import FvdepCore.Cli

namespace FvdepIO

/-- Writes `FvdepCore.Cli.run args` verbatim (stdout, then stderr) + returns its exit code. A failed
write = I/O failure (`docs/interface.md` §2): exit 2, the reason on stderr while stderr accepts it;
uncaught, the runtime would exit 1 (= a negative verdict). A broken pipe (the reader stopped
reading, `fvdep … | head -1`) stays quiet, as standard tools do. -/
def run (args : List String) : IO UInt32 := do
  let o := FvdepCore.Cli.run args
  try
    if !o.stdout.isEmpty then
      let out ← IO.getStdout
      out.putStr o.stdout
      out.flush
    if !o.stderr.isEmpty then
      let err ← IO.getStderr
      err.putStr o.stderr
      err.flush
    return o.exit
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
