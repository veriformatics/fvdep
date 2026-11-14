import FvdepDev.Sys

/-- `fvdep-dev sys run OP…` (contract U3 F6): the persistence API's dev driver; never shipped. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "sys" :: "run" :: ops => FvdepDev.Sys.run ops
  | _ => do
    IO.eprint FvdepDev.Sys.usage
    return 2
