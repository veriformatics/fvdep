import FvdepDev.Resources
import FvdepDev.Sys

/-- `fvdep-dev sys run OP…` (contract U3 F6): the persistence API's dev driver; `fvdep-dev json
measure FAMILY N TASKS` (J5 resources: `tools/json-resources.sh`); never shipped. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "sys" :: "run" :: ops => FvdepDev.Sys.run ops
  | "json" :: "measure" :: rest => FvdepDev.Resources.run rest
  | _ => do
    IO.eprint (FvdepDev.Sys.usage ++ FvdepDev.Resources.usage)
    return 2
