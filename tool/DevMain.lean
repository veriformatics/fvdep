import FvdepDev.Cache
import FvdepDev.Export
import FvdepDev.Index
import FvdepDev.Library
import FvdepDev.Oracle
import FvdepDev.Phase
import FvdepDev.Resources
import FvdepDev.Sandbox
import FvdepDev.Sys

/-- `fvdep-dev sys run OP…` (contract U3 F6): the persistence API's dev driver; `fvdep-dev json
measure FAMILY N TASKS` (J5 resources: `tools/json-resources.sh`); `fvdep-dev oracle <id>@<ver>`
(contract U4 B5: the launch specs over adapter protocol v1); `fvdep-dev index decode <file>`
(contract U4 C9); `fvdep-dev sandbox run …` (contract U5 D2); `fvdep-dev cache …` (contract U5
D3); `fvdep-dev phase check …` (contract U5 D1); `fvdep-dev export read …` (contract U5b X);
`fvdep-dev library tree|plan …` (contract U5b L4); never shipped. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "sys" :: "run" :: ops => FvdepDev.Sys.run ops
  | "json" :: "measure" :: rest => FvdepDev.Resources.run rest
  | "oracle" :: rest => FvdepDev.Oracle.run rest
  | "index" :: rest => FvdepDev.Index.run rest
  | "sandbox" :: "run" :: rest => FvdepDev.Sandbox.run rest
  | "cache" :: rest => FvdepDev.Cache.run rest
  | "phase" :: rest => FvdepDev.Phase.run rest
  | "export" :: rest => FvdepDev.Export.run rest
  | "library" :: rest => FvdepDev.Library.run rest
  | _ => do
    IO.eprint
        (FvdepDev.Sys.usage ++ FvdepDev.Resources.usage ++ FvdepDev.Oracle.usage ++
          FvdepDev.Index.usage ++
          FvdepDev.Sandbox.usage ++
          FvdepDev.Cache.usage ++
          FvdepDev.Phase.usage ++
          FvdepDev.Export.usage ++
          FvdepDev.Library.usage)
    return 2
