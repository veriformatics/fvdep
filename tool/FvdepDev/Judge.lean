import FvdepCore.Judge.Profile

/-! `fvdep-dev judge profile` (contract U7 V2; never shipped): prints the verification profile v1's
persisted form — `docs/verification-profile.json`'s bytes (`lake test` compares them). -/

namespace FvdepDev.Judge

def usage : String := "usage: fvdep-dev judge profile\n"

def run : List String → IO UInt32
  | ["profile"] => do
    (← IO.getStdout).write FvdepCore.Judge.v1.text
    return 0
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Judge
