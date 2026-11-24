import FvdepIO.Parse

/-- `fvdep-parse` (contract `docs/contracts/U6-profile.md` P1) = `FvdepIO.Parse.main`. -/
def main : List String → IO UInt32 := FvdepIO.Parse.main
