import FvdepIO.Step

/-- `fvdep-step` (contract `docs/contracts/U5-sandbox.md` R8) = `FvdepIO.Step.main`. -/
def main : List String → IO UInt32 := FvdepIO.Step.main
