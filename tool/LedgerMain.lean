import FvdepLedger.Check

/-! `fvdep-ledger` (contract U2 L8): `unsafe` for `enableInitializersExecution` (notation-aware
printing loads the environment's extensions); a gate tool, outside every shipped closure. -/

unsafe def main (args : List String) : IO UInt32 := FvdepLedger.Check.main args
