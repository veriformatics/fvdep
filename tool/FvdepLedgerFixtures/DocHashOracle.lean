import FvdepLedgerFixtures.Clean
import Lean

/-! Independent L7 oracle: the committed fixture statement, not checker code. -/

open Lean Elab Term in
run_elab
  do
    let info ← getConstInfo ``FvdepLedgerFixtures.Clean.statement
    match info with
    | .defnInfo value =>
      logInfo m!"ORACLE_HASH_DECIMAL={value.value.hash.toNat}"
    | _ =>
      throwError "The fixture statement must be a definition."
