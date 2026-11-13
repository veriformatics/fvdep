import Lean

/-! Invalid proof hidden in an owned import; axiom inspection alone cannot detect it. -/

open Lean Elab Term Meta in
set_option debug.skipKernelTC true in
run_elab
  do
    addDecl
        (.thmDecl
          { name := `FvdepLedgerFixtures.ForgedImport.falseProof
            levelParams := []
            type := mkConst ``False
            value := mkConst ``True.intro })
