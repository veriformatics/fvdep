namespace Fvdep

/-- Equals `version` in `lakefile.lean` + `tool/lakefile.lean` (gate stage `meta`) and the
`fvdep --version` output (gate stage `cli`). -/
def version : String := "0.1.0"

end Fvdep
