import FvdepIO.Toml

/-! Fuzz target `manifest-decode` (contract U3 "Fuzz"): a manifest read from any bytes prints to
bytes that read back to it (T's printer round trip through Lake's parser); coverage-guided over
`textStage`, `ofLake` + `validate` (Lake.Toml is prebuilt: residue `toml-parse`). A violation
throws, which the harness turns into an abort. -/

namespace FvdepFuzz

open FvdepIO.Toml FvdepCore.Manifest

@[export fvdep_fuzz_manifest]
def manifestTarget (b : ByteArray) : IO UInt8 := do
  match ← readManifest b with
  | .error _ =>
    return 0
  | .ok m =>
    match ← readManifest (printManifest m) with
    | .ok m' =>
      if m' == m then
        return 0
      else
        throw (IO.userError "manifest-decode: read (print m) ≠ m")
    | .error _ =>
      throw (IO.userError "manifest-decode: print m does not read back")

end FvdepFuzz
