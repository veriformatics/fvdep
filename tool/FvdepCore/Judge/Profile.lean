import FvdepCore.Judge.Graph
import FvdepCore.Judge.Kernel

/-! U7 V (contract `docs/contracts/U7-judge.md` V1–V3): the verification profile v1 — compiled-in
data the judge runs under (kernels + their pins, the allowlist, the step limits, W, G5's reviewed
opaque names) + its persisted form (V2). Pure. v1's deadlines, W, opaque list + canary digest stay
provisional until Q qualifies them (V3: the freeze records then); the pins = vflab's elan v4.35.0
install until U7-D2 checks them against the release's own bytes. -/

namespace FvdepCore.Judge

open FvdepCore.Evidence FvdepCore.Json FvdepCore.Sandbox

/-- V1: one kernel's pin + invocation (its argv = K1's for `threads`). -/
structure VKernel where
  sha256 : String
  deadline : Nat
  threads : Nat
  deriving DecidableEq, Repr

/-- V1: the verification profile; its kernels = U2's `kernels`, one entry each by construction. -/
structure VProfile where
  id : String
  toolchain : String
  githash : String
  fingerprint : String
  exportFormat : String
  allowlist : List String
  implementationFreeze : String
  lean : VKernel
  conLeche : VKernel
  nanoda : VKernel
  step : Limits
  opaques : List Lean.Name
  work : Nat
  canaries : String
  deriving DecidableEq, Repr

def VProfile.kernel (p : VProfile) : Kernel → VKernel
  | .lean => p.lean
  | .conLeche => p.conLeche
  | .nanoda => p.nanoda

/-- K1: a kernel step's limits = the profile's step limits under that kernel's own deadline. -/
def VProfile.limits (p : VProfile) (k : Kernel) : Limits :=
  { p.step with deadline := (p.kernel k).deadline }

/-- V1 (provisional until Q: deadlines, W, opaques, canaries; fingerprint measured at U7-D2). -/
def v1 : VProfile :=
  { id := "fvdep/verification/1"
    toolchain := "v4.35.0"
    githash := "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
    fingerprint := ""
    exportFormat := "3.1.0"
    allowlist := ["propext", "Classical.choice", "Quot.sound"]
    implementationFreeze := "c6d7118cf6d7abef"
    lean := ⟨"12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6", 600, 1⟩
    conLeche := ⟨"23a32522ea2c79f4ec8b48916272b37a423bda171e57cd83cfcf142eec50e621", 600, 2⟩
    nanoda := ⟨"cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5", 600, 2⟩
    step := {}
    opaques := [`String.Internal.append]
    work := 100000000
    canaries := "" }

/-- U2's view of the profile: its id + allowlist (E1's `Profile`). -/
def VProfile.evidence (p : VProfile) : Profile := ⟨p.id, p.allowlist⟩

/-- V2: the persisted form (schema 1, canonical J: members in byte order); each kernel's path +
argv, NanoDa's config + G1's roots print from the definitions the steps run. -/
def VProfile.toJson (p : VProfile) : Value :=
  let strs (xs : List String) : Value := .arr (xs.map .str)
  let kernelJson (k : Kernel) : Value :=
    .obj
      [("argv", strs (kernelArgv (p.kernel k).threads k)), ("deadline", .int (p.kernel k).deadline),
        ("name", .str (kernelName k)), ("path", .str ("bin/" ++ kernelBin k)),
        ("sha256", .str (p.kernel k).sha256), ("threads", .int (p.kernel k).threads)]
  .obj
    [("allowlist", strs p.allowlist), ("canaries", .str p.canaries),
      ("exportFormat", .str p.exportFormat), ("fingerprint", .str p.fingerprint), ("id", .str p.id),
      ("implementationProfile",
        .obj [("freeze", .str p.implementationFreeze), ("id", .str FvdepCore.Profile.profileId)]),
      ("kernels", .arr (kernels.map kernelJson)),
      ("nanoda", nanodaValue p.allowlist p.nanoda.threads),
      ("opaques", strs (p.opaques.map toString)), ("roots", strs (mandatory.map toString)),
      ("schema", .int 1),
      ("step",
        .obj
          [("diagnosticBytes", .int p.step.diagnosticBytes), ("fileBytes", .int p.step.fileCap),
            ("frameBytes", .int p.step.frameBytes), ("tmpBytes", .int p.step.tmpBytes),
            ("workBytes", .int p.step.workBytes)]),
      ("toolchain", .obj [("githash", .str p.githash), ("release", .str p.toolchain)]),
      ("work", .int p.work)]

/-- V2: `docs/verification-profile.json`'s bytes = the persisted form + LF. -/
def VProfile.text (p : VProfile) : ByteArray := (print p.toJson).push 0x0A

end FvdepCore.Judge
