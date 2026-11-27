import FvdepCore.Judge.Kernel

/-! Spec for K2's status table (contract `docs/contracts/U7-judge.md` K2), written from the contract
apart from `FvdepCore.Judge.kernelStatus`'s code: which step observations are infrastructure,
which exit code + stream contents each kernel's accept, reject + decline need (the kernels' texts =
the code's named constants, reviewed data against K2). -/

namespace FvdepAudit.Judge.Kernel.Spec

open FvdepCore.Evidence FvdepCore.Phase FvdepCore.Sandbox FvdepCore.Judge

/-- A string's UTF-8 bytes. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

/-- K2: the step ran clean + its child exited `c` — bwrap's exit = the frame's, no data file, no
full tmpfs. -/
def Exited (r : KernelRun) (c : Nat) : Prop :=
  r.outcome = .exited c ∧ r.frame = .ok (.exited c) 0 false

/-- K2's infrastructure: a setup or protocol failure, or an exit whose frame is unreadable, over its
cap, or reports a status the helper's exit contradicts, a data file, a full tmpfs or a child that
never started. -/
def IsInfra (r : KernelRun) : Prop :=
  (∃ d, r.outcome = .setupFailed d) ∨
    r.outcome = .protocol ∨
    ∃ n,
      r.outcome = .exited n ∧
        (r.frame = .invalid ∨
          r.frame = .overflow ∨
          ∃ ch f full,
            r.frame = .ok ch f full ∧
              (ch.helperExit ≠ n ∨ f ≠ 0 ∨ full = true ∨ ∃ w, ch = .notStarted w))

/-- K2's accept per kernel + exit code: leanchecker 0 + exactly its accept line, con-leche 0 +
exactly `con-leche: accepted <digits> declarations (--verified)` + LF, NanoDa 0 + nothing; stderr
empty. -/
def Accepts : Kernel → Nat → ByteArray → ByteArray → Prop
  | .lean, 0, out, err => out.data.toList = utf8 leanAccept ∧ err.data.toList = []
  | .conLeche, 0, out, err =>
    (∃ ds : List UInt8,
        ds ≠ [] ∧
          (∀ d ∈ ds, 48 ≤ d ∧ d ≤ 57) ∧
          out.data.toList = utf8 conAcceptHead ++ ds ++ utf8 conAcceptTail) ∧
      err.data.toList = []
  | .nanoda, 0, out, err => out.data.toList = [] ∧ err.data.toList = []
  | _, _, _, _ => False

/-- K2's reject per kernel + exit code: leanchecker 1 + stdout beginning with its rejection, or with
the accept line followed by the quotient post-check's rejection; con-leche 1 + stderr beginning
`invalid`; NanoDa 1 + stderr beginning with an unpermitted axiom. -/
def Rejects : Kernel → Nat → ByteArray → ByteArray → Prop
  | .lean, 1, out, _ =>
    utf8 leanReject <+: out.data.toList ∨ utf8 leanAccept ++ utf8 quotReject <+: out.data.toList
  | .conLeche, 1, _, err => utf8 conReject <+: err.data.toList
  | .nanoda, 1, _, err => utf8 nanodaReject <+: err.data.toList
  | _, _, _, _ => False

/-- K2's decline: con-leche 2 + stderr beginning `not implemented yet`. -/
def Declines : Kernel → Nat → ByteArray → Prop
  | .conLeche, 2, err => utf8 conDecline <+: err.data.toList
  | _, _, _ => False

end FvdepAudit.Judge.Kernel.Spec
