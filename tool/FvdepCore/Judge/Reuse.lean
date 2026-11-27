import FvdepCore.Judge.Kernel

/-! K5 (contract `docs/contracts/U7-judge.md` Part B K5): one command's memo of kernel answers —
keyed by the complete invocation context, the kernel + the staged e2's digest; a completed status
alone is kept, the first one recorded per key answers it. -/

namespace FvdepCore.Judge

open FvdepCore.Evidence

/-- One kernel run's complete invocation context: T1's installation fingerprint, the kernel's pinned
binary digest, the step it runs (`kernelSpec`: mounts, environment, argv, tmpfs sizes), its step
limits (the deadline among them) + the staged config's digest (NanoDa's; empty for none) — the
profile's id alone is no key (an override or a re-ruling changes the context). -/
structure Invocation where
  fingerprint : String
  pin : String
  spec : FvdepCore.Sandbox.Spec
  limits : FvdepCore.Sandbox.Limits
  config : String
  deriving DecidableEq

/-- K5's key. -/
structure ReuseKey where
  invocation : Invocation
  kernel : Kernel
  e2 : String
  deriving DecidableEq

/-- A kernel's answer: its result + its J4 line (never its elapsed time). -/
abbrev Answer := KResult × String

/-- Completed statuses alone are recordable: infrastructure + a timeout are never reused. -/
def recordable : KResult → Bool
  | .status .accept | .status .reject | .status .crash | .status (.decline _) => true
  | .status (.timeout _) | .infra .. => false

/-- One command's memo: the recorded answers in their order. -/
abbrev Memo := List (ReuseKey × Answer)

def Memo.lookup (m : Memo) (k : ReuseKey) : Option Answer := (m.find? (·.1 == k)).map (·.2)

/-- A run's answer recorded once: an unrecordable result or a key already answered leaves `m`. -/
def Memo.record (m : Memo) (k : ReuseKey) (a : Answer) : Memo :=
  if recordable a.1 && (m.lookup k).isNone then m ++ [(k, a)] else m

/-- The memo a command's run events (each an actual pinned run's answer, in order) build. -/
def Memo.ofEvents (es : List (ReuseKey × Answer)) : Memo :=
  es.foldl (fun m e => m.record e.1 e.2) []

end FvdepCore.Judge
