import FvdepCore.Evidence
import FvdepCore.Index.Command
import FvdepCore.Phase
import FvdepCore.Profile.Check
import FvdepCore.Sandbox

/-! U7 K (contract `docs/contracts/U7-judge.md` K1–K3): one kernel step's layout (K1), its status
(K2's table: total, in order) + NanoDa's config (K3). Pure; the step itself = U5's runner
(residue `sandbox-spawn`), the kernels' own verdicts = residue `kernels`. -/

namespace FvdepCore.Judge

open FvdepCore.Evidence FvdepCore.Phase FvdepCore.Sandbox

/-! ## K1 -/

/-- K1's export path inside the step (the staged e2). -/
def e2Path : String := "/fvdep/src/e2.ndjson"

/-- K1's NanoDa config path inside the step. -/
def nanodaPath : String := "/fvdep/src/nanoda.json"

/-- K1 + K4: a kernel's binary under the toolchain's `bin`. -/
def kernelBin : Kernel → String
  | .lean => "leanchecker"
  | .conLeche => "con-leche"
  | .nanoda => "nanoda_bin"

/-- K1: a kernel's command with its binary at `bin`. -/
def kernelArgvAt (bin : String) (threads : Nat) (k : Kernel) : List String :=
  bin ::
    match k with
    | .lean => ["--from-export", e2Path]
    | .conLeche => ["--verified", "--jobs=" ++ num threads, e2Path]
    | .nanoda => [nanodaPath]

/-- K1: a kernel's binary inside the step = under the toolchain's `bin` at `/fvdep/sysroot`. -/
def kernelPath (k : Kernel) : String := "/fvdep/sysroot/bin/" ++ kernelBin k

/-- K1: a kernel's command. -/
def kernelArgv (threads : Nat) (k : Kernel) : List String := kernelArgvAt (kernelPath k) threads k

/-- D3: a stub kernel's binary inside the step = staged beside e2 (a test seam; never PROVEN). -/
def stubPath (k : Kernel) : String := "/fvdep/src/stub-" ++ kernelBin k

/-- K1: one kernel step — the toolchain at `/fvdep/sysroot`, the helper at `/fvdep/step`, the staged
e2 + NanoDa's config at `/fvdep/src`, nothing else (no project or proof view); the environment =
`LEAN_ABORT_ON_PANIC=1` alone; the helper's per-file cap, then the kernel's command (its binary at
`bin`: the toolchain's, or D3's stub). -/
def kernelSpec (sysroot step src : String) (lim : Limits) (threads : Nat) (k : Kernel)
    (bin : String := kernelPath k) : Spec :=
  { ro := [(sysroot, .sysroot), (step, .step), (src, .src)]
    env := [("LEAN_ABORT_ON_PANIC", "1")]
    workBytes := lim.workBytes
    tmpBytes := lim.tmpBytes
    argv := ["--file-bytes", num lim.fileCap, "--"] ++ kernelArgvAt bin threads k }

/-! ## K2 -/

/-- K2's view of the step's frame: unreadable, over its cap, or the child's status + the data files
it carried + whether a tmpfs was full in the helper's sample after the child. -/
inductive KFrame where
  | invalid
  | overflow
  | ok (child : Child) (files : Nat) (full : Bool)
  deriving DecidableEq, Repr

/-- K2's input: one kernel step as U5 observed it + the two streams as kept (`whole` = no byte
dropped from either) + the step's deadline in seconds. -/
structure KernelRun where
  outcome : Outcome
  frame : KFrame
  stdout : ByteArray
  stderr : ByteArray
  whole : Bool
  deadline : Nat

/-- K2's result: infrastructure (exit 2, never a verdict) or the kernel's status (U2's). -/
inductive KResult where
  | infra (code : Infra) (detail : String)
  | status (s : KernelStatus)
  deriving DecidableEq, Repr

/-- A result without its texts (the claims' view: the details = tested presentation). -/
inductive KShape where
  | infra (code : Infra)
  | accept
  | reject
  | crash
  | timeout (seconds : Nat)
  | decline
  deriving DecidableEq, Repr

def KResult.shape : KResult → KShape
  | .infra c _ => .infra c
  | .status .accept => .accept
  | .status .reject => .reject
  | .status .crash => .crash
  | .status (.timeout s) => .timeout s
  | .status (.decline _) => .decline

/-- `b`'s bytes = `s`'s UTF-8. -/
def bytesAre (s : String) (b : ByteArray) : Bool := b.data.toList == s.toUTF8.data.toList

/-- `b`'s bytes begin with `p`'s UTF-8. -/
def bytesStart (p : String) (b : ByteArray) : Bool := p.toUTF8.data.toList.isPrefixOf b.data.toList

def isDigitByte (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

def leanAccept : String := "Lean default kernel accepts the solution\n"

def leanReject : String := "Lean default kernel rejects the solution: "

def quotReject : String := "Quotient post-check rejects the solution: "

def conAcceptHead : String := "con-leche: accepted "

def conAcceptTail : String := " declarations (--verified)\n"

def conReject : String := "con-leche: invalid:"

def conDecline : String := "con-leche: not implemented yet:"

def nanodaReject : String := "Error: export file declares unpermitted axiom"

/-- con-leche's accept line: `con-leche: accepted <N> declarations (--verified)` + LF, N = one or
more decimal digits. -/
def isConAccept (b : ByteArray) : Bool :=
  let xs := b.data.toList
  let p := conAcceptHead.toUTF8.data.toList
  let q := conAcceptTail.toUTF8.data.toList
  p.isPrefixOf xs && q.isSuffixOf xs && p.length + q.length < xs.length &&
    ((xs.drop p.length).take (xs.length - p.length - q.length)).all isDigitByte

/-- A stream's lines, split at LF in bytes (each line decoded alone: a later invalid byte never
re-decodes an earlier line). -/
def splitLf : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: rest =>
    if b == 10 then [] :: splitLf rest
    else
      match splitLf rest with
      | l :: ls => (b :: l) :: ls
      | [] => [[b]]

def lineText (l : List UInt8) : String :=
  FvdepCore.Index.Command.textOfBytes (ByteArray.mk l.toArray)

/-- A decline's detail: the kernel's first stderr line, its run time (` t=…`) cut — two equal
declines must compare equal (U2's conflict check, K5's reuse) —, at most 1,024 bytes. -/
def declineDetail (err : ByteArray) : String :=
  let l := lineText ((splitLf err.data.toList).headD [])
  let core :=
    match l.splitOn " t=" with
    | [] => l
    | [x] => x
    | parts => " t=".intercalate parts.dropLast
  FvdepCore.Profile.cutDetail core

/-- K2's accept per kernel + exit code: leanchecker 0 + exactly its accept line, con-leche 0 +
exactly its accept line, NanoDa 0 + no stdout; stderr empty. -/
def acceptsB : Kernel → Nat → ByteArray → ByteArray → Bool
  | .lean, 0, out, err => bytesAre leanAccept out && bytesAre "" err
  | .conLeche, 0, out, err => isConAccept out && bytesAre "" err
  | .nanoda, 0, out, err => bytesAre "" out && bytesAre "" err
  | _, _, _, _ => false

/-- K2's reject: leanchecker 1 + its rejection (or the accept line, then the quotient post-check's
rejection) on stdout; con-leche 1 + `invalid` on stderr; NanoDa 1 + an unpermitted axiom on
stderr. -/
def rejectsB : Kernel → Nat → ByteArray → ByteArray → Bool
  | .lean, 1, out, _ => bytesStart leanReject out || bytesStart (leanAccept ++ quotReject) out
  | .conLeche, 1, _, err => bytesStart conReject err
  | .nanoda, 1, _, err => bytesStart nanodaReject err
  | _, _, _, _ => false

/-- K2's decline: con-leche 2 + `not implemented yet` on stderr. -/
def declinesB : Kernel → Nat → ByteArray → Bool
  | .conLeche, 2, err => bytesStart conDecline err
  | _, _, _ => false

/-- K2's per-kernel table over the child's exit code + its streams: an accept (both streams whole),
else a reject, else a decline, else a crash. -/
def kernelTable (k : Kernel) (code : Nat) (out err : ByteArray) (whole : Bool) : KernelStatus :=
  if whole && acceptsB k code out err then .accept
  else
    if rejectsB k code out err then .reject
    else if declinesB k code err then .decline (declineDetail err) else .crash

/-- K2 (total, in order): U5's step observation first — setup + protocol failures, an unreadable or
over-cap frame, a status the helper contradicts, a data file, a full tmpfs, a child that never
started → infrastructure; the deadline → `timeout`; a signal → crash; then the kernel's table. -/
def kernelStatus (k : Kernel) (r : KernelRun) : KResult :=
  match r.outcome with
  | .setupFailed d => .infra .sandboxSetup d
  | .protocol => .infra .sandboxSetup "the step reported two exit codes"
  | .timedOut => .status (.timeout r.deadline)
  | .exited n =>
    match r.frame with
    | .invalid => .infra .io "the step helper failed"
    | .overflow => .infra .io "the step's outputs exceeded their cap"
    | .ok child files full =>
      if child.helperExit != n then .infra .io "the step helper failed"
      else
        if files != 0 then .infra .io "the kernel step wrote a file"
        else
          if full then .infra .io "the step exceeded a size cap"
          else
            match child with
            | .notStarted why => .infra .io s!"the step did not start: {why}"
            | .signaled _ => .status .crash
            | .exited c => .status (kernelTable k c r.stdout r.stderr r.whole)

/-- J4: a kernel's own message — the first nonblank line of its stderr, else of its stdout, at most
1,024 bytes (`(no output)` when both are blank). -/
def kernelLine (r : KernelRun) : String :=
  let firstOf (b : ByteArray) : Option String :=
    (splitLf b.data.toList).findSome? fun l =>
      let t := lineText l
      if FvdepCore.Index.Assemble.trimText t != "" then some t else none
  FvdepCore.Profile.cutDetail
    (((firstOf r.stderr).orElse fun _ => firstOf r.stdout).getD "(no output)")

/-! ## K3 -/

/-- K3: NanoDa's config: the staged export, the allowlist as permitted axioms, an unpermitted one
declared anywhere = a hard error, `threads` workers, Nat + String extensions. -/
def nanodaValue (allowlist : List String) (threads : Nat) : FvdepCore.Json.Value :=
  .obj
    [("export_file_path", .str e2Path), ("nat_extension", .bool true),
      ("num_threads", .int threads), ("permitted_axioms", .arr (allowlist.map .str)),
      ("string_extension", .bool true), ("unpermitted_axiom_hard_error", .bool true),
      ("use_stdin", .bool false)]

/-- K3: the config file's bytes (canonical J). -/
def nanodaConfig (allowlist : List String) (threads : Nat) : ByteArray :=
  FvdepCore.Json.print (nanodaValue allowlist threads)

end FvdepCore.Judge
