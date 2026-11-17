import FvdepCore.Index.Command
import FvdepCore.Sandbox
import FvdepCore.Step
import FvdepIO.Spawn
import FvdepIO.Sys

/-! The sandbox runner (contract `docs/contracts/U5-sandbox.md` R2–R6; ledger residue
`sandbox-spawn`): one step = bwrap spawned with `bwrapArgs` (R1), stdout, stderr, the status
descriptor + descriptor 4 pumped together (R3), the deadline enforced by SIGKILL (R4), the outcome
classified (`classify`, R6) + the frame read (`FvdepCore.Step.read`). The caller owns the run
directory (R7). -/

namespace FvdepIO.Sandbox

open FvdepCore.Sandbox FvdepCore.Step

/-- R3: a stream's first + last `keep` bytes + its total. -/
structure Retained where
  head : ByteArray := .empty
  tail : ByteArray := .empty
  total : Nat := 0

/-- The head fills first; past it, the tail keeps the last `keep` bytes. -/
def Retained.push (keep : Nat) (r : Retained) (chunk : ByteArray) : Retained :=
  let room := keep - r.head.size
  let rest := r.tail ++ chunk.extract room chunk.size
  { head := r.head ++ chunk.extract 0 room
    tail := if keep < rest.size then rest.extract (rest.size - keep) rest.size else rest
    total := r.total + chunk.size }

def Retained.kept (r : Retained) : ByteArray := r.head ++ r.tail

def Retained.dropped (r : Retained) : Nat := r.total - r.head.size - r.tail.size

/-- What descriptor 4 delivered (R3, R8). -/
inductive Received where
  | ok (o : Output)
  | overflow
  | invalid

/-- One step as the supervisor observed it. -/
structure Observation where
  outcome : Outcome
  stdout : Retained
  stderr : Retained
  frame : Received

/-- Milliseconds the channels get to close after the deadline kill (R4). -/
def drainGrace : Nat := 5000

/-- bwrap's status lines past this many bytes are dropped (bwrap writes two short lines). -/
def statusCap : Nat := 65536

structure Pumps where
  out : Retained := {}
  err : Retained := {}
  status : ByteArray := .empty
  frame : ByteArray := .empty
  overflow : Bool := false

/-- A chunk from channel `ch`: 0 = stdout, 1 = stderr, 2 = status, 3 = descriptor 4. -/
def Pumps.add (keep frameCap : Nat) (p : Pumps) (ch : Nat) (chunk : ByteArray) : Pumps :=
  match ch with
  | 0 => { p with out := p.out.push keep chunk }
  | 1 => { p with err := p.err.push keep chunk }
  | 2 => if p.status.size < statusCap then { p with status := p.status ++ chunk } else p
  | _ =>
    if p.overflow || frameCap < p.frame.size + chunk.size then
      { p with
        overflow := true, frame := .empty }
    else { p with frame := p.frame ++ chunk }

/-- R3 + R4: every channel read to its end; the deadline (monotonic ms) kills bwrap once, then
the channels still drain for at most `drainGrace` (the pid namespace dies with bwrap ⇒ every writer
closes). -/
partial def pump (pid : UInt32) (chans : Array (Nat × Nat)) (deadline : Nat) (killed : Bool)
    (keep frameCap : Nat) (p : Pumps) : IO (Pumps × Bool) := do
  if chans.isEmpty then
    return (p, killed)
  let now ← IO.monoMsNow
  -- The kill ends every process of the step's PID namespace, so its descriptors close at once; one
  -- still open `drainGrace` later = a process outside that namespace (a bwrap fault): closed here,
  -- never a hang.
  if killed && deadline + drainGrace ≤ now then
    for (fd, _) in chans do
      discard <| FvdepIO.Sys.Native.close fd.toUInt32
    return (p, killed)
  let killed ←
    if !killed && deadline ≤ now then
      do
        let _ ← FvdepIO.Spawn.kill pid 9
        pure true
    else
      pure killed
  let wait := if killed then 1000 else min (deadline - now) 1000
  match ← FvdepIO.Spawn.poll (chans.map (·.1)) wait.toUInt32 with
  | .error 4 =>
    pump pid chans deadline killed keep frameCap p
  | .error e =>
    throw (IO.userError s!"poll: {FvdepIO.Spawn.errnoText e}")
  | .ok revents =>
    let mut p := p
    let mut left := #[]
    for (fd, ch) in chans, ev in revents do
      if ev == 0 then
        left := left.push (fd, ch)
      else
        match ← FvdepIO.Sys.Native.read fd.toUInt32 65536 with
        | .ok chunk =>
          if chunk.isEmpty then
            discard <| FvdepIO.Sys.Native.close fd.toUInt32
          else
            p := p.add keep frameCap ch chunk
            left := left.push (fd, ch)
        | .error 4 =>
          left := left.push (fd, ch)
        | .error _ =>
          discard <| FvdepIO.Sys.Native.close fd.toUInt32
    pump pid left deadline killed keep frameCap p

/-- bwrap's own exit (its status descriptor carries the step's; `EINTR` retried). -/
partial def reap (pid : UInt32) : IO Unit := do
  match ← FvdepIO.Spawn.wait pid with
  | .error 4 =>
    reap pid
  | _ =>
    pure ()

/-- The first line of a stream's kept head (R6's setup-failure detail). -/
def firstLine (b : ByteArray) : String :=
  match (FvdepCore.Index.Command.textOfBytes b).splitOn "\n" with
  | l :: _ => l
  | [] => ""

/-- One step: `bwrap` (an absolute path, T1's) runs `bwrapArgs spec`. -/
def run (bwrap : String) (spec : Spec) (lim : Limits) : IO (Except String Observation) := do
  match ← FvdepIO.Spawn.bwrap bwrap ("bwrap" :: bwrapArgs spec).toArray with
  | .error e =>
    return .error s!"bwrap could not start: {FvdepIO.Spawn.errnoText e}"
  | .ok #[pid, o, e, s, f] =>
    let start ← IO.monoMsNow
    let (p, killed) ←
      pump pid.toUInt32 #[(o, 0), (e, 1), (s, 2), (f, 3)] (start + lim.deadline * 1000) false
          (lim.diagnosticBytes / 2) lim.frameBytes {}
    reap pid.toUInt32
    let frame :=
      if p.overflow then .overflow
      else
        match read p.frame with
        | some out => .ok out
        | none => .invalid
    return .ok
        { outcome := classify (statusLines p.status) killed (firstLine p.err.head)
          stdout := p.out
          stderr := p.err
          frame }
  | .ok _ =>
    return .error "bwrap answered no process"

end FvdepIO.Sandbox
