import FvdepCore.Bundle
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

/-- Horspool's skip table of a nonempty marker: per byte value, the shift its occurrence as a
window's last byte allows. -/
def skipOf (m : ByteArray) : Array Nat :=
  Id.run do
    let mut t := (List.replicate 256 m.size).toArray
    for j in [0:m.size - 1] do
      t := t.set! m[j]!.toNat (m.size - 1 - j)
    return t

/-- The first index ≥ `start` where the nonempty marker `m` occurs in `b` (`skip` = `skipOf m`). -/
def find (b m : ByteArray) (skip : Array Nat) (start : Nat) : Option Nat :=
  Id.run do
    let k := m.size
    let mut i := start
    while i + k ≤ b.size do
      let last := b[i + k - 1]!
      if last == m[k - 1]! then
        let mut hit := true
        for j in [0:k - 1] do
          if b[i + j]! != m[j]! then
            hit := false
            break
        if hit then
          return some i
      i := i + max 1 skip[last.toNat]!
    return none

/-- The index after the last line feed before `i` (0 when none). -/
def lineStart (b : ByteArray) (i : Nat) : Nat :=
  Id.run do
    let mut j := i
    while 0 < j do
      if b[j - 1]! == 10 then
        return j
      j := j - 1
    return 0

/-- The index of the first line feed at or after `i`. -/
def lineEnd (b : ByteArray) (i : Nat) : Option Nat :=
  Id.run do
    let mut j := i
    while j < b.size do
      if b[j]! == 10 then
        return some j
      j := j + 1
    return none

/-- B1 while pumping (R3): a stream's first complete line holding `marker` that `parse` reads, found
before any drop — the stream searched for the marker (no work per line), a hit's line read alone,
the unfinished line carried (its first `cap` bytes; an overlong line's message marked `…`). -/
structure Scan where
  carry : ByteArray := .empty
  cut : Bool := false
  found : Option FvdepCore.Bundle.Diag := none

/-- A marked line's diagnostic. -/
def Scan.probe (parse : String → Option FvdepCore.Bundle.Diag) (line : ByteArray) (cut : Bool) :
    Option FvdepCore.Bundle.Diag :=
  (parse (FvdepCore.Index.Command.textOfBytes line)).map fun d =>
    if cut then { d with message := d.message ++ "…" } else d

def Scan.push (cap : Nat) (parse : String → Option FvdepCore.Bundle.Diag) (marker : ByteArray)
    (skip : Array Nat) (s : Scan) (chunk : ByteArray) : Scan :=
  Id.run do
    if s.found.isSome then
      return s
    let buf := s.carry ++ chunk
    let mut pos := 0
    while true do
      match find buf marker skip pos with
      | none =>
        break
      | some k =>
        let start := lineStart buf k
        match lineEnd buf (k + marker.size) with
        | none =>
          return { carry := buf.extract start (start + cap),
                   cut := s.cut || cap < buf.size - start }
        | some e =>
          let cut := (start == 0 && s.cut) || cap < e - start
          if let some d := Scan.probe parse (buf.extract start (min e (start + cap))) cut then
            return { found := some d }
          pos := e + 1
    let start := lineStart buf buf.size
    return {
        carry := buf.extract start (min buf.size (start + cap))
        cut := (start == 0 && s.cut) || cap < buf.size - start }

/-- The end of the stream: its unterminated last line, read like the others. -/
def Scan.finish (parse : String → Option FvdepCore.Bundle.Diag) (marker : ByteArray)
    (skip : Array Nat) (s : Scan) : Option FvdepCore.Bundle.Diag :=
  s.found <|> if (find s.carry marker skip 0).isSome then Scan.probe parse s.carry s.cut else none

/-- Lean's `--json` messages on stdout (keys sorted, compact) + its text form on stderr. -/
def jsonMarker : ByteArray := "\"severity\":\"error\"".toUTF8

def jsonSkip : Array Nat := skipOf jsonMarker

def textMarker : ByteArray := ": error".toUTF8

def textSkip : Array Nat := skipOf textMarker

/-- What descriptor 4 delivered (R3, R8). -/
inductive Received where
  | ok (o : Output)
  | overflow
  | invalid

/-- One step as the supervisor observed it (+ B1's first error diagnostic of each stream). -/
structure Observation where
  outcome : Outcome
  stdout : Retained
  stderr : Retained
  frame : Received
  firstOut : Option FvdepCore.Bundle.Diag := none
  firstErr : Option FvdepCore.Bundle.Diag := none

/-- Milliseconds the channels get to close after the deadline kill (R4). -/
def drainGrace : Nat := 5000

/-- bwrap's status lines past this many bytes are dropped (bwrap writes two short lines). -/
def statusCap : Nat := 65536

structure Pumps where
  out : Retained := {}
  err : Retained := {}
  outScan : Scan := {}
  errScan : Scan := {}
  status : ByteArray := .empty
  frame : ByteArray := .empty
  overflow : Bool := false

/-- A chunk from channel `ch`: 0 = stdout, 1 = stderr, 2 = status, 3 = descriptor 4 (`keep` = each
stream's head + tail, `2 × keep` = one diagnostic line's cap). -/
def Pumps.add (keep frameCap : Nat) (p : Pumps) (ch : Nat) (chunk : ByteArray) : Pumps :=
  match ch with
  | 0 =>
    { p with
      out := p.out.push keep chunk
      outScan := p.outScan.push (2 * keep) FvdepCore.Bundle.ofJson jsonMarker jsonSkip chunk }
  | 1 =>
    { p with
      err := p.err.push keep chunk
      errScan := p.errScan.push (2 * keep) FvdepCore.Bundle.ofText textMarker textSkip chunk }
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

/-- One step: `bwrap` (an absolute path, T1's) runs `bwrapArgs spec`; the deadline = `untilMs` (a
phase's absolute monotonic deadline, P1) else `lim.deadline` seconds from the spawn. -/
def run (bwrap : String) (spec : Spec) (lim : Limits) (untilMs : Option Nat := none) :
    IO (Except String Observation) := do
  match ← FvdepIO.Spawn.bwrap bwrap ("bwrap" :: bwrapArgs spec).toArray with
  | .error e =>
    return .error s!"bwrap could not start: {FvdepIO.Spawn.errnoText e}"
  | .ok #[pid, o, e, s, f] =>
    let start ← IO.monoMsNow
    let (p, killed) ←
      pump pid.toUInt32 #[(o, 0), (e, 1), (s, 2), (f, 3)]
          (untilMs.getD (start + lim.deadline * 1000)) false (lim.diagnosticBytes / 2)
          lim.frameBytes {}
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
          frame
          firstOut := p.outScan.finish FvdepCore.Bundle.ofJson jsonMarker jsonSkip
          firstErr := p.errScan.finish FvdepCore.Bundle.ofText textMarker textSkip }
  | .ok _ =>
    return .error "bwrap answered no process"

end FvdepIO.Sandbox
