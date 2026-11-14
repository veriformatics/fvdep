import FvdepAudit.Sys.Model

/-! Syscall-script denotation. The native guard linearizes an entire API operation; finalization
is one close-if-open operation in that same sequence. A trace records calls, not successful IO
alone: recovered EINTR attempts remain visible. -/

namespace FvdepAudit.Sys.Spec

open FvdepIO.Sys FvdepIO.Sys.Model
open FvdepIO.Sys.Policy (Script ScriptIO)

abbrev Trace := List Event

/-- POSIX read + write results report at most the requested bytes. Open returns a newly owned
file description; allocation until the one close attempt is the OS-side script assumption. -/
def Consistent (events : Trace) : Prop :=
  ∀ e ∈ events,
    match e.request, e.response with
    | .write _ _ count, .ok n => n ≤ count
    | .read _ count, .ok n => n ≤ count
    | _, _ => True

/-- One syscall step, including at most `budget` recovered EINTRs. A close never uses Retry. -/
inductive Retry (request : Request) : Nat → Trace → Except Cause Nat → Prop where
  | success (budget n) : Retry request budget [⟨request, .ok n⟩] (.ok n)
  |
  failure (budget n) (notInterrupted : n ≠ 4) :
    Retry request budget [⟨request, .error n⟩] (.error (.errno n))
  | exhausted : Retry request 0 [⟨request, .error 4⟩] (.error .retryExhausted)
  |
  interrupted {budget events result} (rest : Retry request budget events result) :
    Retry request (budget + 1) (⟨request, .error 4⟩ :: events) result

/-- Every positive acknowledgement advances by exactly that count. The next remaining-byte step
starts with a fresh retry budget; a zero result is terminal rather than a progress loop. -/
inductive Writes (fd : Nat) : Nat → Nat → Trace → Except Cause Unit → Prop where
  | empty (offset) : Writes fd offset 0 [] (.ok ())
  |
  progress {offset remaining n first rest result} (nonempty : 0 < remaining)
    (attempt : Retry (.write fd offset (min remaining (2 ^ 30))) 64 first (.ok n))
    (positive : 0 < n) (bounded : n ≤ min remaining (2 ^ 30))
    (tail : Writes fd (offset + n) (remaining - n) rest result) :
    Writes fd offset remaining (first ++ rest) result
  |
  stalled {offset remaining first} (nonempty : 0 < remaining)
    (attempt : Retry (.write fd offset (min remaining (2 ^ 30))) 64 first (.ok 0)) :
    Writes fd offset remaining first (.error .noProgress)
  |
  failed {offset remaining first cause} (nonempty : 0 < remaining)
    (attempt : Retry (.write fd offset (min remaining (2 ^ 30))) 64 first (.error cause)) :
    Writes fd offset remaining first (.error cause)

def error (op : Op) (path : Path) (cause : Cause) : SysError := { op, cause, path }

def unitResult (op : Op) (path : Path) : Except Cause Nat → Except SysError Nat
  | .ok _ => .ok 0
  | .error cause => .error (error op path cause)

def writeResult (path : Path) : Except Cause Unit → Except SysError Nat
  | .ok _ => .ok 0
  | .error cause => .error (error .write path cause)

/-- Close is a single attempt, including EINTR. -/
def closeResult (op : Op) (path : Path) : Response → Except SysError Nat
  | .ok _ => .ok 0
  | .error n => .error (error op path (.errno n))

def directoryResult (path : Path) (primary : Except Cause Nat) (closed : Response) :
    Except SysError Nat :=
  match primary, closed with
  | .ok _, r => closeResult .closeDir path r
  | .error cause, .ok _ => .error (error .syncDir path cause)
  | .error cause, .error n =>
    .error { error .syncDir path cause with secondary := [(.closeDir, n)] }

inductive Create (path : Path) (mode : Mode) : Trace → Except SysError Nat → Prop where
  |
  accepted {events fd} (attempt : Retry (.create path mode) 64 events (.ok fd)) :
    Create path mode events (.ok fd)
  |
  failed {events cause} (attempt : Retry (.create path mode) 64 events (.error cause)) :
    Create path mode events (.error (error .create path cause))

inductive Directory (path : Path) : Trace → Except SysError Nat → Prop where
  |
  openFailed {events cause} (attempt : Retry (.openDir path) 64 events (.error cause)) :
    Directory path events (.error (error .openDir path cause))
  |
  opened {opened synced fd primary closed} (openAttempt : Retry (.openDir path) 64 opened (.ok fd))
    (syncAttempt : Retry (.fsync fd) 64 synced primary) :
    Directory path (opened ++ synced ++ [⟨.close fd, closed⟩]) (directoryResult path primary closed)

def after (writer : WriterState) : WriterAction → WriterState
  | .close | .finalize => { writer with closed := true }
  | _ => writer

/-- Finalization's dummy `.ok 0` denotes no report, not successful durability IO. -/
inductive WriterOperation (writer : WriterState) :
    WriterAction → Trace → Except SysError Nat → Prop where
  |
  alreadyClosed (action) (closed : writer.closed = true) (explicit : action ≠ .finalize) :
    WriterOperation writer action []
      (.error
        (error
          (match action with
          | .write _ => .write
          | .sync => .sync
          | _ => .close)
          writer.path .alreadyClosed))
  | finalizedClosed (closed : writer.closed = true) : WriterOperation writer .finalize [] (.ok 0)
  |
  written {size events result} (opened : writer.closed = false)
    (steps : Writes writer.fd 0 size events result) :
    WriterOperation writer (.write size) events (writeResult writer.path result)
  |
  synced {events result} (opened : writer.closed = false)
    (attempt : Retry (.fsync writer.fd) 64 events result) :
    WriterOperation writer .sync events (unitResult .sync writer.path result)
  |
  closed {response} (opened : writer.closed = false) :
    WriterOperation writer .close [⟨.close writer.fd, response⟩]
      (closeResult .close writer.path response)
  |
  finalized {response} (opened : writer.closed = false) :
    WriterOperation writer .finalize [⟨.close writer.fd, response⟩] (.ok 0)

inductive WriterTrace :
    WriterState → List WriterAction → Trace → List (Except SysError Nat) → Prop where
  | nil (writer) : WriterTrace writer [] [] []
  |
  cons {writer action actions first rest result results}
    (head : WriterOperation writer action first result)
    (tail : WriterTrace (after writer action) actions rest results) :
    WriterTrace writer (action :: actions) (first ++ rest) (result :: results)

def closeCount (events : Trace) : Nat :=
  (events.filter fun e =>
      match e.request with
      | .close _ => true
      | _ => false).length

def successfulCount : Except Cause Nat → Nat
  | .ok n => n
  | .error _ => 0

def acknowledged (events : Trace) : Nat :=
  (events.map fun e =>
      match e.request, e.response with
      | .write _ _ _, .ok n => n
      | _, _ => 0).sum

def writerOnly (fd : Nat) (events : Trace) : Prop :=
  ∀ e ∈ events,
    match e.request with
    | .write actual _ count => actual = fd ∧ count ≤ 2 ^ 30
    | .fsync actual | .close actual => actual = fd
    | _ => False

/-- A recovered prefix has at most 64 EINTRs; the 65th interruption terminates. -/
def RetryLimit : Prop :=
  (∀ request budget events result,
      Retry request budget events result → events.length ≤ budget + 1) ∧
    (∀ request, Retry request 64 (List.replicate 65 ⟨request, .error 4⟩) (.error .retryExhausted)) ∧
    ∀ request budget events result,
      Retry request budget events result → ∀ e ∈ events, e.request = request

/-! ## `replace`, `readFile`, `withWriterLock` (F2–F3), written apart from the policy: names as
text; literal constants (64 = attempts per step + temp names, EEXIST 17, ENOENT 2, EWOULDBLOCK 11,
EINTR 4, temp mode 0644 = 420, read steps ≤ 2^20 bytes, the 2^30-byte read cap). -/

/-- F2's names: the target `<dir>/<name>`, attempt `n`'s temp `<dir>/.<name>.tmp-<pid>-<n>`, the
writer lock `<dir>/.fvdep-writer.lock`. -/
def targetText (dir : Path) (name : Name) : String := dir.toString ++ "/" ++ name.toString

def tempText (dir : Path) (name : Name) (pid n : Nat) : String :=
  dir.toString ++ "/." ++ name.toString ++ ".tmp-" ++ toString pid ++ "-" ++ toString n

def lockText (dir : Path) : String := dir.toString ++ "/.fvdep-writer.lock"

/-- The calls naming the path text `t`. -/
def Names (t : String) : Request → Prop
  | .create p _ | .openDir p | .openRead p | .unlink p | .openLock p => p.toString = t
  | .rename source target => source.toString = t ∨ target.toString = t
  | _ => False

/-- F2's temp walk from attempt `n`: create-exclusive with mode 0644 (one F3 step); EEXIST → the
next name; all 64 taken → `tempsTaken` naming the last. -/
inductive TempWalk (dir : Path) (name : Name) (pid : Nat) :
    Nat → Trace → Except SysError (Path × Nat) → Prop where
  |
  created {n events fd} {temp : Path} {mode : Mode} (bound : n < 64)
    (named : temp.toString = tempText dir name pid n) (perm : mode.toNat = 420)
    (attempt : Retry (.create temp mode) 64 events (.ok fd)) :
    TempWalk dir name pid n events (.ok (temp, fd))
  |
  taken {n first rest result} {temp : Path} {mode : Mode} (bound : n < 64)
    (named : temp.toString = tempText dir name pid n) (perm : mode.toNat = 420)
    (attempt : Retry (.create temp mode) 64 first (.error (.errno 17)))
    (next : TempWalk dir name pid (n + 1) rest result) :
    TempWalk dir name pid n (first ++ rest) result
  |
  failed {n events cause} {temp : Path} {mode : Mode} (bound : n < 64)
    (named : temp.toString = tempText dir name pid n) (perm : mode.toNat = 420)
    (attempt : Retry (.create temp mode) 64 events (.error cause)) (other : cause ≠ .errno 17) :
    TempWalk dir name pid n events (.error { op := .create, cause, path := temp })
  |
  allTaken {last : Path} (named : last.toString = tempText dir name pid 63) :
    TempWalk dir name pid 64 [] (.error { op := .create, cause := .tempsTaken, path := last })

/-- Cleanup's unlink of the temp (one F3 step); a failure appends `(unlink, errno)`, EINTR past
the budget. -/
inductive Unlinked (temp : Path) (e : SysError) : Trace → SysError → Prop where
  | removed {events n} (attempt : Retry (.unlink temp) 64 events (.ok n)) : Unlinked temp e events e
  |
  failed {events n} (attempt : Retry (.unlink temp) 64 events (.error (.errno n))) :
    Unlinked temp e events { e with secondary := e.secondary ++ [(.unlink, n)] }
  |
  interrupted {events} (attempt : Retry (.unlink temp) 64 events (.error .retryExhausted)) :
    Unlinked temp e events { e with secondary := e.secondary ++ [(.unlink, 4)] }

/-- Cleanup while the temp is open: its one close attempt, then the unlink. -/
inductive Abandoned (temp : Path) (fd : Nat) (e : SysError) : Trace → SysError → Prop where
  |
  closed {n events e'} (unlink : Unlinked temp e events e') :
    Abandoned temp fd e (⟨.close fd, .ok n⟩ :: events) e'
  |
  closeFailed {n events e'}
    (unlink : Unlinked temp { e with secondary := e.secondary ++ [(.close, n)] } events e') :
    Abandoned temp fd e (⟨.close fd, .error n⟩ :: events) e'

/-- After the temp's close: one rename step onto the target, then `syncDir dir`. A failed rename
unlinks the temp (error path = the target); a `syncDir` failure after it = `durability`. -/
inductive Commit (dir : Path) (name : Name) (temp : Path) :
    Trace → Except SysError Unit → Prop where
  |
  renameFailed {renamed cleanup cause e} {target : Path}
    (named : target.toString = targetText dir name)
    (attempt : Retry (.rename temp target) 64 renamed (.error cause))
    (clean : Unlinked temp { op := .rename, cause, path := target } cleanup e) :
    Commit dir name temp (renamed ++ cleanup) (.error e)
  |
  unsynced {renamed synced n e} {target : Path} (named : target.toString = targetText dir name)
    (attempt : Retry (.rename temp target) 64 renamed (.ok n))
    (flush : Directory dir synced (.error e)) :
    Commit dir name temp (renamed ++ synced) (.error { e with durability := true })
  |
  replaced {renamed synced n m} {target : Path} (named : target.toString = targetText dir name)
    (attempt : Retry (.rename temp target) 64 renamed (.ok n))
    (flush : Directory dir synced (.ok m)) : Commit dir name temp (renamed ++ synced) (.ok ())

/-- From the open temp: all `size` bytes written, fsync, its one close, then the commit. A write
or sync failure abandons the temp; a failed close unlinks it. -/
inductive Body (dir : Path) (name : Name) (size : Nat) (temp : Path) (fd : Nat) :
    Trace → Except SysError Unit → Prop where
  |
  writeFailed {written cleanup cause e} (data : Writes fd 0 size written (.error cause))
    (clean : Abandoned temp fd { op := .write, cause, path := temp } cleanup e) :
    Body dir name size temp fd (written ++ cleanup) (.error e)
  |
  syncFailed {written synced cleanup cause e} (data : Writes fd 0 size written (.ok ()))
    (sync : Retry (.fsync fd) 64 synced (.error cause))
    (clean : Abandoned temp fd { op := .sync, cause, path := temp } cleanup e) :
    Body dir name size temp fd (written ++ synced ++ cleanup) (.error e)
  |
  closeFailed {written synced cleanup n m e} (data : Writes fd 0 size written (.ok ()))
    (sync : Retry (.fsync fd) 64 synced (.ok m))
    (clean : Unlinked temp { op := .close, cause := .errno n, path := temp } cleanup e) :
    Body dir name size temp fd (written ++ synced ++ ⟨.close fd, .error n⟩ :: cleanup) (.error e)
  |
  closed {written synced rest n m result} (data : Writes fd 0 size written (.ok ()))
    (sync : Retry (.fsync fd) 64 synced (.ok m)) (commit : Commit dir name temp rest result) :
    Body dir name size temp fd (written ++ synced ++ ⟨.close fd, .ok n⟩ :: rest) result

/-- F2 `replace dir name` of `size` bytes by process `pid`: the temp walk, then the body. -/
inductive Replace (dir : Path) (name : Name) (pid size : Nat) :
    Trace → Except SysError Unit → Prop where
  |
  noTemp {events e} (walk : TempWalk dir name pid 0 events (.error e)) :
    Replace dir name pid size events (.error e)
  |
  opened {created rest temp fd result} (walk : TempWalk dir name pid 0 created (.ok (temp, fd)))
    (body : Body dir name size temp fd rest result) :
    Replace dir name pid size (created ++ rest) result

/-- F2 + F3: read until a 0-byte read, each step asking `min (cap + 1) 2^20` bytes (`cap` = the
bytes still allowed); a positive read starts a fresh step; past `cap` → `tooLarge`. -/
inductive Reads (fd : Nat) : Nat → Nat → Trace → Except Cause Nat → Prop where
  |
  done {total cap events} (attempt : Retry (.read fd (min (cap + 1) (2 ^ 20))) 64 events (.ok 0)) :
    Reads fd total cap events (.ok total)
  |
  progress {total cap n first rest result}
    (attempt : Retry (.read fd (min (cap + 1) (2 ^ 20))) 64 first (.ok n)) (positive : 0 < n)
    (within : n ≤ cap) (tail : Reads fd (total + n) (cap - n) rest result) :
    Reads fd total cap (first ++ rest) result
  |
  tooLarge {total cap n events}
    (attempt : Retry (.read fd (min (cap + 1) (2 ^ 20))) 64 events (.ok n)) (over : cap < n) :
    Reads fd total cap events (.error .tooLarge)
  |
  failed {total cap events cause}
    (attempt : Retry (.read fd (min (cap + 1) (2 ^ 20))) 64 events (.error cause)) :
    Reads fd total cap events (.error cause)

/-- `readFile`'s result: the byte count; a failed close after a good read = the error; a read
failure keeps a failed close as its secondary cause. -/
def readResult (path : Path) : Except Cause Nat → Response → Except SysError (Option Nat)
  | .ok n, .ok _ => .ok (some n)
  | .ok _, .error e => .error { op := .close, cause := .errno e, path }
  | .error cause, .ok _ => .error { op := .read, cause, path }
  | .error cause, .error e => .error { op := .read, cause, path, secondary := [(.close, e)] }

/-- F2 `readFile path cap`: open (one F3 step; ENOENT → absent), the reads under the caller's byte
cap, one close attempt. -/
inductive ReadFile (path : Path) (cap : Nat) : Trace → Except SysError (Option Nat) → Prop where
  |
  absent {events} (attempt : Retry (.openRead path) 64 events (.error (.errno 2))) :
    ReadFile path cap events (.ok none)
  |
  openFailed {events cause} (attempt : Retry (.openRead path) 64 events (.error cause))
    (present : cause ≠ .errno 2) :
    ReadFile path cap events (.error { op := .openRead, cause, path })
  |
  opened {opened read fd result closed} (openAttempt : Retry (.openRead path) 64 opened (.ok fd))
    (body : Reads fd 0 cap read result) :
    ReadFile path cap (opened ++ read ++ [⟨.close fd, closed⟩]) (readResult path result closed)

/-- The lock failure: EWOULDBLOCK = `busy`; a failed close follows as the secondary cause. -/
def refusal (file : Path) (cause : Cause) (closed : Response) : SysError :=
  { op := .lock
    cause := if cause = .errno 11 then .busy else cause
    path := file
    secondary :=
      match closed with
      | .ok _ => []
      | .error n => [(.close, n)] }

/-- F2 `withWriterLock dir act` over the script monad: open the lock file (one F3 step; created if
absent), `flock` (one F3 step), `act` on the answers that follow, then one close attempt whose
failure is ignored (the close released the lock). A failure before `act` runs nothing + closes
what it opened. -/
inductive Lock {α : Type} (dir : Path) (act : ScriptIO α) (script : Script) :
    Trace → Except SysError α → Prop where
  |
  openFailed {opened cause} {file : Path} (named : file.toString = lockText dir)
    (attempt : Retry (.openLock file) 64 opened (.error cause)) :
    Lock dir act script opened (.error { op := .openLock, cause, path := file })
  |
  refused {opened locked fd cause closed} {file : Path} (named : file.toString = lockText dir)
    (openAttempt : Retry (.openLock file) 64 opened (.ok fd))
    (lockAttempt : Retry (.lock fd) 64 locked (.error cause)) :
    Lock dir act script (opened ++ locked ++ [⟨.close fd, closed⟩])
      (.error (refusal file cause closed))
  |
  ran {opened locked fd n closed} {file : Path} (named : file.toString = lockText dir)
    (openAttempt : Retry (.openLock file) 64 opened (.ok fd))
    (lockAttempt : Retry (.lock fd) 64 locked (.ok n)) :
    Lock dir act script
      (opened ++ locked ++ (act.run fun i => script (i + (opened.length + locked.length))).events ++
        [⟨.close fd, closed⟩])
      (.ok (act.run fun i => script (i + (opened.length + locked.length))).result)

/-! ## Directory model (F4): regular files by path text + descriptor ownership. Assumptions: a
stable directory (distinct path texts = distinct entries; no other process renames, removes or
writes them), cooperative writers (no other process touches the target or this call's temps),
rename atomic per the OS contract (one that reports failure may still have landed: NFS). -/

structure DirState where
  files : String → Option (List UInt8)
  owners : Nat → Option String

namespace DirState

def put (s : DirState) (p : String) (c : Option (List UInt8)) : DirState :=
  { s with files := fun q => if q = p then c else s.files q }

def own (s : DirState) (fd : Nat) (p : Option String) : DirState :=
  { s with owners := fun g => if g = fd then p else s.owners g }

/-- rename(2): the source's file takes the destination's name (replacing what was there); the
same name or a missing source changes nothing. -/
def move (s : DirState) (src dst : String) : DirState :=
  if src = dst then s
  else
    match s.files src with
    | none => s
    | some c => (s.put dst (some c)).put src none

end DirState

/-- A completed call's effect; `payload` = the bytes `write fd offset count` sends, from `offset`.
create (exclusive) = a new empty file owned by the returned descriptor; an open gives the
descriptor to its path (the lock file created empty if absent); a write appends the acknowledged
part of its slice to its descriptor's file; close releases the descriptor (also on failure);
rename moves; unlink removes; every other call + failure changes nothing. -/
def apply (payload : List UInt8) (s : DirState) : Event → DirState
  | ⟨.create p _, .ok fd⟩ => (s.put p.toString (some [])).own fd (some p.toString)
  | ⟨.openDir p, .ok fd⟩ => s.own fd (some p.toString)
  | ⟨.openRead p, .ok fd⟩ => s.own fd (some p.toString)
  | ⟨.openLock p, .ok fd⟩ =>
    (s.put p.toString (some ((s.files p.toString).getD []))).own fd (some p.toString)
  | ⟨.write fd offset _, .ok n⟩ =>
    match s.owners fd with
    | some p => s.put p ((s.files p).map (· ++ (payload.drop offset).take n))
    | none => s
  | ⟨.close fd, _⟩ => s.own fd none
  | ⟨.rename src dst, .ok _⟩ => s.move src.toString dst.toString
  | ⟨.unlink p, .ok _⟩ => s.put p.toString none
  | _ => s

/-- One call: its effect, or (a rename reporting failure) the move it may still have made. -/
inductive Step (payload : List UInt8) : DirState → Event → DirState → Prop where
  | applied (s e) : Step payload s e (apply payload s e)
  |
  landed (s src dst n) :
    Step payload s ⟨.rename src dst, .error n⟩ (s.move src.toString dst.toString)

inductive Steps (payload : List UInt8) : DirState → Trace → DirState → Prop where
  | nil (s) : Steps payload s [] s
  |
  cons {s e s' events s''} (head : Step payload s e s') (tail : Steps payload s' events s'') :
    Steps payload s (e :: events) s''

/-- The call in flight when the process stops: never started, or done with any response. -/
def InFlight (payload : List UInt8) (s : DirState) (request : Request) (s' : DirState) : Prop :=
  s' = s ∨ ∃ response, Step payload s ⟨request, response⟩ s'

/-- The path text `t` holds what it held in `s₀` (absent or old bytes) or the new bytes. -/
def OldOrNew (payload : List UInt8) (s₀ s : DirState) (t : String) : Prop :=
  s.files t = s₀.files t ∨ s.files t = some payload

/-- No call in `events` is a rename. -/
def NoRename (events : Trace) : Prop := ∀ e ∈ events, ∀ src dst, e.request ≠ .rename src dst

def bytesOf (b : List UInt8) : ByteArray := ⟨⟨b⟩⟩

end FvdepAudit.Sys.Spec
