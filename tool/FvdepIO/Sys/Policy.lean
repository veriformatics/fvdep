import FvdepIO.Sys.Types

/-! The persistence policy (contract `docs/contracts/U3-codecs.md` F2–F3; fvapi 02d99d1
`Fvapi.Sys.Fsync.Policy` + `replace`, `readFile`, `withWriterLock`): written against a syscall
interface, so the native implementation and the syscall-script model run the same code. Only the
syscalls + the writer guard cross the FFI. -/

namespace FvdepIO.Sys.Policy

open Model

structure Interface (m : Type → Type) where
  call : Request → m Response

def error (op : Op) (path : Path) (cause : Cause) : SysError := { op, cause, path }

def unitResult (op : Op) (path : Path) : Except Cause Nat → Except SysError Nat
  | .ok _ => .ok 0
  | .error cause => .error (error op path cause)

def writeResult (path : Path) : Except Cause Unit → Except SysError Nat
  | .ok _ => .ok 0
  | .error cause => .error (error .write path cause)

def closeResult (op : Op) (path : Path) : Response → Except SysError Nat
  | .ok _ => .ok 0
  | .error n => .error (error op path (.errno n))

/-- F3: one step; `budget` counts retries after the first attempt (`EINTR` alone retries). -/
def retry {m : Type → Type} [Monad m] (sys : Interface m) (request : Request) :
    Nat → m (Except Cause Nat)
  | 0 => do
    match ← sys.call request with
    | .ok n =>
      return .ok n
    | .error n =>
      return .error (if n = eintr then .retryExhausted else .errno n)
  | budget + 1 => do
    match ← sys.call request with
    | .ok n =>
      return .ok n
    | .error n =>
      if n = eintr then
        retry sys request budget
      else
        return .error (.errno n)

/-- F3: write `remaining` bytes from `offset`; each positive acknowledgement starts a fresh step;
a 0-byte write → `noProgress`; an over-report (more than asked) fails closed. -/
def writes {m : Type → Type} [Monad m] (sys : Interface m) (fd offset remaining : Nat) :
    m (Except Cause Unit) := do
  if remaining = 0 then
    return .ok ()
  let count := min remaining maxChunk
  match ← retry sys (.write fd offset count) retryBudget with
  | .error cause =>
    return .error cause
  | .ok 0 =>
    return .error .noProgress
  | .ok (n + 1) =>
    if n + 1 ≤ count then
      writes sys fd (offset + (n + 1)) (remaining - (n + 1))
    else
      return .error (.errno 5)
termination_by remaining
decreasing_by omega

def create {m : Type → Type} [Monad m] (sys : Interface m) (path : Path) (mode : Mode) :
    m (Except SysError Nat) := do
  match ← retry sys (.create path mode) retryBudget with
  | .ok fd =>
    return .ok fd
  | .error cause =>
    return .error (error .create path cause)

def after (writer : WriterState) : WriterAction → WriterState
  | .close | .finalize => { writer with closed := true }
  | _ => writer

def actionOp : WriterAction → Op
  | .write _ => .write
  | .sync => .sync
  | .close | .finalize => .close

def writer {m : Type → Type} [Monad m] (sys : Interface m) (owned : WriterState)
    (action : WriterAction) : m (Except SysError Nat) :=
  if owned.closed then
    if action = .finalize then pure (.ok 0)
    else pure (.error (error (actionOp action) owned.path .alreadyClosed))
  else
    match action with
    | .write size => do
      return writeResult owned.path (← writes sys owned.fd 0 size)
    | .sync => do
      return unitResult .sync owned.path (← retry sys (.fsync owned.fd) retryBudget)
    | .close => do
      return closeResult .close owned.path (← sys.call (.close owned.fd))
    | .finalize => do
      let _ ← sys.call (.close owned.fd)
      return .ok 0

def directoryResult (path : Path) (primary : Except Cause Nat) (closed : Response) :
    Except SysError Nat :=
  match primary, closed with
  | .ok _, r => closeResult .closeDir path r
  | .error cause, .ok _ => .error (error .syncDir path cause)
  | .error cause, .error n =>
    .error { error .syncDir path cause with secondary := [(.closeDir, n)] }

def directory {m : Type → Type} [Monad m] (sys : Interface m) (path : Path) :
    m (Except SysError Nat) := do
  match ← retry sys (.openDir path) retryBudget with
  | .error cause =>
    return .error (error .openDir path cause)
  | .ok fd =>
    let primary ← retry sys (.fsync fd) retryBudget
    let closed ← sys.call (.close fd)
    return directoryResult path primary closed

def actions {m : Type → Type} [Monad m] (sys : Interface m) (owned : WriterState) :
    List WriterAction → m (List (Except SysError Nat))
  | [] => pure []
  | action :: rest => do
    let result ← writer sys owned action
    let results ← actions sys (after owned action) rest
    return result :: results

/-! ## `readFile` (F2) -/

/-- F3: read until a 0-byte read; each positive read starts a fresh step; `cap` = the bytes still
allowed (one more → `tooLarge`). The bytes themselves go to the interface's buffer; this counts
them. -/
def reads {m : Type → Type} [Monad m] (sys : Interface m) (fd total cap : Nat) :
    m (Except Cause Nat) := do
  let count := min (cap + 1) readChunk
  match ← retry sys (.read fd count) retryBudget with
  | .error cause =>
    return .error cause
  | .ok 0 =>
    return .ok total
  | .ok (n + 1) =>
    if n + 1 ≤ count then
      if h : n + 1 ≤ cap then
        reads sys fd (total + (n + 1)) (cap - (n + 1))
      else
        return .error .tooLarge
    else
      return .error (.errno 5)
termination_by cap
decreasing_by omega

/-- `readFile`'s result from the reads + the close: a failed close after good reads = the error; a
read failure keeps a failed close as its secondary cause. -/
def readOutcome (path : Path) : Except Cause Nat → Response → Except SysError (Option Nat)
  | .ok n, .ok _ => .ok (some n)
  | .ok _, .error e => .error (error .close path (.errno e))
  | .error cause, .ok _ => .error (error .read path cause)
  | .error cause, .error e => .error { error .read path cause with secondary := [(.close, e)] }

/-- F2: open, read until 0 (at most `cap` bytes; one more → `tooLarge`), close; ENOENT → `none`. -/
def readFile {m : Type → Type} [Monad m] (sys : Interface m) (path : Path) (cap : Nat) :
    m (Except SysError (Option Nat)) := do
  match ← retry sys (.openRead path) retryBudget with
  | .error cause =>
    if cause = .errno enoent then
      return .ok none
    else
      return .error (error .openRead path cause)
  | .ok fd =>
    let r ← reads sys fd 0 cap
    let closed ← sys.call (.close fd)
    return readOutcome path r closed

/-! ## `replace` (F2) -/

/-- The secondary cause a failed cleanup step records (its errno; `EINTR` past the budget). -/
def causeErrno : Cause → Nat
  | .errno n => n
  | _ => eintr

/-- F2: create the first free temp (attempt `n` on); EEXIST → the next one; 64 taken →
`tempsTaken`. -/
def createTemp {m : Type → Type} [Monad m] (sys : Interface m) (dir : Path) (name : Name)
    (pid : Nat) : Nat → m (Except SysError (Path × Nat))
  | n =>
    if h : n < tempTries then do
      let temp := tempPath dir name pid n
      match ← retry sys (.create temp Mode.default) retryBudget with
      | .ok fd =>
        return .ok (temp, fd)
      | .error cause =>
        if cause = .errno eexist then
          createTemp sys dir name pid (n + 1)
        else
          return .error (error .create temp cause)
    else return .error (error .create (tempPath dir name pid (tempTries - 1)) .tempsTaken)
termination_by n => tempTries - n

/-- F2 cleanup: unlink the temp this call created (one F3 step); a failure joins the causes. -/
def dropTemp {m : Type → Type} [Monad m] (sys : Interface m) (temp : Path) (e : SysError) :
    m SysError := do
  match ← retry sys (.unlink temp) retryBudget with
  | .ok _ =>
    return e
  | .error cause =>
    return { e with secondary := e.secondary ++ [(.unlink, causeErrno cause)] }

/-- F2 cleanup while the temp is open: close it once, then unlink it. -/
def abandon {m : Type → Type} [Monad m] (sys : Interface m) (temp : Path) (fd : Nat)
    (e : SysError) : m SysError := do
  let e' :=
    match ← sys.call (.close fd) with
    | .ok _ => e
    | .error n => { e with secondary := e.secondary ++ [(.close, n)] }
  dropTemp sys temp e'

/-- F2 after the temp's close: rename it over `dir/name`, then `syncDir dir`; a failed rename
unlinks the temp; a failure after the rename = `durability` (the target holds the new bytes). -/
def commit {m : Type → Type} [Monad m] (sys : Interface m) (dir : Path) (name : Name)
    (temp : Path) : m (Except SysError Unit) := do
  let target := dir.at name
  match ← retry sys (.rename temp target) retryBudget with
  | .error cause =>
    return .error (← dropTemp sys temp (error .rename target cause))
  | .ok _ =>
    match ← directory sys dir with
    | .error e =>
      return .error { e with durability := true }
    | .ok _ =>
      return .ok ()

/-- F2 from the open temp: write all `size` bytes → fsync → close → `commit`; a write or sync
failure closes the temp once, then unlinks it; a failed close unlinks it. -/
def body {m : Type → Type} [Monad m] (sys : Interface m) (dir : Path) (name : Name) (size : Nat)
    (temp : Path) (fd : Nat) : m (Except SysError Unit) := do
  match ← writes sys fd 0 size with
  | .error cause =>
    return .error (← abandon sys temp fd (error .write temp cause))
  | .ok () =>
    match ← retry sys (.fsync fd) retryBudget with
    | .error cause =>
      return .error (← abandon sys temp fd (error .sync temp cause))
    | .ok _ =>
      match ← sys.call (.close fd) with
      | .error n =>
        return .error (← dropTemp sys temp (error .close temp (.errno n)))
      | .ok _ =>
        commit sys dir name temp

/-- F2: temp (create-exclusive) → `body` (write all `size` bytes, fsync, close, rename over
`dir/name`, `syncDir dir`). -/
def replace {m : Type → Type} [Monad m] (sys : Interface m) (dir : Path) (name : Name)
    (pid size : Nat) : m (Except SysError Unit) := do
  match ← createTemp sys dir name pid 0 with
  | .error e =>
    return .error e
  | .ok (temp, fd) =>
    body sys dir name size temp fd

/-! ## `withWriterLock` (F2) -/

/-- The lock's refusal: EWOULDBLOCK → `busy`; a failed close follows as the secondary cause. -/
def lockRefusal (path : Path) (cause : Cause) : Response → SysError
  | .ok _ => error .lock path (if cause = .errno ewouldblock then .busy else cause)
  | .error n =>
    { error .lock path (if cause = .errno ewouldblock then .busy else cause) with
      secondary := [(.close, n)] }

/-- F2: open (creating) + `flock` `<dir>/.fvdep-writer.lock`, run `act`, close; EWOULDBLOCK →
`busy`; any failure before `act` runs nothing + closes what it opened. A failed close after `act`
keeps `act`'s result (the close released the lock). -/
def withLock {m : Type → Type} [Monad m] {α : Type} (sys : Interface m) (dir : Path) (act : m α) :
    m (Except SysError α) := do
  let path := lockPath dir
  match ← retry sys (.openLock path) retryBudget with
  | .error cause =>
    return .error (error .openLock path cause)
  | .ok fd =>
    match ← retry sys (.lock fd) retryBudget with
    | .error cause =>
      let closed ← sys.call (.close fd)
      return .error (lockRefusal path cause closed)
    | .ok _ =>
      let a ← act
      let _ ← sys.call (.close fd)
      return .ok a

end FvdepIO.Sys.Policy
