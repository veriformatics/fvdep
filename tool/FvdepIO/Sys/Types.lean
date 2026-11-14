/-! Persistence types (contract `docs/contracts/U3-codecs.md` F2; port of fvapi 02d99d1
`Fvapi.Sys.Fsync.Types`): paths, basenames, modes, errors, and the syscall model the policy is
written against (requests, responses, events). -/

namespace FvdepIO.Sys

/-- F2: a path without NUL (the C shim passes it as a C string). -/
structure Path where
  toString : String
  nulFree : '\x00' ∉ toString.toList

namespace Path

def ofString? (s : String) : Option Path := if h : '\x00' ∉ s.toList then some ⟨s, h⟩ else none

instance : ToString Path := ⟨Path.toString⟩

theorem nulFree_append {a b : String} (ha : '\x00' ∉ a.toList) (hb : '\x00' ∉ b.toList) :
    '\x00' ∉ (a ++ b).toList := by
  simp only [String.toList_append, List.mem_append, not_or]
  exact ⟨ha, hb⟩

theorem nulFree_repr (n : Nat) : '\x00' ∉ n.repr.toList := by
  rw [Nat.toList_repr]
  intro h
  have := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) h
  simp at this

/-- `dir/part`. -/
def child (dir : Path) (part : String) (h : '\x00' ∉ part.toList) : Path :=
  ⟨dir.toString ++ "/" ++ part, nulFree_append (nulFree_append dir.nulFree (by decide)) h⟩

end Path

/-- The writer-lock file's name (F2: never a `replace` target). -/
def lockName : String := ".fvdep-writer.lock"

/-- F2: a basename: nonempty, no NUL or `/`, neither `.` nor `..`, not the writer-lock file. -/
def nameOk (s : String) : Bool :=
  !s.isEmpty && !s.toList.contains '\x00' && !s.toList.contains '/' && s != "." && s != ".." &&
    s != lockName

structure Name where
  toString : String
  ok : nameOk toString = true

namespace Name

def ofString? (s : String) : Option Name := if h : nameOk s = true then some ⟨s, h⟩ else none

instance : ToString Name := ⟨Name.toString⟩

theorem nulFree (n : Name) : '\x00' ∉ n.toString.toList := by
  have := n.ok
  simp only [nameOk, Bool.and_eq_true, Bool.not_eq_true'] at this
  simpa using this.1.1.1.1.2

end Name

/-- `dir/name`. -/
def Path.at (dir : Path) (name : Name) : Path := dir.child name.toString name.nulFree

/-- F2: `replace`'s temp for attempt `n`: `<dir>/.<name>.tmp-<pid>-<n>`. -/
def tempPath (dir : Path) (name : Name) (pid n : Nat) : Path :=
  dir.child ("." ++ name.toString ++ ".tmp-" ++ pid.repr ++ "-" ++ n.repr) <| by
    refine
      Path.nulFree_append
        (Path.nulFree_append
          (Path.nulFree_append
            (Path.nulFree_append (Path.nulFree_append (by decide) name.nulFree) (by decide))
            (Path.nulFree_repr pid))
          (by decide))
        (Path.nulFree_repr n)

/-- F2: the writer lock `<dir>/.fvdep-writer.lock`. -/
def lockPath (dir : Path) : Path := dir.child lockName (by decide)

/-- A permission mode (≤ 0o777). -/
structure Mode where
  toNat : Nat
  bounded : toNat ≤ 511

namespace Mode

def ofNat? (n : Nat) : Option Mode := if h : n ≤ 511 then some ⟨n, h⟩ else none

/-- 0o644. -/
def default : Mode := ⟨420, by decide⟩

instance : Inhabited Mode := ⟨default⟩

end Mode

/-- The step a `SysError` names. -/
inductive Op where
  | create
  | write
  | sync
  | close
  | openDir
  | syncDir
  | closeDir
  | openRead
  | read
  | rename
  | unlink
  | openLock
  | lock
  deriving Repr, DecidableEq

/-- Why a step failed. -/
inductive Cause where
  | errno (number : Nat)
  | retryExhausted
  | noProgress
  | alreadyClosed
  /-- `withWriterLock`: another process holds the lock. -/
  | busy
  /-- `replace`: all 64 temp names exist. -/
  | tempsTaken
  /-- `readFile`: the file holds more than the caller's cap. -/
  | tooLarge
  deriving Repr, DecidableEq

/-- F2: the primary failure + the cleanup failures after it, in order. `durability`: the rename
reported success + a later step of `syncDir` failed, so the target holds the new bytes. -/
structure SysError where
  op : Op
  cause : Cause
  path : Path
  secondary : List (Op × Nat) := []
  durability : Bool := false

namespace Model

/-- A syscall's answer: `.error errno` or `.ok value`. -/
abbrev Response := Except Nat Nat

def eintr : Nat := 4

def eexist : Nat := 17

def enoent : Nat := 2

def ewouldblock : Nat := 11

/-- F3: retries after `EINTR` per step. -/
def retryBudget : Nat := 64

/-- The largest count one `write` asks for. -/
def maxChunk : Nat := 2 ^ 30

/-- The count one `read` asks for (its buffer is allocated per call). -/
def readChunk : Nat := 2 ^ 20

/-- F2: temp-name attempts per `replace`. -/
def tempTries : Nat := 64

/-- F2: `readFile`'s default cap (a cap makes its read loop total). -/
def readCap : Nat := 2 ^ 30

/-- One syscall, as the C shim issues it. -/
inductive Request where
  | create (path : Path) (mode : Mode)
  | openDir (path : Path)
  | write (fd offset count : Nat)
  | fsync (fd : Nat)
  | close (fd : Nat)
  | openRead (path : Path)
  | read (fd count : Nat)
  | rename (source target : Path)
  | unlink (path : Path)
  | openLock (path : Path)
  | lock (fd : Nat)

structure Event where
  request : Request
  response : Response

structure WriterState where
  path : Path
  fd : Nat
  closed : Bool := false

inductive WriterAction where
  | write (size : Nat)
  | sync
  | close
  | finalize
  deriving Repr, DecidableEq

end Model

end FvdepIO.Sys
