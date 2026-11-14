import FvdepCore.Hash.Frame
import FvdepCore.Json
import FvdepIO.Sys

/-! Dev driver for the persistence API (contract `docs/contracts/U3-codecs.md` F6; fvapi 02d99d1
`Fvapi.Sys.Fsync.Dev` + `replace`, `read`, `lock`, `unlock`, `wait`): `fvdep-dev sys run OP…`, one
canonical JSON record per op on stdout (`Value.object`: keys in byte order). Never shipped
(lean_lib `FvdepDev`). -/

namespace FvdepDev.Sys

open FvdepCore.Json FvdepIO.Sys

inductive Command where
  | create (path : Path) (mode : Mode)
  | write (size : Nat)
  | sync
  | close
  | drop
  | syncDir (path : Path)
  | replace (dir : Path) (name : Name) (size : Nat)
  | read (dir : Path) (name : Name)
  | lock (dir : Path)
  | unlock
  | wait

def usage : String :=
  "usage: fvdep-dev sys run OP…\n" ++
    "ops: create PATH [MODE], write N, sync, close, drop, syncdir PATH, replace DIR NAME N,\n" ++
    "     read DIR NAME, lock DIR … unlock (the ops between run under the lock), wait\n"

def operation (s : String) : Bool :=
  ["create", "write", "sync", "close", "drop", "syncdir", "replace", "read", "lock", "unlock",
        "wait"].contains
    s

/-- An octal mode of 1–3 digits. -/
def mode? (s : String) : Option Mode := do
  let cs := s.toList
  unless 1 ≤ cs.length && cs.length ≤ 3 && cs.all (fun c => '0' ≤ c && c ≤ '7') do
    none
  Mode.ofNat? (cs.foldl (fun n c => n * 8 + (c.toNat - '0'.toNat)) 0)

/-- A decimal count. -/
def count? (s : String) : Option Nat := do
  unless !s.isEmpty && s.toList.all (fun c => '0' ≤ c && c ≤ '9') do
    none
  s.toNat?

def parse : List String → Option (List Command)
  | [] => some []
  | "create" :: path :: rest => do
    let path ← Path.ofString? path
    match rest with
    | m :: more =>
      if operation m then
        return .create path Mode.default :: (← parse (m :: more))
      else
        return .create path (← mode? m) :: (← parse more)
    | [] =>
      return [.create path Mode.default]
  | "write" :: n :: rest => do
    return .write (← count? n) :: (← parse rest)
  | "sync" :: rest => do
    return .sync :: (← parse rest)
  | "close" :: rest => do
    return .close :: (← parse rest)
  | "drop" :: rest => do
    return .drop :: (← parse rest)
  | "syncdir" :: path :: rest => do
    return .syncDir (← Path.ofString? path) :: (← parse rest)
  | "replace" :: dir :: name :: n :: rest => do
    return .replace (← Path.ofString? dir) (← Name.ofString? name) (← count? n) :: (← parse rest)
  | "read" :: dir :: name :: rest => do
    return .read (← Path.ofString? dir) (← Name.ofString? name) :: (← parse rest)
  | "lock" :: dir :: rest => do
    return .lock (← Path.ofString? dir) :: (← parse rest)
  | "unlock" :: rest => do
    return .unlock :: (← parse rest)
  | "wait" :: rest => do
    return .wait :: (← parse rest)
  | _ => none

def opName : Op → String
  | .create => "create"
  | .write => "write"
  | .sync => "sync"
  | .close => "close"
  | .openDir => "openDir"
  | .syncDir => "syncDir"
  | .closeDir => "closeDir"
  | .openRead => "openRead"
  | .read => "read"
  | .rename => "rename"
  | .unlink => "unlink"
  | .openLock => "openLock"
  | .lock => "lock"

def causeName : Cause → String
  | .errno _ => "errno"
  | .retryExhausted => "retryExhausted"
  | .noProgress => "noProgress"
  | .alreadyClosed => "alreadyClosed"
  | .busy => "busy"
  | .tempsTaken => "tempsTaken"
  | .tooLarge => "tooLarge"

/-- One secondary cause: the cleanup op + its errno. -/
def secondaryJson (s : Op × Nat) : Value := .object [("op", .str (opName s.1)), ("errno", .int s.2)]

def errorJson (e : SysError) : Value :=
  .object <|
    [("op", .str (opName e.op)), ("cause", .str (causeName e.cause)),
        ("path", .str e.path.toString)] ++
      (match e.cause with
      | .errno n => [("errno", .int n)]
      | _ => []) ++
      (if e.secondary.isEmpty then [] else [("secondary", .arr (e.secondary.map secondaryJson))]) ++
      if e.durability then [("durability", .bool true)] else []

def emit (record : Value) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn (String.fromUTF8! (print record))
  out.flush

def report (op : String) (result : Except SysError Unit) (extra : List (String × Value) := []) :
    IO Unit :=
  emit <|
    match result with
    | .ok _ => .object ([("op", .str op), ("ok", .bool true)] ++ extra)
    | .error e => .object [("op", .str op), ("ok", .bool false), ("error", errorJson e)]

/-- Exactly `n` bytes from stdin, `none` at an early end. -/
def readExactly (n : Nat) : IO (Option ByteArray) := do
  let stdin ← IO.getStdin
  let mut bytes := ByteArray.empty
  while bytes.size < n do
    let part ← stdin.read (min (n - bytes.size) 65536).toUSize
    if part.isEmpty then
      return none
    bytes := bytes ++ part
  return some bytes

/-- The ops up to the matching `unlock` (exclusive) + the ops after it. -/
def untilUnlock : List Command → List Command × List Command
  | [] => ([], [])
  | .unlock :: rest => ([], rest)
  | c :: rest =>
    let (inside, after) := untilUnlock rest
    (c :: inside, after)

/-- Run the ops in order; `lock DIR` runs the ops up to its `unlock` (or the end) inside
`withWriterLock` (the lock is held exactly while they run); a refused lock skips them + their
`unlock`. `none` = completed, `some rc` = a usage stop. -/
partial def steps (slot : IO.Ref (Option Writer)) (locked : Bool) :
    List Command → IO (Option UInt32)
  | [] => return none
  | command :: rest => do
    let usageStop : IO (Option UInt32) := do
      IO.eprint usage
      return some 2
    match command with
    | .create path mode =>
      if (← slot.get).isSome then
        return ← usageStop
      match ← Writer.create path mode with
      | .error e =>
        report "create" (.error e)
      | .ok w =>
        slot.set (some w)
        report "create" (.ok ())
      steps slot locked rest
    | .write n =>
      let some w ← slot.get | usageStop
      let some bytes ← readExactly n | usageStop
      report "write" (← w.write bytes)
      steps slot locked rest
    | .sync =>
      let some w ← slot.get | usageStop
      report "sync" (← w.sync)
      steps slot locked rest
    | .close =>
      let some w ← slot.get | usageStop
      report "close" (← w.close)
      steps slot locked rest
    | .drop =>
      if (← slot.get).isNone then
        return ← usageStop
      slot.set none
      report "drop" (.ok ())
      steps slot locked rest
    | .syncDir path =>
      report "syncdir" (← syncDir path)
      steps slot locked rest
    | .replace dir name n =>
      let some bytes ← readExactly n | usageStop
      report "replace" (← replace dir name bytes)
      steps slot locked rest
    | .read dir name =>
      match ← readFile dir name with
      | .error e =>
        report "read" (.error e)
      | .ok none =>
        report "read" (.ok ()) [("bytes", .null)]
      | .ok (some b) =>
        report "read" (.ok ()) [("bytes", .str (FvdepCore.Hash.hex b))]
      steps slot locked rest
    | .lock dir =>
      if locked then
        return ← usageStop
      let (inside, after) := untilUnlock rest
      let r ←
        withWriterLock dir do
            report "lock" (.ok ())
            steps slot true inside
      match r with
      | .error e =>
        report "lock" (.error e)
      | .ok (some rc) =>
        return some rc
      | .ok none =>
        report "unlock" (.ok ())
      steps slot locked after
    | .unlock =>
      usageStop
    | .wait =>
      let _ ← (← IO.getStdin).getLine
      report "wait" (.ok ())
      steps slot locked rest

def run (args : List String) : IO UInt32 := do
  let some commands := parse args |
    IO.eprint usage;
    return 2
  if commands.isEmpty then
    IO.eprint usage
    return 2
  return (← steps (← IO.mkRef none) false commands).getD 0

end FvdepDev.Sys
