import FvdepIO.Sys.Policy

/-! Persistence in `IO` (contract `docs/contracts/U3-codecs.md` F1–F2): the policy over the C shim
`c/fvdep_sys.c` (one libc call per extern; residue `sys-shim`). fvapi 02d99d1's `Writer` +
`syncDir`, + `replace`, `readFile`, `withWriterLock`. -/

namespace FvdepIO.Sys

open Model

namespace Native

opaque WriterImpl : NonemptyType.{0}

abbrev Writer := WriterImpl.type

@[extern "fvdep_sys_open_file"]
opaque openFile (path : @& String) (mode : UInt32) : IO Response

@[extern "fvdep_sys_open_dir"]
opaque openDir (path : @& String) : IO Response

@[extern "fvdep_sys_open_read"]
opaque openRead (path : @& String) : IO Response

@[extern "fvdep_sys_open_lock"]
opaque openLock (path : @& String) : IO Response

@[extern "fvdep_sys_write"]
opaque write (fd : UInt32) (bytes : @& ByteArray) (offset count : USize) : IO Response

@[extern "fvdep_sys_read"]
opaque read (fd : UInt32) (count : USize) : IO (Except Nat ByteArray)

@[extern "fvdep_sys_sync"]
opaque sync (fd : UInt32) : IO Response

@[extern "fvdep_sys_close"]
opaque close (fd : UInt32) : IO Response

@[extern "fvdep_sys_rename"]
opaque rename (source target : @& String) : IO Response

@[extern "fvdep_sys_unlink"]
opaque unlink (path : @& String) : IO Response

@[extern "fvdep_sys_lock"]
opaque lock (fd : UInt32) : IO Response

@[extern "fvdep_sys_writer_new"]
opaque writerNew (fd : UInt32) (path : @& String) : IO Writer

@[extern "fvdep_sys_writer_acquire"]
opaque writerAcquire (writer : @& Writer) : IO (Nat × Bool)

@[extern "fvdep_sys_writer_mark_closed"]
opaque writerMarkClosed (writer : @& Writer) : IO Unit

@[extern "fvdep_sys_writer_release"]
opaque writerRelease (writer : @& Writer) : IO Unit

end Native

/-- The policy's syscalls over the shim: `write` sends from `bytes`, `read` appends to `buffer`,
a guarded writer is marked closed before its one close attempt. -/
def syscalls (bytes : ByteArray) (buffer : IO.Ref ByteArray) (owned : Option Native.Writer) :
    Policy.Interface IO :=
  ⟨fun
    | .create path mode => Native.openFile path.toString mode.toNat.toUInt32
    | .openDir path => Native.openDir path.toString
    | .write fd offset count => Native.write fd.toUInt32 bytes offset.toUSize count.toUSize
    | .fsync fd => Native.sync fd.toUInt32
    | .close fd => do
      if let some w := owned then
        Native.writerMarkClosed w
      Native.close fd.toUInt32
    | .openRead path => Native.openRead path.toString
    | .read fd count => do
      match ← Native.read fd.toUInt32 count.toUSize with
      | .error n =>
        return .error n
      | .ok chunk =>
        buffer.modify (· ++ chunk)
        return .ok chunk.size
    | .rename source target => Native.rename source.toString target.toString
    | .unlink path => Native.unlink path.toString
    | .openLock path => Native.openLock path.toString
    | .lock fd => Native.lock fd.toUInt32⟩

def plain (bytes : ByteArray := .empty) : IO (Policy.Interface IO) := do
  return syscalls bytes (← IO.mkRef .empty) none

/-- One create-owned description (fvapi): the native guard carries the descriptor + the closed
flag; copies share it; the finalizer closes it if still open. -/
structure Writer where private mk ::
  private native : Native.Writer
  path : Path

namespace Writer

def create (path : Path) (mode : Mode := Mode.default) : IO (Except SysError Writer) := do
  match ← Policy.create (← plain) path mode with
  | .error e =>
    return .error e
  | .ok fd =>
    return .ok ⟨← Native.writerNew fd.toUInt32 path.toString, path⟩

private def run (writer : Writer) (action : WriterAction) (bytes : ByteArray := .empty) :
    IO (Except SysError Unit) := do
  let (fd, closed) ← Native.writerAcquire writer.native
  try
    let sys := syscalls bytes (← IO.mkRef .empty) (some writer.native)
    return (← Policy.writer sys ⟨writer.path, fd, closed⟩ action).map fun _ => ()
  finally
    Native.writerRelease writer.native

def write (writer : Writer) (bytes : ByteArray) : IO (Except SysError Unit) :=
  run writer (.write bytes.size) bytes

def sync (writer : Writer) : IO (Except SysError Unit) := run writer .sync

/-- Marked closed before its single close attempt (`EINTR` included). -/
def close (writer : Writer) : IO (Except SysError Unit) := run writer .close

end Writer

def syncDir (path : Path) : IO (Except SysError Unit) := do
  return (← Policy.directory (← plain) path).map fun _ => ()

/-- F2: replace `dir/name` by `bytes` durably (temp, write, fsync, close, rename, `syncDir`). -/
def replace (dir : Path) (name : Name) (bytes : ByteArray) : IO (Except SysError Unit) := do
  Policy.replace (← plain bytes) dir name (← IO.Process.getPID).toNat bytes.size

/-- F2: `dir/name`'s bytes, `none` when absent. -/
def readFile (dir : Path) (name : Name) (cap : Nat := readCap) :
    IO (Except SysError (Option ByteArray)) := do
  let buffer ← IO.mkRef ByteArray.empty
  match ← Policy.readFile (syscalls .empty buffer none) (dir.at name) cap with
  | .error e =>
    return .error e
  | .ok none =>
    return .ok none
  | .ok (some _) =>
    return .ok (some (← buffer.get))

/-- F2: run `act` holding `<dir>/.fvdep-writer.lock` (`busy` when another process holds it); an
exception of `act` propagates after the close. -/
def withWriterLock {α : Type} (dir : Path) (act : IO α) : IO (Except SysError α) := do
  match ← Policy.withLock (← plain) dir act.toBaseIO with
  | .error e =>
    return .error e
  | .ok (.ok a) =>
    return .ok a
  | .ok (.error ex) =>
    throw ex

end FvdepIO.Sys
