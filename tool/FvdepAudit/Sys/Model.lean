import FvdepIO.Sys.Policy

/-! The syscall-script interpretation of the persistence policy (fvapi 02d99d1): a script answers
the n-th syscall; a run records every call + its answer. Proofs run the shipped policy over it. -/

namespace FvdepIO.Sys.Model

/-- One scripted run of a policy operation: its result, every call + answer, the calls consumed. -/
structure Execution where
  result : Except SysError Nat
  events : List Event
  consumed : Nat

end FvdepIO.Sys.Model

namespace FvdepIO.Sys.Policy

open Model

abbrev Script := Nat → Response

structure Recorded (α : Type) where
  result : α
  events : List Event := []
  consumed : Nat := 0

structure ScriptIO (α : Type) where
  run : Script → Recorded α

namespace ScriptIO

variable {α β : Type}

def pure (a : α) : ScriptIO α := ⟨fun _ => ⟨a, [], 0⟩⟩

def bind (a : ScriptIO α) (f : α → ScriptIO β) : ScriptIO β :=
  ⟨fun script =>
    let first := a.run script
    let rest := (f first.result).run (fun n => script (n + first.consumed))
    ⟨rest.result, first.events ++ rest.events, first.consumed + rest.consumed⟩⟩

instance : Monad ScriptIO where
  pure := pure
  bind := bind

end ScriptIO

def scripted : Interface ScriptIO :=
  ⟨fun request => ⟨fun script => ⟨script 0, [⟨request, script 0⟩], 1⟩⟩⟩

def asExecution (record : Recorded (Except SysError Nat)) : Execution :=
  ⟨record.result, record.events, record.consumed⟩

def scriptCreate (path : Path) (mode : Mode) (script : Script) : Execution :=
  asExecution ((create scripted path mode).run script)

def scriptWriter (owned : WriterState) (action : WriterAction) (script : Script) : Execution :=
  asExecution ((writer scripted owned action).run script)

def scriptDirectory (path : Path) (script : Script) : Execution :=
  asExecution ((directory scripted path).run script)

def scriptActions (owned : WriterState) (as : List WriterAction) (script : Script) :
    Recorded (List (Except SysError Nat)) := (actions scripted owned as).run script

def scriptReplace (dir : Path) (name : Name) (pid size : Nat) (script : Script) :
    Recorded (Except SysError Unit) := (replace scripted dir name pid size).run script

def scriptReadFile (path : Path) (cap : Nat) (script : Script) :
    Recorded (Except SysError (Option Nat)) := (readFile scripted path cap).run script

def scriptLock {α : Type} (dir : Path) (act : ScriptIO α) (script : Script) :
    Recorded (Except SysError α) := (withLock scripted dir act).run script

end FvdepIO.Sys.Policy
