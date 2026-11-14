import FvdepIO.Sys
import Lean.Data.Json

namespace SysExtra

open FvdepIO.Sys Lean

abbrev J := Lean.Json

def obj := Lean.Json.mkObj

def fixture {α : Type} : Except String α → IO α
  | .ok x => pure x
  | .error e => throw (IO.userError e)

def field (j : J) (key : String) : IO J := fixture (j.getObjVal? key)

def string (j : J) (key : String) : IO String := field j key >>= fun v => fixture v.getStr?

def path (j : J) (key : String) : IO FvdepIO.Sys.Path := do
  let s ← string j key
  let some p := FvdepIO.Sys.Path.ofString? s | throw (IO.userError "fixture path")
  return p

def name (j : J) : IO FvdepIO.Sys.Name := do
  let s ← string j "name"
  let some n := FvdepIO.Sys.Name.ofString? s | throw (IO.userError "fixture name")
  return n

def cause : Cause → String
  | .errno _ => "errno"
  | .retryExhausted => "retryExhausted"
  | .noProgress => "noProgress"
  | .alreadyClosed => "alreadyClosed"
  | .busy => "busy"
  | .tempsTaken => "tempsTaken"
  | .tooLarge => "tooLarge"

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

def error (e : SysError) : J := obj [
  ("op", .str (opName e.op)),
  ("cause", .str (cause e.cause)), ("path", .str e.path.toString),
  ("secondary", .arr (e.secondary.map fun (o, n) => obj [
    ("op", .str (opName o)), ("errno", toJson n)]).toArray),
  ("errno", match e.cause with | .errno n => toJson n | _ => .null),
  ("durability", .bool e.durability)]

def unitResult (op : String) : Except SysError Unit → J
  | .ok _ => obj [("op", .str op), ("ok", .bool true)]
  | .error e => obj [("op", .str op), ("ok", .bool false), ("error", error e)]

def bytes : ByteArray := ⟨(Array.range 256).map UInt8.ofNat⟩

def run (j : J) : IO J := do
  match ← string j "op" with
  | "types" =>
    let p ← string j "path"
    let n ← string j "name"
    let m ← fixture ((← field j "mode").getNat?)
    return obj [
      ("path", .bool (FvdepIO.Sys.Path.ofString? p).isSome),
      ("name", .bool (FvdepIO.Sys.Name.ofString? n).isSome),
      ("mode", .bool (Mode.ofNat? m).isSome),
      ("path_value", match FvdepIO.Sys.Path.ofString? p with
        | some x => .str x.toString | none => .null),
      ("name_value", match FvdepIO.Sys.Name.ofString? n with
        | some x => .str x.toString | none => .null)]
  | "read-size" =>
    match ← readFile (← path j "dir") (← name j) with
    | .error e => return obj [("ok", .bool false), ("error", error e)]
    | .ok none => return obj [("ok", .bool true), ("size", .null)]
    | .ok (some b) =>
      let indices := if b.isEmpty then #[] else #[0, b.size / 2, b.size - 1]
      let samples := indices.map fun i => obj [("at", toJson i), ("value", toJson b[i]!.toNat)]
      return obj [("ok", .bool true), ("size", toJson b.size), ("samples", .arr samples)]
  | "lock-count" =>
    let count ← IO.mkRef 0
    let result ← withWriterLock (← path j "dir") do
      count.modify (· + 1)
      return 37
    return obj [("count", toJson (← count.get)),
      ("result", match result with
        | .ok n => obj [("ok", .bool true), ("value", toJson n)]
        | .error e => obj [("ok", .bool false), ("error", error e)])]
  | "lock-throw" =>
    let count ← IO.mkRef 0
    let result ← try
      let r ← withWriterLock (← path j "dir") (do
        count.modify (· + 1)
        throw (IO.userError "F6-sentinel") : IO Unit)
      pure (obj [("threw", .bool false), ("result", match r with
        | .ok _ => .null | .error e => error e)])
      catch e => pure (obj [("threw", .bool true), ("message", .str e.toString)])
    return obj [("count", toJson (← count.get)), ("result", result)]
  | "writer-race" =>
    match ← Writer.create (← path j "path") with
    | .error e => return obj [("created", .bool false), ("error", error e)]
    | .ok w =>
      let go ← IO.mkRef false
      let mut tasks := #[]
      for i in List.range 16 do
        let task ← IO.asTask do
          while !(← go.get) do IO.sleep 1
          if i % 4 == 0 then IO.sleep 1
          let wrote ← Writer.write w bytes
          let synced ← Writer.sync w
          return (unitResult "write" wrote, unitResult "sync" synced)
        tasks := tasks.push task
      let closer ← IO.asTask do
        while !(← go.get) do IO.sleep 1
        Writer.close w
      go.set true
      let mut results := #[]
      for task in tasks do
        match task.get with
        | .error e => throw e
        | .ok (a, b) => results := results ++ #[a, b]
      let closed ← match closer.get with
        | .error e => throw e
        | .ok r => pure r
      let again ← Writer.close w
      return obj [("created", .bool true), ("records", .arr results),
        ("close", unitResult "close" closed), ("again", unitResult "close" again)]
  | _ => throw (IO.userError "fixture operation")

end SysExtra

def main : IO UInt32 := do
  try
    let input ← (← IO.getStdin).getLine
    let j ← SysExtra.fixture (Lean.Json.parse input)
    let result ← SysExtra.run j
    (← IO.getStdout).putStrLn result.compress
    return 0
  catch e =>
    (← IO.getStderr).putStrLn e.toString
    return 2
