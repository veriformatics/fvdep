import FvdepCore.Doc

/-! J5 resources (contract `docs/contracts/U3-codecs.md` "Resources (J5)"): `fvdep-dev json measure
FAMILY N TASKS [CYCLES]` = one measurement per process (`VmHWM` = this run's peak) of a generated
input at size `N` through the compiled codec — `decode` in `TASKS` dedicated Tasks (each decodes
its own copy; `TASKS` = 0: on the calling thread, the CLI's path), `print`, result release, `CYCLES`
times; family `object` = `Value.object` over `N`
members in reverse key order; family `lock` = `decodeLock` of `N` receipts, `Lock.normalize` of
them reversed, `encodeLock`. One TSV row per cycle (`tools/json-resources.sh`). Recorded, not
promised; never shipped. -/

namespace FvdepDev.Resources

open FvdepCore.Json FvdepCore.Doc FvdepCore.Status

/-- `VmRSS` + `VmHWM` of this process, kB (`/proc/self/status` lines `Name:\t   N kB`). -/
def memory : IO (Nat × Nat) := do
  let lines := (← IO.FS.readFile "/proc/self/status").splitOn "\n"
  let field (name : String) : Nat :=
    match lines.find? (·.startsWith name) with
    | some line => (String.ofList (line.toList.filter Char.isDigit)).toNat?.getD 0
    | none => 0
  return (field "VmRSS:", field "VmHWM:")

/-- User + system CPU of every thread so far, clock ticks (`/proc/self/stat` fields 14 + 15, counted
after the parenthesized command name). -/
def cpuTicks : IO Nat := do
  let stat ← IO.FS.readFile "/proc/self/stat"
  let fields := ((stat.splitOn ") ").getLast?.getD "").splitOn " "
  let field (i : Nat) : Nat := (fields.getD i "0").toNat?.getD 0
  return field 11 + field 12

/-- `n` copies of `s` after `out`. -/
def rep (out : ByteArray) (s : String) (n : Nat) : ByteArray :=
  Id.run do
    let piece := s.toUTF8
    let mut b := out
    for _ in [0:n] do
      b := b.append piece
    return b

/-- `i` as 7 decimal digits. -/
def pad7 (i : Nat) : String :=
  let s := toString i
  "".pushn '0' (7 - s.length) ++ s

/-- `{"<pre><pad7 (order i)>":0,…}` over `i < m`. -/
def keysText (pre : String) (m : Nat) (order : Nat → Nat) : ByteArray :=
  Id.run do
    let mut b := "{".toUTF8
    for i in [0:m] do
      if i > 0 then
        b := b.append ",".toUTF8
      b := b.append ("\"" ++ pre ++ pad7 (order i) ++ "\":0").toUTF8
    return b.append "}".toUTF8

def library : String := "0123456789abcdef0123456789abcdef01234567"

/-- The codec suite's default proof receipt (`tests/codec/doc_oracle.py`) for module `p<i>.op`. -/
def receiptText (i : Nat) : String :=
  "{\"checked\":\"2026-02-31T23:59:60Z\",\"digests\":{\"adapter\":null,\"impl_sources\":\"" ++
    "".pushn 'b' 64 ++
    "\",\"phase1_export\":\"" ++
    "".pushn 'd' 64 ++
    "\",\"proof_sources\":\"" ++
    "".pushn 'c' 64 ++
    "\",\"solution_export\":\"" ++
    "".pushn 'e' 64 ++
    "\",\"spec_closure\":\"" ++
    "".pushn 'a' 64 ++
    "\"},\"evidence\":\"proof\",\"library\":\"" ++
    library ++
    "\",\"policy\":\"required\"," ++
    "\"request\":{\"adapter\":null,\"impl\":\"Impl.encode\",\"module\":\"p" ++
    pad7 i ++
    ".op\",\"proof\":\"Proof.encode_eq\",\"shape\":\"fn\",\"version\":\"1.0.0\"}," ++
    "\"verification_profile\":\"lean4.35@v1+qualified\"}"

/-- A lock of `m` receipts in ascending module order (D4). -/
def lockText (m : Nat) : ByteArray :=
  Id.run do
    let mut b := ("{\"library\":\"" ++ library ++ "\",\"modules\":[").toUTF8
    for i in [0:m] do
      if i > 0 then
        b := b.append ",".toUTF8
      b := b.append (receiptText i).toUTF8
    return b.append "],\"schema\":1}".toUTF8

/-- The input family at size `n`: an unclosed nesting (`deep`), a digit run, an over-cap string
whose suffix is malformed (`string`; multibyte `string-mb`; escapes `string-esc`), a flat array
of zeros or of 16-digit integers (`ints`: the digit loop runs per digit),
an object with sorted, reverse or shuffled 64-byte-common-prefix keys. -/
def generate (family : String) (n : Nat) : Option ByteArray :=
  match family with
  | "deep" => some (rep .empty "[" n)
  | "digits" => some (rep .empty "1" n)
  | "string" => some (rep (rep "\"".toUTF8 "a" n) "\\q\"" 1)
  | "string-mb" => some (rep (rep "\"".toUTF8 "é" n) "\\q\"" 1)
  | "string-esc" => some (rep (rep "\"".toUTF8 "\\n" n) "\\q\"" 1)
  | "array" => some (rep (rep "[".toUTF8 "0," (n - 1)) "0]" 1)
  | "ints" => some (rep (rep "[".toUTF8 "1234567890123456," (n - 1)) "1234567890123456]" 1)
  | "keys-sorted" => some (keysText "k" n id)
  | "keys-reverse" => some (keysText "k" n (n - 1 - ·))
  -- 1,000,003 is prime ⇒ `i ↦ i * 1,000,003 mod n` permutes `[0, n)` for every `n` below it.
  | "keys-prefix" => some (keysText ("".pushn 'p' 64) n (· * 1000003 % n))
  | _ => none

def outcome : Except DecodeError Value → String
  | .ok _ => "ok"
  | .error .malformed => "malformed"
  | .error .tooLarge => "tooLarge"
  | .error (.duplicateKey _) => "duplicateKey"

/-- Milliseconds between two `IO.monoNanosNow` readings, 3 decimals. -/
def ms (t0 t1 : Nat) : String :=
  let us := (t1 - t0) / 1000
  let frac := toString (us % 1000)
  s!"{us / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- Each input decoded in its own dedicated Task (the closure runs on the Task's thread), results
in order; the Tasks are dropped on return. -/
def decodeAll (inputs : List ByteArray) : IO (Array (Except DecodeError Value)) := do
  let tasks := inputs.map fun b => Task.spawn (prio := .dedicated) fun _ => decode b
  let mut out := #[]
  for t in tasks do
    out := out.push (← IO.wait t)
  return out

/-- Columns: family n tasks bytes outcome decode_ms normalize_ms print_ms out_bytes release_ms
cpu_ticks (decode phase) rss_kB (before) hwm_kB released_kB. -/
def row (cells : List String) : IO Unit := IO.println ("\t".intercalate cells)

def measureJson (family : String) (n tasks cycles : Nat) (input : ByteArray) : IO Unit := do
  let inputs := (List.range (max tasks 1)).map fun k => rep input " " k
  let results : IO.Ref (Array (Except DecodeError Value)) ← IO.mkRef #[]
  let printed : IO.Ref (Array ByteArray) ← IO.mkRef #[]
  let (rss, _) ← memory
  for c in [0:max cycles 1] do
    let c0 ← cpuTicks
    let t0 ← IO.monoNanosNow
    if tasks == 0 then
      results.set (inputs.toArray.map decode)
    else
      results.set (← decodeAll inputs)
    let t1 ← IO.monoNanosNow
    let c1 ← cpuTicks
    for r in ← results.get do
      if let .ok v := r then
        printed.modify (·.push (print v))
    let t2 ← IO.monoNanosNow
    let out := (← printed.get).foldl (· + ·.size) 0
    let first := ((← results.get)[0]?).map outcome |>.getD "-"
    let (_, hwm) ← memory
    let t3 ← IO.monoNanosNow
    results.set #[]
    printed.set #[]
    let t4 ← IO.monoNanosNow
    let (released, _) ← memory
    let name := if cycles ≤ 1 then family else s!"{family}#{c + 1}"
    row
        [name, toString n, toString tasks, toString input.size, first, ms t0 t1, "-", ms t1 t2,
          toString out, ms t3 t4, toString (c1 - c0), toString rss, toString hwm, toString released]

def measureObject (n : Nat) : IO Unit := do
  let members : List (String × Value) :=
    (List.range n).map fun i => ("k" ++ pad7 (n - 1 - i), .int 0)
  let slot : IO.Ref (Option Value) ← IO.mkRef none
  let printed : IO.Ref ByteArray ← IO.mkRef .empty
  let (rss, _) ← memory
  let c0 ← cpuTicks
  let t0 ← IO.monoNanosNow
  slot.set (some (Value.object members))
  let t1 ← IO.monoNanosNow
  let c1 ← cpuTicks
  if let some v← slot.get then
    printed.set (print v)
  let t2 ← IO.monoNanosNow
  let out := (← printed.get).size
  let (_, hwm) ← memory
  let t3 ← IO.monoNanosNow
  slot.set none
  printed.set .empty
  let t4 ← IO.monoNanosNow
  let (released, _) ← memory
  row
      ["object", toString n, "1", "0", "ok", "-", ms t0 t1, ms t1 t2, toString out, ms t3 t4,
        toString (c1 - c0), toString rss, toString hwm, toString released]

def measureLock (n : Nat) : IO Unit := do
  let text := lockText n
  let decoded : IO.Ref (Option Lock) ← IO.mkRef none
  let reversed : IO.Ref (Option Lock) ← IO.mkRef none
  let normal : IO.Ref (Option Lock) ← IO.mkRef none
  let printed : IO.Ref ByteArray ← IO.mkRef .empty
  let (rss, _) ← memory
  let c0 ← cpuTicks
  let t0 ← IO.monoNanosNow
  decoded.set (decodeLock text).toOption
  let t1 ← IO.monoNanosNow
  let c1 ← cpuTicks
  let some l ← decoded.get | row ["lock", toString n, "1", toString text.size, "error"]
  reversed.set (some { l with entries := l.entries.reverse })
  let some r ← reversed.get | return
  let t2 ← IO.monoNanosNow
  normal.set (some r.normalize)
  let t3 ← IO.monoNanosNow
  let some m ← normal.get | return
  printed.set (encodeLock m)
  let t4 ← IO.monoNanosNow
  let out := (← printed.get).size
  let (_, hwm) ← memory
  let t5 ← IO.monoNanosNow
  decoded.set none
  reversed.set none
  normal.set none
  printed.set .empty
  let t6 ← IO.monoNanosNow
  let (released, _) ← memory
  row
      ["lock", toString n, "1", toString text.size, "ok", ms t0 t1, ms t2 t3, ms t3 t4,
        toString out, ms t5 t6, toString (c1 - c0), toString rss, toString hwm, toString released]

def usage : String := "usage: fvdep-dev json measure FAMILY N TASKS [CYCLES]\n"

/-- `fvdep-dev json measure FAMILY N TASKS [CYCLES]` (CYCLES: decode, print + release repeated in
one process, one row each: freed memory the allocator keeps plateaus, a leak grows per cycle). -/
def run (args : List String) : IO UInt32 := do
  let fail : IO UInt32 := do
    IO.eprint usage
    return 2
  let (family, n, tasks, cycles) ←
    match args with
    | [f, n, t] =>
      pure (f, n.toNat?, t.toNat?, some 1)
    | [f, n, t, c] =>
      pure (f, n.toNat?, t.toNat?, c.toNat?)
    | _ =>
      return ← fail
  let (some n, some tasks, some cycles) := (n, tasks, cycles) | fail
  match family with
  | "object" =>
    measureObject n
  | "lock" =>
    measureLock n
  | _ =>
    let some input := generate family n | return ← fail
    measureJson family n tasks cycles input
  return 0

end FvdepDev.Resources
