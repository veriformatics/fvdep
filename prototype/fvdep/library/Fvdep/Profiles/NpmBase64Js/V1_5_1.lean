import Fvdep.Base64.Decode.V1_0_0
/-!
# Profile: npm `base64-js` 1.5.1 (`fromByteArray`, `toByteArray`)

Model = a literal port of `toByteArray` (index loop, `revLookup`, fixed-size `Uint8Array`),
checked against the real package by `fvdep profile npm:base64-js --check`.
Lengths count UTF-16 code units in JS and code points here; equal for the BMP text the check sends.
Deviations from `base64.decode@1.0.0`, each with a kernel-checked witness:
unused bits ignored, URL-safe `-`/`_` accepted, other non-alphabet chars read as 0,
data after the first `=` dropped, excess padding yields zero bytes.
`agrees` (where the contract accepts, the package returns the same bytes) is OPEN.
No theorem yet states that this deviation list is complete.
-/
namespace Fvdep.Profiles.NpmBase64Js.V1_5_1
open Fvdep.Base64 Encode.V1_0_0

def encode := Encode.V1_0_0.encode

/-- `revLookup[code]`: alphabet index; `-`/`_` → 62/63; anything else is `undefined`, read as 0. -/
def rev (c : Char) : Nat :=
  match val c with
  | some i => i
  | none => if c = '-' then 62 else if c = '_' then 63 else 0

/-- `revLookup[b64.charCodeAt(i)]`, 0 past the end (`NaN` index → `undefined`). -/
def get (s : List Char) (i : Nat) : Nat := (s[i]?.map rev).getD 0

def decode (s : List Char) : Option (List Nat) :=
  let len := s.length
  if len % 4 ≠ 0 then none else
  let validLen := (s.idxOf? '=').getD len
  let ph := if validLen = len then 0 else 4 - validLen % 4
  -- `new Uint8Array(byteLength)` throws on a negative length (e.g. `====`)
  if (validLen + ph) * 3 / 4 < ph then none else
  let size := (validLen + ph) * 3 / 4 - ph
  let full := if ph > 0 then validLen - 4 else validLen
  let groups := (full + 3) / 4
  let body := (List.range groups).flatMap fun g =>
    let i := 4 * g
    let t := get s i * 262144 + get s (i + 1) * 4096 + get s (i + 2) * 64 + get s (i + 3)
    [t / 65536 % 256, t / 256 % 256, t % 256]
  let i := 4 * groups
  let tail :=
    if ph = 2 then [(get s i * 4 + get s (i + 1) / 16) % 256]
    else if ph = 1 then
      let t := get s i * 1024 + get s (i + 1) * 16 + get s (i + 2) / 4
      [t / 256 % 256, t % 256]
    else []
  some ((body ++ tail ++ List.replicate size 0).take size)

/-! ## Relation to the contract -/

theorem encode_eq_contract : encode = Encode.V1_0_0.encode := rfl

/-- Witness: unused bits ignored (`QR==` decodes like `QQ==`). -/
theorem dev_unused_bits :
    decode "QR==".toList = some [65] ∧ Decode.V1_0_0.decode "QR==".toList = none := by decide

/-- Witness: URL-safe chars accepted in standard decoding (`-_8=` = `+/8=`). -/
theorem dev_url_chars :
    decode "-_8=".toList = some [251, 255] ∧ Decode.V1_0_0.decode "-_8=".toList = none := by decide

/-- Witness: non-alphabet chars read as 0 bits (`!!!!` → three zero bytes). -/
theorem dev_invalid_chars :
    decode "!!!!".toList = some [0, 0, 0] ∧ Decode.V1_0_0.decode "!!!!".toList = none := by decide

/-- Witness: data after the first `=` is dropped (`QQ==QUJD` → `A`). -/
theorem dev_after_padding :
    decode "QQ==QUJD".toList = some [65] ∧ Decode.V1_0_0.decode "QQ==QUJD".toList = none := by decide

/-- Witness: a group of padding alone yields zero bytes (`QUJD====` → two zero bytes). -/
theorem dev_excess_padding :
    decode "QUJD====".toList = some [0, 0] ∧ Decode.V1_0_0.decode "QUJD====".toList = none := by
  decide

/-- Where the contract accepts, the package returns the same bytes. OPEN: proof pending. -/
theorem agrees (s : List Char) (bs : List Nat) (h : Decode.V1_0_0.decode s = some bs) :
    decode s = some bs := by
  sorry

end Fvdep.Profiles.NpmBase64Js.V1_5_1
