/-! C ABI shapes v1.0.0 (`docs/library.md` C ABI shapes; Decisions C ABI): an `abi` implementation
proves `@impl = Fvdep.Abi.V1_0_0.<shape> @spec`. Bytes in, bytes out over the whole byte domain;
every conversion (UTF-8 validity included) sits inside the statement. -/

namespace Fvdep.Abi.V1_0_0

/-- The base64 encoders: the spec's characters as UTF-8 bytes. -/
def encoder : (List UInt8 → List Char) → ByteArray → ByteArray := fun f b =>
  (String.ofList (f b.toList)).toUTF8

/-- The base64 decoders: input bytes that are not UTF-8 = rejected; else the spec's result. -/
def decoder : (List Char → Option (List UInt8)) → ByteArray → Option ByteArray := fun f b =>
  (String.fromUTF8? b).bind fun s => (f s.toList).map fun l => ⟨l.toArray⟩

end Fvdep.Abi.V1_0_0
