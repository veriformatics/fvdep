/-!
# C ABI conventions for Lean implementations shipped as a C library

fvdep states what an exported function must equal, through these fixed conversions:
an op `bytes → text` exports as `ByteArray → String`, an op `text → bytes | err` as
`String → Option ByteArray`. The implementer proves the export equal to the wrapped spec.
-/
namespace Fvdep.Abi

def bytesIn (b : ByteArray) : List Nat := b.toList.map UInt8.toNat
def bytesOut (l : List Nat) : ByteArray := ⟨(l.map Nat.toUInt8).toArray⟩
def textIn (s : String) : List Char := s.toList
def textOut (l : List Char) : String := String.ofList l

/-- Export shape of an op `bytes → text`. -/
def encoder (f : List Nat → List Char) : ByteArray → String := fun b => textOut (f (bytesIn b))
/-- Export shape of an op `text → bytes | err`. -/
def decoder (f : List Char → Option (List Nat)) : String → Option ByteArray :=
  fun s => (f (textIn s)).map bytesOut

end Fvdep.Abi
