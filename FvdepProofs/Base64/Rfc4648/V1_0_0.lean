import Fvdep.Base64.Rfc4648.V1_0_0

/-! Lemmas about the shared RFC 4648 module, generic over an alphabet that is `Good` (both RFC
alphabets are): the encoders' `bits` + `length` and the decoders' `inverse` + `canonical`. -/

namespace FvdepProofs.Base64.Rfc4648.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0

/-- What the proofs need of an alphabet: 64 symbols, each symbol's value its index, `=` none of
them. -/
structure Good (a : List Char) : Prop where
  length : a.length = 64
  valueSymbol : ∀ i, i < 64 → value a (symbol a i) = some i
  symbolNePad : ∀ i, i < 64 → symbol a i ≠ '='
  valuePad : value a '=' = none

set_option maxRecDepth 8000 in
theorem standard_good : Good standard := ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 8000 in
theorem url_good : Good url := ⟨by decide, by decide, by decide, by decide⟩

theorem value_spec {a : List Char} (g : Good a) {c : Char} {i : Nat} (h : value a c = some i) :
    i < 64 ∧ symbol a i = c := by
  obtain ⟨hi, hc, -⟩ := List.idxOf?_eq_some_iff.mp h
  refine ⟨g.length ▸ hi, ?_⟩
  simp [symbol, List.getD, hi, hc]

/-- A byte from a number: its low 8 bits. -/
theorem ofNat_eq {k : Nat} {x : UInt8} (h : k % 256 = x.toNat) : UInt8.ofNat k = x :=
  UInt8.toNat.inj (by simpa using h)

theorem encodeWith_eq_nil {a : List Char} {b : List UInt8} : encodeWith a b = [] ↔ b = [] := by
  constructor
  · intro h
    rcases b with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> simp [encodeWith] at h ⊢
  · rintro rfl
    rfl

theorem encodeWith_length (a : List Char) :
    ∀ b : List UInt8, (encodeWith a b).length = 4 * ((b.length + 2) / 3)
  | _ :: _ :: _ :: rest => by
    simp only [encodeWith, List.length_cons, encodeWith_length a rest]
    omega
  | [_, _] => by simp [encodeWith]
  | [_] => by simp [encodeWith]
  | [] => by simp [encodeWith]

theorem quad_symbols {a : List Char} (g : Good a) (x y z : UInt8) :
    quad a (symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) / 262144))
        (symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) / 4096 % 64))
        (symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) / 64 % 64))
        (symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) % 64)) =
      some [x, y, z] := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hz := z.toNat_lt
  generalize hn : x.toNat * 65536 + y.toNat * 256 + z.toNat = n
  have h0 : n / 262144 < 64 := by omega
  have h1 : n / 4096 % 64 < 64 := Nat.mod_lt _ (by decide)
  have h2 : n / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  have h3 : n % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [quad, g.valueSymbol _ h0, g.valueSymbol _ h1, g.valueSymbol _ h2, g.valueSymbol _ h3,
    Option.bind_eq_bind, Option.bind_some, Nat.toUInt8_eq, Option.some.injEq, List.cons.injEq,
    and_true]
  refine ⟨ofNat_eq ?_, ofNat_eq ?_, ofNat_eq ?_⟩ <;> omega

theorem decodeWith_encodeWith {a : List Char} (g : Good a) :
    ∀ b : List UInt8, decodeWith a (encodeWith a b) = some b
  | x :: y :: z :: rest => by
    have hq := quad_symbols g x y z
    have h3 : (x.toNat * 65536 + y.toNat * 256 + z.toNat) % 64 < 64 := Nat.mod_lt _ (by decide)
    by_cases hr : rest = []
    · subst hr
      simp only [encodeWith, decodeWith, List.isEmpty_nil, final, g.symbolNePad _ h3, ↓reduceIte]
      simpa using hq
    · have hie : (encodeWith a rest).isEmpty = false :=
        List.isEmpty_eq_false_iff.mpr (mt encodeWith_eq_nil.mp hr)
      simp only [encodeWith, decodeWith, hie, Bool.false_eq_true, ↓reduceIte, hq,
        decodeWith_encodeWith g rest, Option.bind_eq_bind, Option.bind_some, List.cons_append,
        List.nil_append]
  | [x, y] => by
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    generalize hn : x.toNat * 65536 + y.toNat * 256 = n
    have h0 : n / 262144 < 64 := by omega
    have h1 : n / 4096 % 64 < 64 := Nat.mod_lt _ (by decide)
    have h2 : n / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
    have hm : n / 64 % 64 % 4 = 0 := by omega
    simp only [encodeWith, hn, decodeWith, List.isEmpty_nil, final, g.symbolNePad _ h2, ↓reduceIte,
      g.valueSymbol _ h0, g.valueSymbol _ h1, g.valueSymbol _ h2, hm, Option.bind_eq_bind,
      Option.bind_some, Nat.toUInt8_eq, Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨ofNat_eq ?_, ofNat_eq ?_⟩ <;> omega
  | [x] => by
    have hx := x.toNat_lt
    generalize hn : x.toNat * 65536 = n
    have h0 : n / 262144 < 64 := by omega
    have h1 : n / 4096 % 64 < 64 := Nat.mod_lt _ (by decide)
    have hm : n / 4096 % 64 % 16 = 0 := by omega
    simp only [encodeWith, hn, decodeWith, List.isEmpty_nil, final, ↓reduceIte, g.valueSymbol _ h0,
      g.valueSymbol _ h1, hm, Option.bind_eq_bind, Option.bind_some, Nat.toUInt8_eq,
      Option.some.injEq, List.cons.injEq, and_true]
    apply ofNat_eq
    omega
  | [] => rfl

theorem quad_spec {a : List Char} (g : Good a) {c0 c1 c2 c3 : Char} {q : List UInt8}
    (h : quad a c0 c1 c2 c3 = some q) (t : List UInt8) :
    encodeWith a (q ++ t) = c0 :: c1 :: c2 :: c3 :: encodeWith a t := by
  simp only [quad, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨i0, h0, i1, h1, i2, h2, i3, h3, rfl⟩ := h
  obtain ⟨l0, rfl⟩ := value_spec g h0
  obtain ⟨l1, rfl⟩ := value_spec g h1
  obtain ⟨l2, rfl⟩ := value_spec g h2
  obtain ⟨l3, rfl⟩ := value_spec g h3
  simp only [List.cons_append, List.nil_append, encodeWith, Nat.toUInt8_eq, UInt8.toNat_ofNat',
    List.cons.injEq, and_true]
  refine ⟨congrArg _ ?_, congrArg _ ?_, congrArg _ ?_, congrArg _ ?_⟩ <;> omega

theorem final_spec {a : List Char} (g : Good a) {c0 c1 c2 c3 : Char} {q : List UInt8}
    (h : final a c0 c1 c2 c3 = some q) : encodeWith a q = [c0, c1, c2, c3] := by
  unfold final at h
  split at h
  · subst_vars
    split at h
    · subst_vars
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i0, h0, i1, h1, h⟩ := h
      split at h
      · cases h
        obtain ⟨l0, rfl⟩ := value_spec g h0
        obtain ⟨l1, rfl⟩ := value_spec g h1
        simp only [encodeWith, Nat.toUInt8_eq, UInt8.toNat_ofNat', List.cons.injEq, and_true]
        refine ⟨congrArg _ ?_, congrArg _ ?_⟩ <;> omega
      · cases h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i0, h0, i1, h1, i2, h2, h⟩ := h
      split at h
      · cases h
        obtain ⟨l0, rfl⟩ := value_spec g h0
        obtain ⟨l1, rfl⟩ := value_spec g h1
        obtain ⟨l2, rfl⟩ := value_spec g h2
        simp only [encodeWith, Nat.toUInt8_eq, UInt8.toNat_ofNat', List.cons.injEq, and_true]
        refine ⟨congrArg _ ?_, congrArg _ ?_, congrArg _ ?_⟩ <;> omega
      · cases h
  · simpa [encodeWith] using quad_spec g h []

theorem encodeWith_decodeWith {a : List Char} (g : Good a) :
    ∀ (s : List Char) (b : List UInt8), decodeWith a s = some b → encodeWith a b = s
  | [], b, h => by
    simp only [decodeWith, Option.some.injEq] at h
    subst h
    rfl
  | c0 :: c1 :: c2 :: c3 :: rest, b, h => by
    simp only [decodeWith] at h
    split at h
    · rename_i hr
      have : rest = [] := List.isEmpty_iff.mp hr
      subst this
      exact final_spec g h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨q, hq, t, ht, rfl⟩ := h
      rw [quad_spec g hq, encodeWith_decodeWith g rest t ht]
  | [_], _, h | [_, _], _, h | [_, _, _], _, h => by simp [decodeWith] at h

/-! ## `encodeWith` = §4's bit-group description -/

theorem bitsOf_eq (x : UInt8) :
    bitsOf x =
      [x.toNat.testBit 7, x.toNat.testBit 6, x.toNat.testBit 5, x.toNat.testBit 4,
        x.toNat.testBit 3, x.toNat.testBit 2, x.toNat.testBit 1, x.toNat.testBit 0] := rfl

theorem valueOf_six (b0 b1 b2 b3 b4 b5 : Bool) :
    valueOf [b0, b1, b2, b3, b4, b5] =
      b0.toNat * 32 + b1.toNat * 16 + b2.toNat * 8 + b3.toNat * 4 + b4.toNat * 2 + b5.toNat := by
  simp only [valueOf, List.foldl]
  omega

/-- `encodeBits` peels a whole 3-byte group. -/
theorem encodeBits_cons3 (a : List Char) (x y z : UInt8) (rest : List UInt8) :
    encodeBits a (x :: y :: z :: rest) =
      symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) / 262144) ::
        symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) / 4096 % 64) ::
        symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) / 64 % 64) ::
        symbol a ((x.toNat * 65536 + y.toNat * 256 + z.toNat) % 64) :: encodeBits a rest := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hz := z.toNat_lt
  simp only [encodeBits, List.flatMap_cons, bitsOf_eq, List.cons_append, List.nil_append, sextets,
    List.map_cons, List.length_cons, List.length_nil, Nat.sub_self, List.replicate_zero,
    List.append_nil, valueOf_six, Nat.toNat_testBit, Nat.reducePow, List.cons.injEq]
  refine ⟨congrArg _ ?_, congrArg _ ?_, congrArg _ ?_, congrArg _ ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · congr 2
    omega

theorem encodeWith_encodeBits (a : List Char) : ∀ b : List UInt8, encodeWith a b = encodeBits a b
  | x :: y :: z :: rest => by
    rw [encodeBits_cons3, ← encodeWith_encodeBits a rest]
    rfl
  | [x, y] => by
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    simp only [encodeWith, encodeBits, List.flatMap_cons, List.flatMap_nil, bitsOf_eq,
      List.cons_append, List.nil_append, List.append_nil, sextets, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, List.replicate, valueOf_six, Nat.toNat_testBit,
      Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, Bool.toNat_false, List.cons.injEq,
      and_true]
    refine ⟨congrArg _ ?_, congrArg _ ?_, congrArg _ ?_⟩ <;> omega
  | [x] => by
    have hx := x.toNat_lt
    simp only [encodeWith, encodeBits, List.flatMap_cons, List.flatMap_nil, bitsOf_eq,
      List.cons_append, List.nil_append, List.append_nil, sextets, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, List.replicate, valueOf_six, Nat.toNat_testBit,
      Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, Bool.toNat_false, List.cons.injEq,
      and_true]
    refine ⟨congrArg _ ?_, congrArg _ ?_⟩ <;> omega
  | [] => by simp [encodeWith, encodeBits, sextets]

end FvdepProofs.Base64.Rfc4648.V1_0_0
