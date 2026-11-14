import FvdepAudit.Protocol.Proof.Val

/-! Proofs: requests + replies (contract U4 B4 `RequestExact`, `ReplyLayout`). -/

namespace FvdepAudit.Protocol.Proof

open FvdepCore.Json FvdepCore.Protocol FvdepAudit.Protocol.Spec

theorem decodeArgs_cons (t : Ty) (ts : List Ty) (a : Value) (as : List Value) (y : Val)
    (ys : List Val) :
    decodeArgs (t :: ts) (a :: as) = some (y :: ys) ↔
      decodeVal t a = some y ∧ decodeArgs ts as = some ys := by
  simp only [decodeArgs, Option.bind_eq_bind]
  cases decodeVal t a <;> cases decodeArgs ts as <;> simp

theorem decodeArgs_cons_nil (t : Ty) (ts : List Ty) (a : Value) (as : List Value) :
    decodeArgs (t :: ts) (a :: as) ≠ some [] := by
  simp only [decodeArgs, Option.bind_eq_bind]
  cases decodeVal t a <;> cases decodeArgs ts as <;> simp

theorem decodeArgs_exact :
    ∀ (ts : List Ty) (as : List Value) (xs : List Val),
      decodeArgs ts as = some xs ↔ as = xs.map valSpec ∧ xs.map Val.ty = ts
  | [], [], xs => by cases xs <;> simp [decodeArgs]
  | [], _ :: _, xs => by cases xs <;> simp [decodeArgs]
  | _ :: _, [], xs => by cases xs <;> simp [decodeArgs]
  | t :: ts, a :: as, xs => by
    cases xs with
    | nil => simp [decodeArgs_cons_nil]
    | cons y ys =>
      rw [decodeArgs_cons, val_exact t a y, decodeArgs_exact ts as ys]
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h2.symm, h3⟩, h1, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h3, h1.symm⟩, h2, h4⟩

theorem decodeArgs_valSpec : ∀ xs : List Val, decodeArgs (xs.map Val.ty) (xs.map valSpec) = some xs
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, List.map_cons, decodeArgs_cons]
    exact ⟨decodeVal_valSpec x, decodeArgs_valSpec xs⟩

theorem request_exact :
    ∀ (sig : Sig) (b : ByteArray) (xs : List Val),
      decodeRequest sig b = .ok xs ↔
        decode b = .ok (requestLayout sig.op (xs.map valSpec)) ∧ xs.map Val.ty = sig.args := by
  intro sig b xs
  constructor
  · intro h
    unfold decodeRequest at h
    split at h
    · cases h
    · cases h
    · cases h
    · rename_i args op hd
      split at h
      · cases h
      · rename_i hop
        split at h
        · cases h
        · split at h
          · rename_i ys hys
            simp only [Except.ok.injEq] at h
            subst h
            obtain ⟨hargs, hty⟩ := (decodeArgs_exact sig.args args ys).mp hys
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hop
            subst hop hargs
            exact ⟨hd, hty⟩
          · cases h
    · cases h
  · rintro ⟨hd, hty⟩
    have hlen : (xs.map valSpec).length = sig.args.length := by
      rw [List.length_map, ← hty, List.length_map]
    unfold decodeRequest
    rw [hd]
    simp only [requestLayout, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hlen]
    rw [← hty, decodeArgs_valSpec]

theorem reply_layout :
    ∀ r : Reply, encodeReply r = (FvdepCore.Json.print (replyLayout r)).push 0x0A := by
  intro r
  cases r <;> simp [encodeReply, replyValue, replyLayout, val_layout]

end FvdepAudit.Protocol.Proof
