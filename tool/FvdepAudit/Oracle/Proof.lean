import FvdepAudit.Export.Proof
import FvdepAudit.Oracle.Spec
import FvdepAudit.Oracle.Wire.Proof

/-! Proofs: the oracle's merge (contract `docs/contracts/U5b-oracle.md` V5 `trace`) + the wire link
(`wireLink`). -/

namespace FvdepAudit.Oracle.Proof

open FvdepCore.Protocol FvdepCore.Oracle FvdepAudit.Oracle.Spec FvdepAudit.Oracle.Wire.Spec

/-! ## UTF-8 lines -/

theorem fromUTF8?_eq_some (b : ByteArray) (s : String) :
    String.fromUTF8? b = some s ↔ s.toByteArray = b := by
  unfold String.fromUTF8?
  split
  · rename_i h
    constructor
    · intro e
      cases e
      rfl
    · intro e
      subst e
      rfl
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro e
    exact h (e ▸ s.isValidUTF8)

theorem parseLine_iff (rt : RTy) (l : ByteArray) (x : Reply) :
    parseLine rt l = some x ↔ Typed rt x ∧ l.data.toList = lineBytes x := by
  unfold parseLine lineBytes
  constructor
  · intro h
    obtain ⟨s, hs, hp⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ht, rfl⟩ := (FvdepAudit.Oracle.Wire.Proof.parseResult_exact rt s x).1 hp
    refine ⟨ht, ?_⟩
    rw [String.toUTF8_eq_toByteArray, (fromUTF8?_eq_some l _).1 hs]
  · rintro ⟨ht, hl⟩
    have hb : l = (resultLayout x).toByteArray := by
      apply ByteArray.ext
      apply Array.toList_inj.1
      rw [hl, String.toUTF8_eq_toByteArray]
    subst hb
    have hs : String.fromUTF8? (resultLayout x).toByteArray = some (resultLayout x) :=
      (fromUTF8?_eq_some _ _).2 rfl
    rw [hs, Option.bind_some]
    exact (FvdepAudit.Oracle.Wire.Proof.parseResult_exact rt _ x).2 ⟨ht, rfl⟩

/-! ## LF-terminated lines by offsets -/

theorem lf_split (b : ByteArray) (i : Nat) (hi : i ≤ b.size) :
    0x0A ∉ (b.extract i (FvdepCore.Export.lineEnd b i)).data.toList ∧
      (FvdepCore.Export.lineEnd b i < b.size →
        b.data.toList.drop i =
          (b.extract i (FvdepCore.Export.lineEnd b i)).data.toList ++
            0x0A :: b.data.toList.drop (FvdepCore.Export.lineEnd b i + 1)) := by
  have he := FvdepAudit.Export.Proof.lineEnd_eq b i hi
  have hsplit :=
    List.takeWhile_append_dropWhile (p := fun x : UInt8 => x != 0x0A) (l := b.data.toList.drop i)
  generalize hl : b.data.toList.drop i = l at hsplit he
  generalize hs : l.takeWhile (fun x : UInt8 => x != 0x0A) = s at hsplit he
  generalize hr : l.dropWhile (fun x : UInt8 => x != 0x0A) = r at hsplit
  have hseg : (b.extract i (FvdepCore.Export.lineEnd b i)).data.toList = s := by
    rw [FvdepAudit.Export.Proof.extract_eq, he, Nat.add_sub_cancel_left, hl, ← hsplit]
    exact List.take_left' rfl
  have hno : 0x0A ∉ s := fun hm => by
    rw [← hs] at hm
    have := List.all_eq_true.1 (List.all_takeWhile (p := fun x : UInt8 => x != 0x0A) (l := l)) _ hm
    simp at this
  have hrest : b.data.toList.drop (FvdepCore.Export.lineEnd b i) = r := by
    rw [he, ← List.drop_drop, hl, ← hsplit]
    exact List.drop_left' rfl
  refine ⟨hseg ▸ hno, fun hlt => ?_⟩
  cases r with
  | nil =>
    have : b.data.toList.drop (FvdepCore.Export.lineEnd b i) ≠ [] := by
      simp [List.drop_eq_nil_iff]
      exact hlt
    exact absurd hrest this
  | cons c
    rest =>
    have hc : c = 0x0A := by
      have h1 :=
        List.head_dropWhile_not (fun x : UInt8 => x != 0x0A) (l := l)
          (by
            rw [hr]; exact List.cons_ne_nil _ _)
      simp only [hr, List.head_cons] at h1
      simpa using h1
    subst hc
    have hend : b.data.toList.drop (FvdepCore.Export.lineEnd b i + 1) = rest := by
      rw [← List.drop_drop, hrest]
      rfl
    rw [← hsplit, hseg, hend]

/-- A line `l` without LF at offset `i`, then LF: `lineEnd` stops at that LF. -/
theorem lineEnd_of (b : ByteArray) (i : Nat) (l rest : List UInt8) (hi : i ≤ b.size)
    (h : b.data.toList.drop i = l ++ 0x0A :: rest) (hl : 0x0A ∉ l) :
    FvdepCore.Export.lineEnd b i = i + l.length := by
  rw [FvdepAudit.Export.Proof.lineEnd_eq b i hi, h, List.takeWhile_append_of_pos]
  · simp
  · intro x hx
    have : x ≠ 0x0A := fun e => hl (e ▸ hx)
    simpa using this

theorem framed_cons (l : List UInt8) (ls : List (List UInt8)) :
    framed (l :: ls) = l ++ 0x0A :: framed ls := by simp [framed]

theorem merged_nil {rt : RTy} {ls : List (List UInt8)} {out : List Reply}
    (h : Merged rt [] ls out) : ls = [] ∧ out = [] := by
  cases h
  exact ⟨rfl, rfl⟩

/-- V5 from offset `i`: the merge accepts exactly the bytes after `i` that frame lines paired with
the requests by `Merged`. -/
theorem mergeFrom_ok (rt : RTy) (b : ByteArray) :
    ∀ (reqs : List Req) (k i : Nat) (out : List Reply),
      i ≤ b.size →
        (mergeFrom rt b k i reqs = .ok out ↔
          ∃ ls : List (List UInt8),
            b.data.toList.drop i = framed ls ∧ (∀ l ∈ ls, 0x0A ∉ l) ∧ Merged rt reqs ls out)
  | [], k, i, out, hi => by
    simp only [mergeFrom, beq_iff_eq]
    constructor
    · intro h
      split at h
      · rename_i he
        cases h
        subst he
        refine ⟨[], ?_, by simp, .nil⟩
        simp [framed, List.drop_eq_nil_of_le]
      · cases h
    · rintro ⟨ls, hd, -, hm⟩
      obtain ⟨rfl, rfl⟩ := merged_nil hm
      have : i = b.size := by
        have h0 : (b.data.toList.drop i).length = 0 := by simp [hd, framed]
        simp at h0
        omega
      simp [this]
  | .invalid r :: rs, k, i, out, hi => by
    simp only [mergeFrom]
    constructor
    · intro h
      cases hm : mergeFrom rt b k i rs with
      | error e =>
        simp [hm] at h; cases h
      | ok out' =>
        simp only [hm] at h
        cases h
        obtain ⟨ls, hd, hn, hmg⟩ := (mergeFrom_ok rt b rs k i out' hi).1 hm
        exact ⟨ls, hd, hn, .invalid r hmg⟩
    · rintro ⟨ls, hd, hn, hmg⟩
      cases hmg with
      | invalid _ hmg' =>
        rw [(mergeFrom_ok rt b rs k i _ hi).2 ⟨ls, hd, hn, hmg'⟩]
        rfl
  | .valid :: rs, k, i, out, hi => by
    obtain ⟨hno, hsplit⟩ := lf_split b i hi
    simp only [mergeFrom]
    constructor
    · intro h
      split at h
      · rename_i hlt
        split at h
        · rename_i x hx
          cases hm : mergeFrom rt b (k + 1) (FvdepCore.Export.lineEnd b i + 1) rs with
          | error e =>
            simp [hm] at h; cases h
          | ok out' =>
            simp only [hm] at h
            cases h
            obtain ⟨ht, hlx⟩ := (parseLine_iff rt _ x).1 hx
            obtain ⟨ls, hd, hn, hmg⟩ :=
              (mergeFrom_ok rt b rs (k + 1) (FvdepCore.Export.lineEnd b i + 1) out' (by omega)).1 hm
            refine ⟨lineBytes x :: ls, ?_, ?_, .valid x ht hmg⟩
            · rw [hsplit hlt, framed_cons, hd, hlx]
            · intro l hl
              simp only [List.mem_cons] at hl
              rcases hl with rfl | hl
              · rw [← hlx]
                exact hno
              · exact hn l hl
        · cases h
      · cases h
    · rintro ⟨ls, hd, hn, hmg⟩
      cases hmg with
      | valid x ht hmg' =>
        rename_i ls' out'
        rw [framed_cons] at hd
        have hnx : 0x0A ∉ lineBytes x := hn _ (by simp)
        have he := lineEnd_of b i (lineBytes x) (framed ls') hi hd hnx
        have hlen :
          (b.data.toList.drop i).length = (lineBytes x).length + 1 + (framed ls').length := by
          rw [hd]
          simp only [List.length_append, List.length_cons]
          omega
        have hlt : FvdepCore.Export.lineEnd b i < b.size := by
          simp at hlen
          omega
        have hseg : (b.extract i (FvdepCore.Export.lineEnd b i)).data.toList = lineBytes x := by
          have := hsplit hlt
          rw [hd] at this
          exact
            (List.append_inj this
                (by
                  have hl2 := congrArg List.length this
                  simp only [List.length_append, List.length_cons] at hl2
                  rw [he]
                  simp
                  omega)).1.symm
        have hrest : b.data.toList.drop (FvdepCore.Export.lineEnd b i + 1) = framed ls' := by
          have := hsplit hlt
          rw [hd, hseg] at this
          simpa using this.symm
        have hx : parseLine rt (b.extract i (FvdepCore.Export.lineEnd b i)) = some x :=
          (parseLine_iff rt _ x).2 ⟨ht, hseg⟩
        simp only [hlt, ↓reduceIte, hx]
        rw [(mergeFrom_ok rt b rs (k + 1) _ out' (by omega)).2
            ⟨ls', hrest, fun l hl => hn l (by simp [hl]), hmg'⟩]
        rfl

/-- V5 `trace`: the merge returns `out` exactly when the step's bytes frame LF-free lines that
`Merged` pairs with the requests: a refused request's `invalid` reply where it stands, a valid
one's admitted reply whose result line is the next line, one line per valid request. -/
theorem merge_exact (rt : RTy) (reqs : List Req) (b : ByteArray) (out : List Reply) :
    merge rt reqs b = .ok out ↔
      ∃ ls : List (List UInt8),
        b.data.toList = framed ls ∧ (∀ l ∈ ls, 0x0A ∉ l) ∧ Merged rt reqs ls out := by
  unfold merge
  rw [mergeFrom_ok rt b reqs 1 0 out (Nat.zero_le _)]
  simp

/-- V5 `wireLink`: what `encodeArgs` writes for typed arguments, `decodeArgs` reads back in order;
a result line `resultLine` prints for an admitted reply parses back to it. -/
theorem wire_link :
    (∀ xs : List Val, Wire.decodeArgs (xs.map Val.ty) (Wire.encodeArgs xs) = some xs) ∧
      ∀ (rt : RTy) (r : Reply), Typed rt r → Wire.parseResult rt (Wire.resultLine r) = some r :=
  ⟨fun xs =>
    (FvdepAudit.Oracle.Wire.Proof.decodeArgs_exact _ _ xs).2
      ⟨rfl, FvdepAudit.Oracle.Wire.Proof.encodeArgs_eq xs⟩,
    fun rt r h =>
    (FvdepAudit.Oracle.Wire.Proof.parseResult_exact rt _ r).2
      ⟨h, FvdepAudit.Oracle.Wire.Proof.resultLine_eq r⟩⟩

end FvdepAudit.Oracle.Proof
