import FvdepAudit.Hash.Spec

/-! Proofs of H4 (contract `docs/contracts/U3-codecs.md`) about `FvdepCore.Hash`'s shipped
functions: `hex` (H1), the `frame` layout + decoding, injectivity, `unframe` exactness (H2). -/

namespace FvdepAudit.Hash.Proof

open FvdepCore.Hash FvdepAudit.Hash.Spec

theorem hexDigit_eq (n : Nat) : hexDigit n = digit n := by
  by_cases h : n < 10 <;> simp [hexDigit, digit, h]

/-- H4 `HexExact`. -/
theorem hex_exact (b : ByteArray) : hex b = hexSpec b := by simp only [hex, hexSpec, hexDigit_eq]

/-! ## 8-byte numbers -/

theorem u64be_data (n : Nat) : (u64be n).data.toList = be8 n := by
  simp only [u64be, be8, List.map, List.toList_toArray, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply UInt8.toNat_inj.mp; simp [Nat.shiftRight_eq_div_pow])

theorem be8Value_be8 (n : Nat) : be8Value (be8 n) = n % 2 ^ 64 := by
  simp [be8Value, be8, List.foldl]
  omega

theorem be8_be8Value (xs : List UInt8) (h : xs.length = 8) : be8 (be8Value xs) = xs := by
  match xs, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7], _ =>
    have := x0.toNat_lt; have := x1.toNat_lt; have := x2.toNat_lt; have := x3.toNat_lt
    have := x4.toNat_lt; have := x5.toNat_lt; have := x6.toNat_lt; have := x7.toNat_lt
    simp only [be8, be8Value, List.foldl, List.map, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp
    all_goals omega

theorem takeU64_be8 (n : Nat) (rest : List UInt8) (h : n < 2 ^ 64) :
    takeU64 (be8 n ++ rest) = some (n, rest) := by
  have hv : be8Value (be8 n) = n := by rw [be8Value_be8, Nat.mod_eq_of_lt h]
  simp only [be8, List.map] at hv ⊢
  simp only [List.cons_append, List.nil_append, takeU64, hv]

theorem takeU64_some {bs rest : List UInt8} {n : Nat} (h : takeU64 bs = some (n, rest)) :
    bs = be8 n ++ rest ∧ n < 2 ^ 64 := by
  unfold takeU64 at h
  split at h
  · rename_i b0 b1 b2 b3 b4 b5 b6 b7 r
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine
      ⟨by
        rw [be8_be8Value _ rfl]; rfl, ?_⟩
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    simp only [be8Value, List.foldl]
    omega
  · simp at h

/-! ## Byte runs + text -/

theorem utf8_length (s : String) : (utf8 s).length = s.utf8ByteSize := by
  rw [utf8, Array.length_toList]
  rfl

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]
  rfl

theorem bytes_eta (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by simp

theorem takeBytes_append (xs rest : List UInt8) (n : Nat) (h : xs.length = n) :
    takeBytes (xs ++ rest) n = some (xs, rest) := by
  subst h
  simp [takeBytes, List.splitAt_eq]

theorem takeBytes_some {bs pre post : List UInt8} {n : Nat}
    (h : takeBytes bs n = some (pre, post)) : pre.length = n ∧ bs = pre ++ post := by
  simp only [takeBytes, List.splitAt_eq] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨‹_›, (List.take_append_drop n bs).symm⟩
  · simp at h

theorem text_utf8 (s : String) : text (utf8 s) = some s := by
  simp [text, utf8, String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

theorem text_some {pre : List UInt8} {s : String} (h : text pre = some s) : utf8 s = pre := by
  simp only [text, String.fromUTF8?] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [utf8, String.fromUTF8]
  · simp at h

/-! ## Layout -/

theorem frame_fold (gs : List (String × ByteArray)) (acc : ByteArray) :
    (gs.foldl (fun acc f => acc ++ u64be f.1.utf8ByteSize ++ f.1.toUTF8 ++ u64be f.2.size ++ f.2)
          acc).data.toList =
      acc.data.toList ++ gs.flatMap entry := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [ByteArray.toList_data_append, u64be_data, List.flatMap_cons, entry, utf8_length,
      List.append_assoc]
    rfl

/-- H4 `FrameLayout`. -/
theorem frame_layout (t : String) (fs : List (String × ByteArray)) :
    (frame t fs).data.toList = frameSpec t fs := by
  rw [frame, frame_fold]
  simp only [ByteArray.toList_data_append, u64be_data, frameSpec, sortByPath, byPath, utf8_length,
    List.append_assoc]
  rfl

/-! ## Decoding -/

/-- Every path strictly above `prev`, strictly ascending. -/
def Ascending (prev : Option String) (gs : List (String × ByteArray)) : Prop :=
  (∀ p ∈ prev, ∀ g ∈ gs, p < g.1) ∧ (gs.map (·.1)).Pairwise (· < ·)

/-- Every path + byte length below 2^64. -/
def Bounded (gs : List (String × ByteArray)) : Prop :=
  ∀ g ∈ gs, (utf8 g.1).length < 2 ^ 64 ∧ g.2.size < 2 ^ 64

theorem takeFiles_entries (gs : List (String × ByteArray)) (prev : Option String)
    (acc : List (String × ByteArray)) (ha : Ascending prev gs) (hb : Bounded gs) :
    takeFiles gs.length prev (gs.flatMap entry) acc = some (acc.reverse ++ gs) := by
  induction gs generalizing prev acc with
  | nil => simp [takeFiles]
  | cons g gs ih =>
    obtain ⟨hp, hpw⟩ := ha
    have hg := hb g (by simp)
    have hall : (prev.all fun p => decide (p < g.1)) = true := by
      cases prev with
      | none => rfl
      | some p => simpa using hp p rfl g (by simp)
    have hrest : Ascending (some g.1) gs := by
      refine ⟨fun p hp' h hh => ?_, (List.pairwise_cons.mp hpw).2⟩
      cases hp'
      exact (List.pairwise_cons.mp hpw).1 h.1 (List.mem_map_of_mem hh)
    have ih' := ih (some g.1) ((g.1, g.2) :: acc) hrest fun g' h => hb g' (by simp [h])
    have hsz := (size_eq_length g.2).symm
    simp only [List.length_cons, List.flatMap_cons, entry, List.append_assoc, takeFiles,
      takeU64_be8 _ _ hg.1, Option.bind_eq_bind, Option.bind_some, takeBytes_append _ _ _ rfl,
      text_utf8, hall, ite_true, takeU64_be8 _ _ hg.2, takeBytes_append _ _ _ hsz, bytes_eta]
    rw [ih']
    simp

theorem lt_of_le_ne {a b : String} (h1 : a ≤ b) (h2 : a ≠ b) : a < b :=
  Classical.byContradiction fun h3 => h2 (Std.le_antisymm h1 (String.not_lt.mp h3))

theorem path_trans (a b c : String × ByteArray) (h1 : decide (a.1 ≤ b.1) = true)
    (h2 : decide (b.1 ≤ c.1) = true) : decide (a.1 ≤ c.1) = true := by
  simp only [decide_eq_true_eq] at *
  exact String.le_trans h1 h2

theorem path_total (a b : String × ByteArray) :
    (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total _ _

theorem byPath_length (fs : List (String × ByteArray)) : (byPath fs).length = fs.length :=
  List.length_mergeSort _

theorem byPath_perm (fs : List (String × ByteArray)) : (byPath fs).Perm fs :=
  List.mergeSort_perm _ _

/-- Sorted by path + distinct paths = strictly ascending. -/
theorem byPath_ascending (fs : List (String × ByteArray)) (hd : (fs.map (·.1)).Nodup) :
    Ascending none (byPath fs) := by
  refine ⟨by simp, ?_⟩
  have hs := List.pairwise_mergeSort path_trans path_total fs
  have hn₀ : ((byPath fs).map Prod.fst).Nodup := ((byPath_perm fs).map Prod.fst).nodup_iff.mpr hd
  have hn : ((byPath fs).map (·.1)).Pairwise (· ≠ ·) := hn₀
  rw [List.pairwise_map] at hn ⊢
  exact (hs.and hn).imp fun h => lt_of_le_ne (of_decide_eq_true h.1) h.2

/-- H4 `FrameDecode`. -/
theorem frame_decode (t : String) (fs : List (String × ByteArray)) (h : FrameDomain t fs) :
    unframe (frame t fs) = some (t, byPath fs) := by
  obtain ⟨hd, ht, hn, hf⟩ := h
  have hb : Bounded (byPath fs) := fun g hg => hf g ((byPath_perm fs).mem_iff.mp hg)
  have hfiles := takeFiles_entries (byPath fs) none [] (byPath_ascending fs hd) hb
  rw [byPath_length] at hfiles
  simp only [unframe, frame_layout, frameSpec, List.append_assoc, takeU64_be8 _ _ ht,
    Option.bind_eq_bind, Option.bind_some, takeBytes_append _ _ _ rfl, text_utf8,
    takeU64_be8 _ _ hn, hfiles]
  simp

theorem takeFiles_some (k : Nat) (prev : Option String) (bs : List UInt8)
    (acc out : List (String × ByteArray)) (h : takeFiles k prev bs acc = some out) :
    ∃ gs,
      out = acc.reverse ++ gs ∧
        bs = gs.flatMap entry ∧ gs.length = k ∧ Ascending prev gs ∧ Bounded gs := by
  induction k generalizing prev bs acc with
  | zero =>
    simp only [takeFiles] at h
    split at h
    · rename_i hbs
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨[], by simp, by simpa using hbs, rfl, ⟨by simp, by simp⟩, by simp [Bounded]⟩
    · simp at h
  | succ k ih =>
    simp only [takeFiles, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨plen, bs1⟩, h1, h⟩ := h
    obtain ⟨⟨pb, bs2⟩, h2, h⟩ := h
    obtain ⟨path, h3, h⟩ := h
    split at h
    · rename_i hall
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨blen, bs3⟩, h4, h⟩ := h
      obtain ⟨⟨bb, bs4⟩, h5, h⟩ := h
      obtain ⟨gs, rfl, rfl, hlen, ⟨hp, hpw⟩, hb⟩ := ih _ _ _ h
      obtain ⟨rfl, hplen⟩ := takeU64_some h1
      obtain ⟨hpbl, rfl⟩ := takeBytes_some h2
      have hpath := text_some h3
      obtain ⟨rfl, hblen⟩ := takeU64_some h4
      obtain ⟨hbbl, rfl⟩ := takeBytes_some h5
      dsimp only at hpbl hpath hbbl
      have hall' : ∀ p ∈ prev, p < path := by
        intro p hp'
        cases hp'
        simpa using hall
      refine ⟨(path, ⟨bb.toArray⟩) :: gs, by simp, ?_, by simp [hlen], ⟨?_, ?_⟩, ?_⟩
      · simp [entry, hpath, hpbl, hbbl, size_eq_length]
      · intro p hp' g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hall' p hp'
        · exact String.lt_trans (hall' p hp') (hp path rfl g hg)
      · simp only [List.map_cons, List.pairwise_cons]
        refine ⟨fun a ha => ?_, hpw⟩
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
        exact hp path rfl g hg
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact
            ⟨by
              rw [hpath, hpbl]; exact hplen, by simp [size_eq_length, hbbl, hblen]⟩
        · exact hb g hg
    · simp at h

/-- H4 `UnframeExact`. -/
theorem unframe_exact (b : ByteArray) (t : String) (fs : List (String × ByteArray))
    (h : unframe b = some (t, fs)) :
    FrameDomain t fs ∧ (fs.map (·.1)).Pairwise (· < ·) ∧ frame t fs = b := by
  simp only [unframe, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨tlen, bs1⟩, h1, h⟩ := h
  obtain ⟨⟨tb, bs2⟩, h2, h⟩ := h
  obtain ⟨tag, h3, h⟩ := h
  obtain ⟨⟨count, bs3⟩, h4, h⟩ := h
  obtain ⟨files, h5, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨gs, hout, hbs, hlen, ⟨-, hpw⟩, hb⟩ := takeFiles_some _ _ _ _ _ h5
  simp only [List.reverse_nil, List.nil_append] at hout
  subst hout
  obtain ⟨hb1, htl⟩ := takeU64_some h1
  obtain ⟨htbl, rfl⟩ := takeBytes_some h2
  have htag := text_some h3
  obtain ⟨rfl, hcount⟩ := takeU64_some h4
  dsimp only at htbl htag hbs hb1
  have hnodup : (files.map (·.1)).Pairwise (· ≠ ·) :=
    hpw.imp fun {a b} (hlt : a < b) (he : a = b) => String.lt_irrefl a (by rwa [← he] at hlt)
  refine
    ⟨⟨hnodup, by
        rw [htag, htbl]; exact htl, by
        rw [hlen]; exact hcount, hb⟩,
      hpw, ?_⟩
  have hle : files.Pairwise fun a b => decide (a.1 ≤ b.1) = true :=
    (List.pairwise_map.mp hpw).imp fun hlt =>
      decide_eq_true (String.not_lt.mp (String.lt_asymm hlt))
  have hsorted : byPath files = files := List.mergeSort_of_pairwise hle
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [frame_layout, hb1, hbs]
  simp only [frameSpec, hsorted, htag, htbl, hlen, List.append_assoc]

/-- H4 `FrameInjective`. -/
theorem frame_injective (t : String) (fs : List (String × ByteArray)) (t' : String)
    (fs' : List (String × ByteArray)) (h : FrameDomain t fs) (h' : FrameDomain t' fs')
    (he : frame t fs = frame t' fs') : t = t' ∧ fs.Perm fs' := by
  have e := frame_decode t fs h
  rw [he, frame_decode t' fs' h'] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, e⟩ := e
  exact ⟨rfl, (byPath_perm fs).symm.trans (e ▸ byPath_perm fs')⟩

end FvdepAudit.Hash.Proof
