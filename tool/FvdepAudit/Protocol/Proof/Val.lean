import FvdepAudit.Hash.Proof.Frame
import FvdepAudit.Protocol.Spec

/-! Proofs: values (contract U4 B4 `ValLayout`, `ValExact`, `ValValid`). -/

namespace FvdepAudit.Protocol.Proof

open FvdepCore.Json FvdepCore.Protocol FvdepAudit.Protocol.Spec Fvdep.Semver.Version.V1_0_0

theorem maxInt_eq : FvdepCore.Json.maxInt = safe := by decide

theorem specMaxInt_eq : FvdepAudit.Json.Spec.maxInt = safe := by decide

/-! ## Decimals -/

theorem decimal_of_parseNat {cs : List Char} {n : Nat} (h : FvdepCore.Ids.parseNat cs = some n) :
    FvdepCore.Ids.decimal n = cs := by
  unfold FvdepCore.Ids.parseNat at h
  rw [← FvdepCore.Ids.decimalFast_eq]
  exact FvdepCore.Ids.canon_print h

theorem dash_not_mem_decimal (n : Nat) : '-' ∉ FvdepCore.Ids.decimal n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have hd : ∀ d, d < 10 → FvdepCore.Ids.digit d ≠ '-' := by decide
    unfold FvdepCore.Ids.decimal
    split
    · rename_i h
      simpa using fun e => hd n h e.symm
    · rename_i h
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨ih (n / 10) (by omega), fun e => hd (n % 10) (Nat.mod_lt _ (by omega)) e.symm⟩

/-! ## Hex -/

open FvdepAudit.Hash.Spec in
/-- The hex text of a byte list (H1's digits). -/
def hexChars (b : List UInt8) : List Char :=
  b.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)]

theorem bytesSpec_eq (b : List UInt8) : bytesSpec b = String.ofList (hexChars b) := by
  simp [bytesSpec, FvdepAudit.Hash.Spec.hexSpec, hexChars]

theorem hexOf_digit :
    ∀ d : Fin 16, FvdepCore.Ids.hexOf? (FvdepAudit.Hash.Spec.digit d.val) = some d := by decide

theorem digit_of_hexOf {c : Char} {d : Fin 16} (h : FvdepCore.Ids.hexOf? c = some d) :
    FvdepAudit.Hash.Spec.digit d.val = c := by
  unfold FvdepCore.Ids.hexOf? at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [FvdepAudit.Hash.Spec.digit, show c.toNat - 48 < 10 by omega, ↓reduceIte]
    rw [show 48 + (c.toNat - 48) = c.toNat by omega, Char.ofNat_toNat]
  · split at h
    · rename_i _ hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [FvdepAudit.Hash.Spec.digit, show ¬(c.toNat - 87 < 10) by omega, ↓reduceIte]
      rw [show 87 + (c.toNat - 87) = c.toNat by omega, Char.ofNat_toNat]
    · cases h

theorem unhex_hexChars : ∀ b : List UInt8, unhex (hexChars b) = some b
  | [] => rfl
  | x :: xs => by
    have hx := x.toNat_lt
    have h1 := hexOf_digit ⟨x.toNat / 16, by omega⟩
    have h2 := hexOf_digit ⟨x.toNat % 16, by omega⟩
    simp only [hexChars, List.flatMap_cons, List.cons_append, List.nil_append] at h1 h2 ⊢
    simp only [unhex, h1, h2, Option.bind_eq_bind, Option.bind_some]
    rw [show
        xs.flatMap
            (fun x =>
              [FvdepAudit.Hash.Spec.digit (x.toNat / 16),
                FvdepAudit.Hash.Spec.digit (x.toNat % 16)]) =
          hexChars xs
        from rfl,
      unhex_hexChars xs]
    simp only [Option.bind_some, Option.some.injEq, List.cons.injEq, and_true]
    apply UInt8.toNat.inj
    simp
    omega

theorem hexChars_of_unhex : ∀ {cs : List Char} {b : List UInt8}, unhex cs = some b → hexChars b = cs
  | [], b, h => by
    simp only [unhex, Option.some.injEq] at h
    subst h
    rfl
  | hi :: lo :: rest, b, h => by
    simp only [unhex, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨d1, h1, d2, h2, t, ht, rfl⟩ := h
    have hv : ((d1.val * 16 + d2.val).toUInt8).toNat = d1.val * 16 + d2.val := by
      simp
      omega
    simp only [hexChars, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [hv, show (d1.val * 16 + d2.val) / 16 = d1.val by omega]
      exact digit_of_hexOf h1
    · rw [hv, show (d1.val * 16 + d2.val) % 16 = d2.val by omega]
      exact digit_of_hexOf h2
    · exact hexChars_of_unhex ht
  | [_], b, h => by simp [unhex] at h

/-! ## Numbers -/

theorem encodeNat_eq (n : Nat) : encodeNat n = natSpec n := by
  simp [encodeNat, natSpec, maxInt_eq, FvdepCore.Ids.decimalFast_eq]

theorem decodeNat_natSpec (n : Nat) : decodeNat (natSpec n) = some n := by
  unfold natSpec
  split
  · rename_i h
    simp only [decodeNat, maxInt_eq]
    split
    · simp
    · exfalso
      omega
  · rename_i h
    simp [decodeNat, String.toList_ofList, FvdepCore.Ids.parseNat_decimal, maxInt_eq]
    omega

theorem natSpec_of_decodeNat {v : Value} {n : Nat} (h : decodeNat v = some n) : natSpec n = v := by
  cases v with
  | int k =>
    simp only [decodeNat, maxInt_eq] at h
    split at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      unfold natSpec
      simp only [show k.toNat ≤ safe by omega, ↓reduceIte]
      congr 1
      omega
    · cases h
  | str s =>
    simp only [decodeNat] at h
    split at h
    · rename_i m hm
      split at h
      · rename_i hlt
        simp only [Option.some.injEq] at h
        subst h
        unfold natSpec
        rw [maxInt_eq] at hlt
        simp only [show ¬(m ≤ safe) by omega, ↓reduceIte]
        rw [decimal_of_parseNat hm, String.ofList_toList]
      · cases h
    · cases h
  | null
  | bool _
  | arr _
  | obj _ => simp [decodeNat] at h

theorem encodeInt_eq (i : Int) : encodeInt i = intSpec i := by
  unfold encodeInt intSpec
  rw [maxInt_eq, FvdepCore.Ids.decimalFast_eq]
  split
  · rfl
  · split <;> simp_all

theorem decodeInt_intSpec (i : Int) : decodeInt (intSpec i) = some i := by
  unfold intSpec
  split
  · rename_i h
    simp only [decodeInt, maxInt_eq, h, ↓reduceIte]
  · rename_i h
    split
    · rename_i hneg
      simp only [decodeInt, List.singleton_append, String.toList_ofList,
        FvdepCore.Ids.parseNat_decimal, maxInt_eq, show safe < i.natAbs by omega, ↓reduceIte]
      congr 1
      omega
    · rename_i hpos
      simp only [decodeInt, List.nil_append, String.toList_ofList]
      split
      · rename_i ds hds
        exact absurd (hds ▸ List.mem_cons_self ..) (dash_not_mem_decimal i.natAbs)
      · simp only [FvdepCore.Ids.parseNat_decimal, maxInt_eq, show safe < i.natAbs by omega,
          ↓reduceIte, Option.some.injEq]
        omega

theorem intSpec_of_decodeInt {v : Value} {i : Int} (h : decodeInt v = some i) : intSpec i = v := by
  cases v with
  | int k =>
    simp only [decodeInt, maxInt_eq] at h
    split at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      unfold intSpec
      simp only [hk, ↓reduceIte]
    · cases h
  | str s =>
    simp only [decodeInt] at h
    split at h
    · rename_i ds hds
      split at h
      · rename_i m hm
        split at h
        · rename_i hlt
          simp only [Option.some.injEq] at h
          subst h
          rw [maxInt_eq] at hlt
          unfold intSpec
          simp only [show (-(m : Int)).natAbs = m by omega, show ¬(m ≤ safe) by omega,
            show (-(m : Int)) < 0 by omega, ↓reduceIte, decimal_of_parseNat hm,
            List.singleton_append, ← hds, String.ofList_toList]
        · cases h
      · cases h
    · rename_i ds hds
      split at h
      · rename_i m hm
        split at h
        · rename_i hlt
          simp only [Option.some.injEq] at h
          subst h
          rw [maxInt_eq] at hlt
          unfold intSpec
          simp only [show (m : Int).natAbs = m by omega, show ¬(m ≤ safe) by omega,
            show ¬((m : Int) < 0) by omega, ↓reduceIte, decimal_of_parseNat hm, List.nil_append,
            String.ofList_toList]
        · cases h
      · cases h
  | null
  | bool _
  | arr _
  | obj _ => simp [decodeInt] at h

/-! ## Lists -/

theorem mapM_map_some {α β : Type} {f : α → Option β} {g : β → α} (hf : ∀ b, f (g b) = some b) :
    ∀ bs : List β, (bs.map g).mapM f = some bs
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, List.mapM_cons, hf b, mapM_map_some hf bs, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

theorem mapM_inv {α β : Type} {f : α → Option β} {g : β → α} (hf : ∀ a b, f a = some b → g b = a) :
    ∀ {as : List α} {bs : List β}, as.mapM f = some bs → bs.map g = as
  | [], bs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | a :: as, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs, rfl⟩ := h
    simp only [List.map_cons, hf a b hb, mapM_inv hf hbs]

/-! ## Units, orderings, texts, identifiers, versions -/

theorem decodeUnit_spec (c : UInt16) : decodeUnit (.int c.toNat) = some c := by
  have := c.toNat_lt
  simp only [decodeUnit, show (0 : Int) ≤ (c.toNat : Int) ∧ (c.toNat : Int) ≤ 65535 by omega]
  simp

theorem unit_of_decodeUnit {v : Value} {c : UInt16} (h : decodeUnit v = some c) :
    Value.int c.toNat = v := by
  unfold decodeUnit at h
  split at h
  · rename_i n
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      congr 1
      simp
      omega
    · cases h
  · cases h

theorem decodeOrdering_spec (o : Ordering) : decodeOrdering (.str (orderingSpec o)) = some o := by
  cases o <;> rfl

theorem ordering_of_decodeOrdering {v : Value} {o : Ordering} (h : decodeOrdering v = some o) :
    Value.str (orderingSpec o) = v := by
  unfold decodeOrdering at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem decodeText_spec (s : List Char) : decodeText (.str (String.ofList s)) = some s := by
  simp [decodeText, String.toList_ofList]

theorem text_of_decodeText {v : Value} {s : List Char} (h : decodeText v = some s) :
    Value.str (String.ofList s) = v := by
  unfold decodeText at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [String.ofList_toList]
  · cases h

theorem decodeIdent_spec (i : Ident) : decodeIdent (identSpec i) = some i := by
  cases i with
  | num n => simp [identSpec, decodeIdent, decodeNat_natSpec]
  | alnum s => simp [identSpec, decodeIdent, String.toList_ofList]

theorem ident_of_decodeIdent {v : Value} {i : Ident} (h : decodeIdent v = some i) :
    identSpec i = v := by
  unfold decodeIdent at h
  split at h
  · rename_i x
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [identSpec, natSpec_of_decodeNat hn]
  · rename_i s
    simp only [Option.some.injEq] at h
    subst h
    simp [identSpec, String.ofList_toList]
  · cases h

theorem decodeVersion_spec (v : Version) : decodeVersion (versionSpec v) = some v := by
  simp only [versionSpec, decodeVersion, Option.bind_eq_bind]
  rw [mapM_map_some decodeText_spec, mapM_map_some decodeIdent_spec]
  simp [decodeNat_natSpec]

theorem version_of_decodeVersion {w : Value} {v : Version} (h : decodeVersion w = some v) :
    versionSpec v = w := by
  unfold decodeVersion at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hbs, M, hMa, m, hma, p, hpa, ps, hps, rfl⟩ := h
    simp only [versionSpec, mapM_inv (fun _ _ hab => text_of_decodeText hab) hbs,
      natSpec_of_decodeNat hMa, natSpec_of_decodeNat hma, natSpec_of_decodeNat hpa,
      mapM_inv (fun _ _ hab => ident_of_decodeIdent hab) hps]
  · cases h

/-! ## The claims -/

theorem decodeVal_valSpec (x : Val) : decodeVal x.ty (valSpec x) = some x := by
  cases x with
  | bytes b => simp [Val.ty, valSpec, decodeVal, bytesSpec_eq, String.toList_ofList, unhex_hexChars]
  | text s => simp [Val.ty, valSpec, decodeVal, String.toList_ofList]
  | utf16 u =>
    simp only [Val.ty, valSpec, decodeVal]
    rw [mapM_map_some decodeUnit_spec]
    rfl
  | nat n => simp [Val.ty, valSpec, decodeVal, decodeNat_natSpec]
  | int i => simp [Val.ty, valSpec, decodeVal, decodeInt_intSpec]
  | ordering o => simp [Val.ty, valSpec, decodeVal, decodeOrdering_spec]
  | version v => simp [Val.ty, valSpec, decodeVal, decodeVersion_spec]

theorem valSpec_of_decodeVal {t : Ty} {v : Value} {x : Val} (h : decodeVal t v = some x) :
    x.ty = t ∧ valSpec x = v := by
  unfold decodeVal at h
  split at h
  · rename_i s
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨rfl, ?_⟩
    simp [valSpec, bytesSpec_eq, hexChars_of_unhex hb, String.ofList_toList]
  · rename_i s
    simp only [Option.some.injEq] at h
    subst h
    simp [Val.ty, valSpec, String.ofList_toList]
  · rename_i xs
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨rfl, ?_⟩
    simp only [valSpec, mapM_inv (fun _ _ hab => unit_of_decodeUnit hab) hu]
  · obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, natSpec_of_decodeNat hn⟩
  · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, intSpec_of_decodeInt hi⟩
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, ordering_of_decodeOrdering ho⟩
  · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, version_of_decodeVersion hw⟩
  · cases h

theorem encodeIdent_eq : encodeIdent = identSpec := by
  funext i
  cases i <;> simp [encodeIdent, identSpec, encodeNat_eq]

theorem val_layout (x : Val) : encodeVal x = valSpec x := by
  cases x with
  | bytes b => simp [encodeVal, valSpec, bytesSpec, FvdepAudit.Hash.Proof.hex_exact]
  | text s => rfl
  | utf16 u => rfl
  | nat n => exact encodeNat_eq n
  | int i => exact encodeInt_eq i
  | ordering o => cases o <;> rfl
  | version v =>
    simp only [encodeVal, encodeVersion, valSpec, versionSpec, encodeNat_eq, encodeIdent_eq]

theorem val_exact :
    ∀ (t : Ty) (v : Value) (x : Val), decodeVal t v = some x ↔ x.ty = t ∧ valSpec x = v := by
  intro t v x
  constructor
  · exact valSpec_of_decodeVal
  · rintro ⟨rfl, rfl⟩
    exact decodeVal_valSpec x

/-! ## Validity: integers, depth, key order -/

theorem natSpec_fit (n : Nat) :
    FvdepAudit.Json.Spec.intsFit (natSpec n) = true ∧
      FvdepAudit.Json.Spec.depth (natSpec n) = 0 ∧
      FvdepAudit.Json.Spec.keysAscend (natSpec n) = true := by
  unfold natSpec
  split
  · rename_i h
    simp only [FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.keysAscend, Int.natAbs_natCast, decide_eq_true_eq, and_true]
    simp only [safe] at h
    simp only [FvdepAudit.Json.Spec.maxInt]
    omega
  · simp [FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.keysAscend]

theorem intSpec_fit (i : Int) :
    FvdepAudit.Json.Spec.intsFit (intSpec i) = true ∧
      FvdepAudit.Json.Spec.depth (intSpec i) = 0 ∧
      FvdepAudit.Json.Spec.keysAscend (intSpec i) = true := by
  unfold intSpec
  split
  · rename_i h
    simp only [FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.keysAscend, decide_eq_true_eq, and_true]
    simp only [safe] at h
    simp only [FvdepAudit.Json.Spec.maxInt]
    omega
  · simp [FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.keysAscend]

theorem units_fit :
    ∀ u : List UInt16,
      FvdepAudit.Json.Spec.intsFitList (u.map fun c => Value.int c.toNat) = true ∧
        FvdepAudit.Json.Spec.depthList (u.map fun c => Value.int c.toNat) = 0 ∧
        FvdepAudit.Json.Spec.keysAscendList (u.map fun c => Value.int c.toNat) = true
  | [] => by
    simp [FvdepAudit.Json.Spec.intsFitList, FvdepAudit.Json.Spec.depthList,
      FvdepAudit.Json.Spec.keysAscendList]
  | c :: u => by
    have hc := c.toNat_lt
    obtain ⟨h1, h2, h3⟩ := units_fit u
    simp only [List.map_cons, FvdepAudit.Json.Spec.intsFitList, FvdepAudit.Json.Spec.depthList,
      FvdepAudit.Json.Spec.keysAscendList, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.keysAscend, h1, h2, h3, Bool.and_true, Int.natAbs_natCast,
      decide_eq_true_eq, Nat.max_def, Nat.le_refl, ↓reduceIte, and_true]
    simp only [FvdepAudit.Json.Spec.maxInt]
    omega

theorem texts_fit :
    ∀ l : List (List Char),
      FvdepAudit.Json.Spec.intsFitList (l.map fun b => Value.str (String.ofList b)) = true ∧
        FvdepAudit.Json.Spec.depthList (l.map fun b => Value.str (String.ofList b)) = 0 ∧
        FvdepAudit.Json.Spec.keysAscendList (l.map fun b => Value.str (String.ofList b)) = true
  | [] => by
    simp [FvdepAudit.Json.Spec.intsFitList, FvdepAudit.Json.Spec.depthList,
      FvdepAudit.Json.Spec.keysAscendList]
  | b :: l => by
    obtain ⟨h1, h2, h3⟩ := texts_fit l
    simp [FvdepAudit.Json.Spec.intsFitList, FvdepAudit.Json.Spec.depthList,
      FvdepAudit.Json.Spec.keysAscendList, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.keysAscend, h1, h2, h3]

theorem ident_fit (i : Ident) :
    FvdepAudit.Json.Spec.intsFit (identSpec i) = true ∧
      FvdepAudit.Json.Spec.depth (identSpec i) = 1 ∧
      FvdepAudit.Json.Spec.keysAscend (identSpec i) = true := by
  cases i with
  | num n =>
    obtain ⟨h1, h2, h3⟩ := natSpec_fit n
    simp [identSpec, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
      FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
      FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers, h1, h2, h3]
  | alnum s =>
    simp [identSpec, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
      FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
      FvdepAudit.Json.Spec.keysAscend, FvdepAudit.Json.Spec.keysAscendMembers]

theorem idents_fit :
    ∀ l : List Ident,
      FvdepAudit.Json.Spec.intsFitList (l.map identSpec) = true ∧
        FvdepAudit.Json.Spec.depthList (l.map identSpec) ≤ 1 ∧
        FvdepAudit.Json.Spec.keysAscendList (l.map identSpec) = true
  | [] => by
    simp [FvdepAudit.Json.Spec.intsFitList, FvdepAudit.Json.Spec.depthList,
      FvdepAudit.Json.Spec.keysAscendList]
  | i :: l => by
    obtain ⟨h1, h2, h3⟩ := idents_fit l
    obtain ⟨k1, k2, k3⟩ := ident_fit i
    simp only [List.map_cons, FvdepAudit.Json.Spec.intsFitList, FvdepAudit.Json.Spec.depthList,
      FvdepAudit.Json.Spec.keysAscendList, h1, h3, k1, k2, k3, Bool.and_self, true_and, and_true]
    omega

theorem val_fit (x : Val) :
    FvdepAudit.Json.Spec.intsFit (valSpec x) = true ∧
      FvdepAudit.Json.Spec.depth (valSpec x) ≤ 3 ∧
      FvdepAudit.Json.Spec.keysAscend (valSpec x) = true := by
  cases x with
  | bytes b =>
    simp [valSpec, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.keysAscend]
  | text s =>
    simp [valSpec, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.keysAscend]
  | utf16 u =>
    obtain ⟨h1, h2, h3⟩ := units_fit u
    exact ⟨h1, (show 1 + FvdepAudit.Json.Spec.depthList _ ≤ 3 by omega), h3⟩
  | nat n =>
    obtain ⟨h1, h2, h3⟩ := natSpec_fit n
    exact ⟨h1, (show FvdepAudit.Json.Spec.depth (natSpec n) ≤ 3 by omega), h3⟩
  | int i =>
    obtain ⟨h1, h2, h3⟩ := intSpec_fit i
    exact ⟨h1, (show FvdepAudit.Json.Spec.depth (intSpec i) ≤ 3 by omega), h3⟩
  | ordering o =>
    simp [valSpec, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.keysAscend]
  | version v =>
    obtain ⟨b1, b2, b3⟩ := texts_fit v.build
    obtain ⟨p1, p2, p3⟩ := idents_fit v.pre
    obtain ⟨M1, M2, M3⟩ := natSpec_fit v.major
    obtain ⟨m1, m2, m3⟩ := natSpec_fit v.minor
    obtain ⟨q1, q2, q3⟩ := natSpec_fit v.patch
    have hk : ["build", "major", "minor", "patch", "pre"].Pairwise (· < ·) := by decide
    simp only [valSpec, versionSpec, FvdepAudit.Json.Spec.intsFit,
      FvdepAudit.Json.Spec.intsFitMembers, FvdepAudit.Json.Spec.depth,
      FvdepAudit.Json.Spec.depthMembers, FvdepAudit.Json.Spec.keysAscend,
      FvdepAudit.Json.Spec.keysAscendMembers, List.map_cons, List.map_nil, b1, b2, b3, p1, p3, M1,
      M2, M3, m1, m2, m3, q1, q2, q3, hk, decide_true, Bool.and_self, true_and, and_true]
    omega

theorem val_valid :
    ∀ x : Val,
      FvdepAudit.Json.Spec.stringsFit (valSpec x) = true →
        FvdepAudit.Json.Spec.Valid (encodeVal x) := by
  intro x hs
  rw [val_layout]
  obtain ⟨h1, h2, h3⟩ := val_fit x
  refine ⟨h1, hs, ?_, h3⟩
  simp only [FvdepAudit.Json.Spec.maxDepth]
  omega

end FvdepAudit.Protocol.Proof
