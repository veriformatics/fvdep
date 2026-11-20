import FvdepAudit.Library.Proof.Record
import FvdepAudit.Oracle.Wire.Spec

/-! Proofs: the internal wire codec (contract `docs/contracts/U5b-oracle.md` W4): the printers =
the spec's layouts, each reader's round trip, the line readers exact (their print check), the
native bridge. -/

namespace FvdepAudit.Oracle.Wire.Proof

open FvdepCore.Protocol FvdepCore.Oracle FvdepAudit.Oracle.Wire.Spec Fvdep.Semver.Version.V1_0_0

/-! ## Digits -/

theorem hexDigit_fin : ∀ d : Fin 16, Wire.hexDigit d.val = hexChar d.val := by decide

theorem hexVal_fin : ∀ d : Fin 16, Wire.hexVal (Wire.hexDigit d.val) = some d.val := by decide

theorem hexDigit_eq (d : Nat) (h : d < 16) : Wire.hexDigit d = hexChar d := hexDigit_fin ⟨d, h⟩

theorem hexVal_hexDigit (d : Nat) (h : d < 16) : Wire.hexVal (Wire.hexDigit d) = some d :=
  hexVal_fin ⟨d, h⟩

/-- No hex digit is a separator. -/
theorem hexDigit_ne_fin :
    ∀ d : Fin 16,
      Wire.hexDigit d.val ≠ ' ' ∧ Wire.hexDigit d.val ≠ '.' ∧ Wire.hexDigit d.val ≠ '/' := by
  decide

theorem hexOf_two (n : Nat) : hexOf 2 n = [hexChar (n / 16 % 16), hexChar (n % 16)] := by
  simp [hexOf, List.range_succ]

theorem hexOf_four (n : Nat) :
    hexOf 4 n =
      [hexChar (n / 4096 % 16), hexChar (n / 256 % 16), hexChar (n / 16 % 16),
        hexChar (n % 16)] := by
  simp [hexOf, List.range_succ]

theorem hexByte_eq (b : UInt8) : Wire.hexByte b = hexOf 2 b.toNat := by
  have hb : b.toNat < 256 := b.toNat_lt
  rw [hexOf_two, Wire.hexByte, Nat.mod_eq_of_lt (show b.toNat / 16 < 16 by omega),
    hexDigit_eq _ (show b.toNat / 16 < 16 by omega), hexDigit_eq _ (Nat.mod_lt _ (by decide))]

theorem hexUnit_eq (u : UInt16) : Wire.hexUnit u = hexOf 4 u.toNat := by
  have hu : u.toNat < 65536 := u.toNat_lt
  rw [hexOf_four, Wire.hexUnit, Nat.mod_eq_of_lt (show u.toNat / 4096 < 16 by omega),
    hexDigit_eq _ (show u.toNat / 4096 < 16 by omega), hexDigit_eq _ (Nat.mod_lt _ (by decide)),
    hexDigit_eq _ (Nat.mod_lt _ (by decide)), hexDigit_eq _ (Nat.mod_lt _ (by decide))]

theorem unhexBytes_hex : ∀ bs : List UInt8, Wire.unhexBytes (bs.flatMap Wire.hexByte) = some bs
  | [] => rfl
  | b :: bs => by
    have hb : b.toNat < 256 := b.toNat_lt
    have hv : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
    simp only [List.flatMap_cons, Wire.hexByte, List.cons_append, List.nil_append, Wire.unhexBytes,
      hexVal_hexDigit _ (show b.toNat / 16 < 16 by omega),
      hexVal_hexDigit _ (Nat.mod_lt b.toNat (show 16 > 0 by decide)), unhexBytes_hex bs, hv]
    simp

theorem unhexUnits_hex : ∀ us : List UInt16, Wire.unhexUnits (us.flatMap Wire.hexUnit) = some us
  | [] => rfl
  | u :: us => by
    have hu : u.toNat < 65536 := u.toNat_lt
    have hv :
      ((u.toNat / 4096 * 16 + u.toNat / 256 % 16) * 16 + u.toNat / 16 % 16) * 16 + u.toNat % 16 =
        u.toNat := by
      omega
    simp only [List.flatMap_cons, Wire.hexUnit, List.cons_append, List.nil_append, Wire.unhexUnits,
      hexVal_hexDigit _ (show u.toNat / 4096 < 16 by omega),
      hexVal_hexDigit _ (Nat.mod_lt (u.toNat / 256) (show 16 > 0 by decide)),
      hexVal_hexDigit _ (Nat.mod_lt (u.toNat / 16) (show 16 > 0 by decide)),
      hexVal_hexDigit _ (Nat.mod_lt u.toNat (show 16 > 0 by decide)), unhexUnits_hex us, hv]
    simp

theorem mem_hexByte {c : Char} {b : UInt8} (h : c ∈ Wire.hexByte b) :
    c ≠ ' ' ∧ c ≠ '.' ∧ c ≠ '/' := by
  have hb : b.toNat < 256 := b.toNat_lt
  simp only [Wire.hexByte, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact hexDigit_ne_fin ⟨b.toNat / 16, by omega⟩
  · exact hexDigit_ne_fin ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩

theorem mem_hexUnit {c : Char} {u : UInt16} (h : c ∈ Wire.hexUnit u) :
    c ≠ ' ' ∧ c ≠ '.' ∧ c ≠ '/' := by
  have hu : u.toNat < 65536 := u.toNat_lt
  simp only [Wire.hexUnit, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact hexDigit_ne_fin ⟨u.toNat / 4096, by omega⟩
  · exact hexDigit_ne_fin ⟨u.toNat / 256 % 16, Nat.mod_lt _ (by decide)⟩
  · exact hexDigit_ne_fin ⟨u.toNat / 16 % 16, Nat.mod_lt _ (by decide)⟩
  · exact hexDigit_ne_fin ⟨u.toNat % 16, Nat.mod_lt _ (by decide)⟩

theorem mem_hex {c : Char} {bs : List UInt8} (h : c ∈ bs.flatMap Wire.hexByte) :
    c ≠ ' ' ∧ c ≠ '.' ∧ c ≠ '/' := by
  obtain ⟨b, -, hc⟩ := List.mem_flatMap.1 h
  exact mem_hexByte hc

/-! ## Decimals -/

theorem decimal_eq (n : Nat) : Wire.decimal n = FvdepCore.Ids.decimal n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold Wire.decimal FvdepCore.Ids.decimal
    by_cases h : n < 10
    · simp only [h, ↓reduceDIte, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceDIte, ↓reduceIte]
      rw [ih (n / 10) (by omega)]
      rfl

theorem digit_fin :
    ∀ d : Fin 10,
      Wire.decVal (FvdepCore.Ids.digit d.val) = some d.val ∧
        FvdepCore.Ids.digit d.val ≠ ' ' ∧
        FvdepCore.Ids.digit d.val ≠ '.' ∧
        FvdepCore.Ids.digit d.val ≠ '/' ∧ FvdepCore.Ids.digit d.val ≠ '-' := by
  decide

theorem readDigits_digits (acc : Nat) :
    ∀ cs : List Char,
      (∀ c ∈ cs, ∃ d : Fin 10, c = FvdepCore.Ids.digit d.val) →
        Wire.readDigits acc cs = some (cs.foldl (fun a c => 10 * a + (c.toNat - 48)) acc)
  | [], _ => rfl
  | c :: cs, h => by
    obtain ⟨d, rfl⟩ := h c (List.mem_cons_self ..)
    have hrest : ∀ c' ∈ cs, ∃ d : Fin 10, c' = FvdepCore.Ids.digit d.val := fun c' hc' =>
      h c' (List.mem_cons_of_mem _ hc')
    simp only [Wire.readDigits, (digit_fin d).1, List.foldl_cons]
    rw [readDigits_digits _ cs hrest, FvdepCore.Ids.digit_toNat d]
    congr 2
    omega

theorem readDecimal_decimal (n : Nat) : Wire.readDecimal (Wire.decimal n) = some n := by
  rw [decimal_eq]
  have hv := readDigits_digits 0 (FvdepCore.Ids.decimal n) (FvdepAudit.Library.Proof.mem_decimal n)
  have hval := FvdepCore.Ids.value_decimal n
  unfold FvdepCore.Ids.value at hval
  cases hd : FvdepCore.Ids.decimal n with
  | nil => exact absurd hd (FvdepAudit.Library.Proof.decimal_ne_nil n)
  | cons c cs =>
    simp only [Wire.readDecimal]
    rw [← hd, hv, hval]

theorem mem_decimal {c : Char} {n : Nat} (h : c ∈ Wire.decimal n) :
    c ≠ ' ' ∧ c ≠ '.' ∧ c ≠ '/' ∧ c ≠ '-' := by
  rw [decimal_eq] at h
  obtain ⟨d, rfl⟩ := FvdepAudit.Library.Proof.mem_decimal n c h
  exact (digit_fin d).2

/-! ## UTF-8 -/

theorem utf8_eq (cs : List Char) : Wire.utf8 cs = utf8Bytes cs := by
  simp only [Wire.utf8, utf8Bytes, String.toUTF8_eq_toByteArray]
  rw [← String.utf8Encode_toList, String.toList_ofList]

theorem unutf8_utf8 (cs : List Char) : Wire.unutf8 (Wire.utf8 cs) = some cs := by
  rw [utf8_eq]
  have e : ByteArray.mk (utf8Bytes cs).toArray = cs.utf8Encode :=
    congrArg ByteArray.mk Array.toArray_toList
  simp only [Wire.unutf8, e, List.utf8Decode?_utf8Encode, Option.map_some]

/-! ## Splitting + joining -/

theorem splitOn_single (sep : Char) : ∀ p : List Char, sep ∉ p → Wire.splitOn sep p = [p]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : sep ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp only [Wire.splitOn, beq_iff_eq, hc, ↓reduceIte, splitOn_single sep cs hcs]

theorem splitOn_append (sep : Char) (rest : List Char) :
    ∀ p : List Char, sep ∉ p → Wire.splitOn sep (p ++ sep :: rest) = p :: Wire.splitOn sep rest
  | [], _ => by simp [Wire.splitOn]
  | c :: cs, h => by
    have hc : c ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : sep ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp only [List.cons_append, Wire.splitOn, beq_iff_eq, hc, ↓reduceIte,
      splitOn_append sep rest cs hcs]

theorem splitOn_joinWith (sep : Char) :
    ∀ ps : List (List Char),
      ps ≠ [] → (∀ p ∈ ps, sep ∉ p) → Wire.splitOn sep (Wire.joinWith sep ps) = ps
  | [], h, _ => absurd rfl h
  | [p], _, hp => by simp [Wire.joinWith, splitOn_single sep p (hp p (by simp))]
  | p :: q :: rest, _, hp => by
    simp only [Wire.joinWith]
    rw [splitOn_append sep _ p (hp p (by simp)),
      splitOn_joinWith sep (q :: rest) (by simp) fun r hr => hp r (by simp [hr])]

theorem joinWith_eq (sep : Char) : ∀ ps : List (List Char), Wire.joinWith sep ps = joined sep ps
  | [] => rfl
  | [p] => by simp [Wire.joinWith, joined]
  | p :: q :: rest => by
    simp only [Wire.joinWith, joined, joinWith_eq sep (q :: rest), List.flatMap_cons,
      List.cons_append]

theorem mem_joinWith {c sep : Char} :
    ∀ {ps : List (List Char)}, c ∈ Wire.joinWith sep ps → c = sep ∨ ∃ p ∈ ps, c ∈ p
  | [], h => by simp [Wire.joinWith] at h
  | [p], h => Or.inr ⟨p, by simp, by simpa [Wire.joinWith] using h⟩
  | p :: q :: rest, h => by
    simp only [Wire.joinWith, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr ⟨p, by simp, h⟩
    · exact Or.inl h
    · rcases mem_joinWith h with h | ⟨r, hr, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, by simp [hr], hc⟩

theorem joinWith_ne_nil {sep : Char} :
    ∀ {ps : List (List Char)}, (∃ p ∈ ps, p ≠ []) → Wire.joinWith sep ps ≠ []
  | [], ⟨_, h, _⟩ => by simp at h
  | [p], ⟨_, h, hne⟩ => by
    simp only [List.mem_singleton] at h
    subst h
    simpa [Wire.joinWith] using hne
  | p :: q :: rest, _ => by simp [Wire.joinWith]

/-! ## Tokens: printers = layouts -/

theorem hexByte_fun : Wire.hexByte = fun b => hexOf 2 b.toNat := funext hexByte_eq

theorem hexUnit_fun : Wire.hexUnit = fun u => hexOf 4 u.toNat := funext hexUnit_eq

theorem identPayload_eq : ∀ i : Ident, Wire.identPayload i = identLayout i
  | .num n => by simp [Wire.identPayload, identLayout, dec, decimal_eq]
  | .alnum s => by simp [Wire.identPayload, identLayout, hexBytes, utf8_eq, hexByte_fun]

theorem buildPayload_eq (s : List Char) : Wire.buildPayload s = buildLayout s := by
  simp [Wire.buildPayload, buildLayout, hexBytes, utf8_eq, hexByte_fun]

theorem joined_cons (sep : Char) (p : List Char) (ps : List (List Char)) :
    joined sep (p :: ps) = p ++ ps.flatMap fun q => sep :: q := rfl

theorem versionPayload_eq (v : Version) : Wire.versionPayload v = versionLayout v := by
  have hi : v.pre.map Wire.identPayload = v.pre.map identLayout :=
    List.map_congr_left fun i _ => identPayload_eq i
  have hb : v.build.map Wire.buildPayload = v.build.map buildLayout :=
    List.map_congr_left fun s _ => buildPayload_eq s
  simp [Wire.versionPayload, Wire.dotted, joinWith_eq, hi, hb, versionLayout, dec, decimal_eq,
    joined_cons]

theorem token_eq : ∀ v : Val, Wire.token v = tokenLayout v
  | .bytes b => by simp [Wire.token, tokenLayout, hexBytes, hexByte_fun]
  | .text s => by simp [Wire.token, tokenLayout, hexBytes, hexByte_fun, utf8_eq]
  | .utf16 u => by simp [Wire.token, tokenLayout, hexUnit_fun]
  | .nat n => by simp [Wire.token, tokenLayout, dec, decimal_eq]
  | .int i => by simp [Wire.token, tokenLayout, intLayout, dec, decimal_eq]
  | .ordering o => by cases o <;> rfl
  | .version v => by simp [Wire.token, tokenLayout, versionPayload_eq]

/-! ## Tokens: separator-free pieces -/

theorem identPayload_safe : ∀ (i : Ident), ∀ c ∈ Wire.identPayload i, c ≠ ' ' ∧ c ≠ '.' ∧ c ≠ '/'
  | .num n, c, h => by
    simp only [Wire.identPayload, List.mem_cons] at h
    rcases h with rfl | h
    · decide
    · exact ⟨(mem_decimal h).1, (mem_decimal h).2.1, (mem_decimal h).2.2.1⟩
  | .alnum s, c, h => by
    simp only [Wire.identPayload, List.mem_cons] at h
    rcases h with rfl | h
    · decide
    · exact mem_hex h

theorem buildPayload_safe (s : List Char) :
    ∀ c ∈ Wire.buildPayload s, c ≠ ' ' ∧ c ≠ '.' ∧ c ≠ '/' := by
  intro c h
  simp only [Wire.buildPayload, List.mem_cons] at h
  rcases h with rfl | h
  · decide
  · exact mem_hex h

theorem dotted_safe {ps : List (List Char)} (h : ∀ p ∈ ps, ∀ c ∈ p, c ≠ ' ' ∧ c ≠ '/') :
    ∀ c ∈ Wire.dotted ps, c ≠ ' ' ∧ c ≠ '/' := by
  intro c hc
  rcases mem_joinWith hc with rfl | ⟨p, hp, hcp⟩
  · decide
  · exact h p hp c hcp

theorem versionPayload_safe (v : Version) : ∀ c ∈ Wire.versionPayload v, c ≠ ' ' := by
  intro c hc
  rcases mem_joinWith hc with rfl | ⟨p, hp, hcp⟩
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rcases mem_joinWith hcp with rfl | ⟨q, hq, hcq⟩
      · decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact (mem_decimal hcq).1
    · exact
        (dotted_safe
            (fun p hp c hc => by
              obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
              exact ⟨(identPayload_safe i c hc).1, (identPayload_safe i c hc).2.2⟩)
            c hcp).1
    · exact
        (dotted_safe
            (fun p hp c hc => by
              obtain ⟨s, -, rfl⟩ := List.mem_map.1 hp
              exact ⟨(buildPayload_safe s c hc).1, (buildPayload_safe s c hc).2.2⟩)
            c hcp).1

theorem token_safe : ∀ v : Val, ' ' ∉ Wire.token v
  | .bytes b, h => by
    simp only [Wire.token, List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (mem_hex h).1 rfl
  | .text s, h => by
    simp only [Wire.token, List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (mem_hex h).1 rfl
  | .utf16 u, h => by
    simp only [Wire.token, List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 h
      exact (mem_hexUnit hx).1 rfl
  | .nat n, h => by
    simp only [Wire.token, List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (mem_decimal h).1 rfl
  | .int i, h => by
    simp only [Wire.token, List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · split at h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by decide)
        · exact (mem_decimal h).1 rfl
      · exact (mem_decimal h).1 rfl
  | .ordering o, h => by cases o <;> simp [Wire.token] at h
  | .version v, h => by
    simp only [Wire.token, List.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact versionPayload_safe v ' ' h rfl

/-! ## Tokens: round trips -/

theorem mapM_map {α : Type} (read : List Char → Option α) (f : α → List Char)
    (hf : ∀ x, read (f x) = some x) : ∀ xs : List α, (xs.map f).mapM read = some xs
  | [] => rfl
  | x :: xs => by simp [List.mapM_cons, hf x, mapM_map read f hf xs]

theorem readDotted_dotted {α : Type} (read : List Char → Option α) (f : α → List Char)
    (hf : ∀ x, read (f x) = some x) (hne : ∀ x, f x ≠ []) (hsafe : ∀ x, '.' ∉ f x) :
    ∀ xs : List α, Wire.readDotted read (Wire.dotted (xs.map f)) = some xs
  | [] => rfl
  | x :: xs => by
    have hj : Wire.dotted ((x :: xs).map f) ≠ [] := joinWith_ne_nil ⟨f x, by simp, hne x⟩
    have hsplit : Wire.splitOn '.' (Wire.dotted ((x :: xs).map f)) = (x :: xs).map f :=
      splitOn_joinWith '.' _ (by simp) fun p hp => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
        exact hsafe y
    generalize hd : Wire.dotted ((x :: xs).map f) = d at hj hsplit
    cases d with
    | nil => exact absurd rfl hj
    | cons c cs =>
      simp only [Wire.readDotted]
      rw [hsplit, mapM_map read f hf]

theorem readIdent_payload : ∀ i : Ident, Wire.readIdent (Wire.identPayload i) = some i
  | .num n => by simp [Wire.identPayload, Wire.readIdent, readDecimal_decimal]
  | .alnum s => by simp [Wire.identPayload, Wire.readIdent, unhexBytes_hex, unutf8_utf8]

theorem readBuild_payload (s : List Char) : Wire.readBuild (Wire.buildPayload s) = some s := by
  simp [Wire.buildPayload, Wire.readBuild, unhexBytes_hex, unutf8_utf8]

theorem readVersion_payload (v : Version) : Wire.readVersion (Wire.versionPayload v) = some v := by
  obtain ⟨a, b, c, pre, build⟩ := v
  have hdec : ∀ n, '.' ∉ Wire.decimal n ∧ '/' ∉ Wire.decimal n := fun n =>
    ⟨fun h => (mem_decimal h).2.1 rfl, fun h => (mem_decimal h).2.2.1 rfl⟩
  have hcore :
    Wire.splitOn '.' (Wire.joinWith '.' [Wire.decimal a, Wire.decimal b, Wire.decimal c]) =
      [Wire.decimal a, Wire.decimal b, Wire.decimal c] :=
    splitOn_joinWith '.' _ (by simp) fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact (hdec _).1
  have hsafe :
    ∀
      p ∈
        [Wire.joinWith '.' [Wire.decimal a, Wire.decimal b, Wire.decimal c],
          Wire.dotted (pre.map Wire.identPayload), Wire.dotted (build.map Wire.buildPayload)],
      '/' ∉ p := by
    intro p hp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rcases mem_joinWith h with h | ⟨q, hq, hcq⟩
      · exact absurd h (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact (hdec _).2 hcq
    · exact
        (dotted_safe
              (fun p hp c hc => by
                obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
                exact ⟨(identPayload_safe i c hc).1, (identPayload_safe i c hc).2.2⟩)
              '/' h).2
          rfl
    · exact
        (dotted_safe
              (fun p hp c hc => by
                obtain ⟨s, -, rfl⟩ := List.mem_map.1 hp
                exact ⟨(buildPayload_safe s c hc).1, (buildPayload_safe s c hc).2.2⟩)
              '/' h).2
          rfl
  have hp :=
    readDotted_dotted Wire.readIdent Wire.identPayload readIdent_payload
      (fun i => by cases i <;> simp [Wire.identPayload])
      (fun i h => (identPayload_safe i '.' h).2.1 rfl) pre
  have hb :=
    readDotted_dotted Wire.readBuild Wire.buildPayload readBuild_payload
      (fun s => by simp [Wire.buildPayload]) (fun s h => (buildPayload_safe s '.' h).2.1 rfl) build
  simp only [Wire.readVersion, Wire.versionPayload, splitOn_joinWith '/' _ (by simp) hsafe, hcore,
    readDecimal_decimal, hp, hb]

theorem readToken_token : ∀ v : Val, Wire.readToken v.ty (Wire.token v) = some v
  | .bytes b => by simp [Val.ty, Wire.token, Wire.readToken, unhexBytes_hex]
  | .text s => by simp [Val.ty, Wire.token, Wire.readToken, unhexBytes_hex, unutf8_utf8]
  | .utf16 u => by simp [Val.ty, Wire.token, Wire.readToken, unhexUnits_hex]
  | .nat n => by simp [Val.ty, Wire.token, Wire.readToken, readDecimal_decimal]
  | .int (.ofNat n) => by
    have hd := readDecimal_decimal n
    have htok : Wire.token (.int (.ofNat n)) = 'i' :: ':' :: Wire.decimal n := by simp [Wire.token]
    rw [htok]
    cases hc : Wire.decimal n with
    | nil =>
      rw [hc] at hd
      simp [Wire.readDecimal] at hd
    | cons c
      cs =>
      have hcm : c ≠ '-' :=
        (mem_decimal
            (show c ∈ Wire.decimal n by
              rw [hc]; simp)).2.2.2
      rw [hc] at hd
      simp [Val.ty, Wire.readToken, hcm, hd]
  | .int (.negSucc k) => by
    have h1 : ((k : Int) + 1).natAbs = k + 1 := rfl
    simp [Val.ty, Wire.token, Wire.readToken, readDecimal_decimal, Int.negSucc_eq, h1]
  | .ordering o => by cases o <;> rfl
  | .version v => by simp [Val.ty, Wire.token, Wire.readToken, readVersion_payload]

/-! ## Lines (W1–W2) -/

theorem encodeArgs_eq (xs : List Val) : Wire.encodeArgs xs = argsLayout xs := by
  simp only [Wire.encodeArgs, argsLayout, joinWith_eq]
  congr 2
  exact List.map_congr_left fun v _ => token_eq v

theorem zip_mapM :
    ∀ xs : List Val,
      ((xs.map Val.ty).zip (xs.map Wire.token)).mapM (fun p => Wire.readToken p.1 p.2) = some xs
  | [] => rfl
  | x :: xs => by simp [List.mapM_cons, readToken_token x, zip_mapM xs]

theorem readArgs_encode (xs : List Val) :
    Wire.readArgs (xs.map Val.ty) (Wire.encodeArgs xs) = some xs := by
  cases xs with
  | nil => simp [Wire.readArgs, Wire.encodeArgs, Wire.joinWith]
  | cons x
    xs =>
    have hsplit :=
      splitOn_joinWith ' ' ((x :: xs).map Wire.token) (by simp) fun p hp => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hp
        exact token_safe v
    have hz := zip_mapM (x :: xs)
    simp only [List.map_cons] at hsplit hz
    simp only [Wire.readArgs, Wire.encodeArgs, List.map_cons, String.toList_ofList, hsplit,
      List.length_cons, List.length_map, beq_self_eq_true, ↓reduceIte, hz]

/-- W4 `argsExact`: a request line reads as `xs` exactly when `xs` has the types `ts` + the line is
`xs`'s layout. -/
theorem decodeArgs_exact (ts : List Ty) (s : String) (xs : List Val) :
    Wire.decodeArgs ts s = some xs ↔ xs.map Val.ty = ts ∧ s = argsLayout xs := by
  constructor
  · intro h
    unfold Wire.decodeArgs at h
    split at h
    · rename_i ys _
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨hc.1, by rw [← hc.2, encodeArgs_eq]⟩
      · cases h
    · cases h
  · rintro ⟨rfl, rfl⟩
    unfold Wire.decodeArgs
    rw [← encodeArgs_eq, readArgs_encode]
    simp

theorem printResult_eq (v : Val) : Wire.printResult v = resultLayout (.ok v) := by
  simp [Wire.printResult, resultLayout, token_eq]

theorem printNone_eq : Wire.printNone = resultLayout .err := rfl

theorem resultLine_eq : ∀ r : Reply, Wire.resultLine r = resultLayout r
  | .ok v => printResult_eq v
  | .err => rfl
  | .invalid _ => rfl

theorem admits_iff : ∀ (rt : RTy) (r : Reply), Wire.admits rt r = true ↔ Typed rt r
  | .plain t, .ok v => by simp [Wire.admits, Typed]
  | .option t, .ok v => by simp [Wire.admits, Typed]
  | .option _, .err => by simp [Wire.admits, Typed]
  | .plain _, .err => by simp [Wire.admits, Typed]
  | .plain _, .invalid _ => by simp [Wire.admits, Typed]
  | .option _, .invalid _ => by simp [Wire.admits, Typed]

theorem readResult_line :
    ∀ (rt : RTy) (r : Reply), Typed rt r → Wire.readResult rt (Wire.resultLine r) = some r
  | .plain t, .ok v, h => by
    simp only [Typed] at h
    subst h
    simp [Wire.readResult, Wire.resultLine, Wire.printResult, readToken_token]
  | .option t, .ok v, h => by
    simp only [Typed] at h
    subst h
    simp [Wire.readResult, Wire.resultLine, Wire.printResult, readToken_token]
  | .option _, .err, _ => by simp [Wire.readResult, Wire.resultLine, Wire.printNone]
  | .plain _, .err, h => by simp [Typed] at h
  | .plain _, .invalid _, h => by simp [Typed] at h
  | .option _, .invalid _, h => by simp [Typed] at h

/-- W4 `resultExact`: a result line reads as `r` exactly when the result type admits `r` + the line
is `r`'s layout. -/
theorem parseResult_exact (rt : RTy) (s : String) (r : Reply) :
    Wire.parseResult rt s = some r ↔ Typed rt r ∧ s = resultLayout r := by
  constructor
  · intro h
    unfold Wire.parseResult at h
    split at h
    · split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨(admits_iff rt _).1 hc.1, by rw [← hc.2, resultLine_eq]⟩
      · cases h
    · cases h
  · rintro ⟨ht, rfl⟩
    unfold Wire.parseResult
    rw [← resultLine_eq, readResult_line rt r ht]
    simp [(admits_iff rt r).2 ht]

/-! ## The native bridge (W3) -/

theorem native_bytes (v : Val) (x : List UInt8) :
    (Wire.Native.ofVal v : Option (List UInt8)) = some x ↔ v = Wire.Native.toVal x := by
  cases v <;> simp [Wire.Native.ofVal, Wire.Native.toVal, eq_comm]

theorem native_byteArray (v : Val) (x : ByteArray) :
    (Wire.Native.ofVal v : Option ByteArray) = some x ↔ v = Wire.Native.toVal x := by
  cases v with
  | bytes
    b =>
    simp only [Wire.Native.ofVal, Wire.Native.toVal, Option.some.injEq, Val.bytes.injEq]
    constructor
    · rintro rfl
      simp
    · rintro rfl
      rfl
  | _ => simp [Wire.Native.ofVal, Wire.Native.toVal]

theorem native_text (v : Val) (x : List Char) :
    (Wire.Native.ofVal v : Option (List Char)) = some x ↔ v = Wire.Native.toVal x := by
  cases v <;> simp [Wire.Native.ofVal, Wire.Native.toVal, eq_comm]

theorem native_utf16 (v : Val) (x : List UInt16) :
    (Wire.Native.ofVal v : Option (List UInt16)) = some x ↔ v = Wire.Native.toVal x := by
  cases v <;> simp [Wire.Native.ofVal, Wire.Native.toVal, eq_comm]

theorem native_nat (v : Val) (x : Nat) :
    (Wire.Native.ofVal v : Option Nat) = some x ↔ v = Wire.Native.toVal x := by
  cases v <;> simp [Wire.Native.ofVal, Wire.Native.toVal, eq_comm]

theorem native_int (v : Val) (x : Int) :
    (Wire.Native.ofVal v : Option Int) = some x ↔ v = Wire.Native.toVal x := by
  cases v <;> simp [Wire.Native.ofVal, Wire.Native.toVal, eq_comm]

theorem native_ordering (v : Val) (x : Ordering) :
    (Wire.Native.ofVal v : Option Ordering) = some x ↔ v = Wire.Native.toVal x := by
  cases v <;> simp [Wire.Native.ofVal, Wire.Native.toVal, eq_comm]

theorem native_version (v : Val) (x : Version) :
    (Wire.Native.ofVal v : Option Version) = some x ↔ v = Wire.Native.toVal x := by
  cases v <;> simp [Wire.Native.ofVal, Wire.Native.toVal, eq_comm]

/-- W4 `nativeExact`'s types: each served representation's values carry its protocol type. -/
theorem native_tys :
    (∀ x : List UInt8, (Wire.Native.toVal x).ty = Wire.Native.ty (List UInt8)) ∧
      (∀ x : ByteArray, (Wire.Native.toVal x).ty = Wire.Native.ty ByteArray) ∧
      (∀ x : List Char, (Wire.Native.toVal x).ty = Wire.Native.ty (List Char)) ∧
      (∀ x : List UInt16, (Wire.Native.toVal x).ty = Wire.Native.ty (List UInt16)) ∧
      (∀ x : Nat, (Wire.Native.toVal x).ty = Wire.Native.ty Nat) ∧
      (∀ x : Int, (Wire.Native.toVal x).ty = Wire.Native.ty Int) ∧
      (∀ x : Ordering, (Wire.Native.toVal x).ty = Wire.Native.ty Ordering) ∧
      ∀ x : Version, (Wire.Native.toVal x).ty = Wire.Native.ty Version :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩

/-- W3 + W4 `nativeValues`: each representation's value is its protocol value: the bytes, characters
+ code units in order, the number, the ordering, the version itself (with `nativeExact`, `ofVal` is
pinned too: no reordering pair passes). -/
theorem native_values :
    (∀ x : List UInt8, Wire.Native.toVal x = Val.bytes x) ∧
      (∀ x : ByteArray, Wire.Native.toVal x = Val.bytes x.data.toList) ∧
      (∀ x : List Char, Wire.Native.toVal x = Val.text x) ∧
      (∀ x : List UInt16, Wire.Native.toVal x = Val.utf16 x) ∧
      (∀ x : Nat, Wire.Native.toVal x = Val.nat x) ∧
      (∀ x : Int, Wire.Native.toVal x = Val.int x) ∧
      (∀ x : Ordering, Wire.Native.toVal x = Val.ordering x) ∧
      ∀ x : Version, Wire.Native.toVal x = Val.version x :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩

end FvdepAudit.Oracle.Wire.Proof
