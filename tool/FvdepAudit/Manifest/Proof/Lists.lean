import FvdepAudit.Json.Proof.Decode.Site
import FvdepAudit.Manifest.Spec

/-! Member-list facts the T3 proofs share: key order, lookups under distinct keys, repeated keys,
and the shipped early-exit helpers against their spec lists. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Manifest FvdepAudit.Manifest.Spec

theorem byKey_eq_sorted (ms : List (String × Tree)) : byKey ms = sorted ms := rfl

theorem byKey_perm (ms : List (String × Tree)) : (byKey ms).Perm ms := List.mergeSort_perm ms _

theorem mem_byKey {ms : List (String × Tree)} {m : String × Tree} : m ∈ byKey ms ↔ m ∈ ms :=
  (byKey_perm ms).mem_iff

theorem byKey_keys_le (ms : List (String × Tree)) : ((byKey ms).map (·.1)).Pairwise (· ≤ ·) := by
  have h :=
    List.pairwise_mergeSort (le := fun a b : String × Tree => decide (a.1 ≤ b.1))
      (fun a b c hab hbc => by
        simpa using Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by simpa using Std.le_total (a := a.1) (b := b.1)) ms
  rw [List.pairwise_map]
  exact h.imp fun hab => of_decide_eq_true hab

theorem keys_nodup_byKey {ms : List (String × Tree)} (hd : (ms.map (·.1)).Nodup) :
    ((byKey ms).map (·.1)).Nodup := ((byKey_perm ms).map (·.1)).nodup_iff.mpr hd

/-- Ascending + distinct = strictly ascending. -/
theorem byKey_keys_lt {ms : List (String × Tree)} (hd : (ms.map (·.1)).Nodup) :
    ((byKey ms).map (·.1)).Pairwise (· < ·) := by
  have hle := byKey_keys_le ms
  have hnd := keys_nodup_byKey hd
  rw [List.Nodup] at hnd
  exact (hle.and hnd).imp fun ⟨h1, h2⟩ => Std.lt_of_le_of_ne h1 h2

variable {β : Type}

theorem lookup_of_mem {ms : List (String × β)} (hd : (ms.map (·.1)).Nodup) {k : String} {v : β}
    (h : (k, v) ∈ ms) : ms.lookup k = some v := by
  induction ms with
  | nil => simp at h
  | cons m ms ih =>
    obtain ⟨a, b⟩ := m
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    rcases List.mem_cons.mp h with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp [List.lookup]
    · have hne : a ≠ k := fun hak => hd.1 ⟨(k, v), hm, hak.symm⟩
      have hb : (k == a) = false := by simpa [beq_iff_eq] using Ne.symm hne
      simp only [List.lookup, hb]
      exact ih hd.2 hm

theorem mem_of_lookup {ms : List (String × β)} {k : String} {v : β} (h : ms.lookup k = some v) :
    (k, v) ∈ ms := by
  obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem lookup_eq_some_iff_mem {ms : List (String × β)} (hd : (ms.map (·.1)).Nodup) {k : String}
    {v : β} : ms.lookup k = some v ↔ (k, v) ∈ ms := ⟨mem_of_lookup, lookup_of_mem hd⟩

theorem lookup_none_iff {ms : List (String × β)} {k : String} :
    ms.lookup k = none ↔ k ∉ ms.map (·.1) := by
  simp only [List.lookup_eq_none_iff, List.mem_map, not_exists, not_and, bne_iff_ne, ne_eq]
  constructor
  · intro h m hm he
    exact h m hm he.symm
  · intro h m hm he
    exact h m hm he.symm

theorem lookup_isSome_iff {ms : List (String × β)} {k : String} :
    (ms.lookup k).isSome ↔ k ∈ ms.map (·.1) := by
  rw [List.lookup_isSome_iff]
  simp only [beq_iff_eq, List.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩

theorem lookup_perm {ms ns : List (String × β)} (hd : (ms.map (·.1)).Nodup) (hp : ns.Perm ms)
    (k : String) : ns.lookup k = ms.lookup k := by
  have hd' : (ns.map (·.1)).Nodup := (hp.map (·.1)).nodup_iff.mpr hd
  cases h : ms.lookup k with
  | none =>
    rw [lookup_none_iff] at h ⊢
    exact fun hm => h ((hp.map (·.1)).mem_iff.mp hm)
  | some v => exact lookup_of_mem hd' (hp.mem_iff.mpr (mem_of_lookup h))

/-! ## Repeated keys -/

theorem repeated_nil_iff (ks : List String) : repeated ks = [] ↔ ks.Nodup := by
  rw [List.nodup_iff_count]
  simp only [repeated, List.filter_eq_nil_iff, decide_eq_true_eq, Nat.not_le]
  constructor
  · intro h k
    by_cases hk : k ∈ ks
    · have := h k hk
      omega
    · rw [List.count_eq_zero.mpr hk]
      omega
  · intro h k _
    have := h k
    omega

theorem repeatedKey_dup (p : List PathSeg) (ms : List (String × Tree)) :
    (repeatedKey ms).map (fun k => (⟨p, .duplicateKey k⟩ : ManifestError)) = dupSpec p ms := by
  have hk : (ms.map fun m => (m.1, Value.null)).map (·.1) = ms.map (·.1) := by simp
  have h := FvdepAudit.Json.Proof.firstRepeat_sort (ms.map fun m => (m.1, Value.null))
  have hr :
    FvdepAudit.Json.Spec.repeatedKeys (ms.map fun m => (m.1, Value.null)) =
      repeated (ms.map (·.1)) := by
    simp only [FvdepAudit.Json.Spec.repeatedKeys, repeated, hk]
  rw [hk, hr] at h
  unfold repeatedKey dupSpec
  rw [h]
  cases repeated (ms.map (·.1)) <;> rfl

theorem dupSpec_none_iff (p : List PathSeg) (ms : List (String × Tree)) :
    dupSpec p ms = none ↔ (ms.map (·.1)).Nodup := by
  rw [← repeated_nil_iff]
  unfold dupSpec
  cases repeated (ms.map (·.1)) <;> simp

theorem repeatedKey_none_iff (ms : List (String × Tree)) :
    repeatedKey ms = none ↔ (ms.map (·.1)).Nodup := by
  rw [← dupSpec_none_iff [] ms, ← repeatedKey_dup]
  cases repeatedKey ms <;> simp

/-! ## Early-exit helpers = the first of their spec lists -/

theorem orElse_eq {α : Type} (a b : Option α) : a.orElse (fun _ => b) = a.or b := by cases a <;> rfl

theorem head?_append' {α : Type} (l₁ l₂ : List α) : (l₁ ++ l₂).head? = l₁.head?.or l₂.head? := by
  cases l₁ <;> rfl

theorem firstKey_eq (bad : String → Bool) (kind : ErrorKind) (p : List PathSeg)
    (ss : List (String × Tree)) :
    firstKey bad kind p ss =
      ((ss.filter fun m => bad m.1).map fun m =>
          (⟨p ++ [.key m.1], kind⟩ : ManifestError)).head? := by
  simp [firstKey, List.head?_map, List.head?_filter]

theorem firstKey_none_iff {bad : String → Bool} {kind : ErrorKind} {p : List PathSeg}
    {ss : List (String × Tree)} : firstKey bad kind p ss = none ↔ ∀ m ∈ ss, bad m.1 = false := by
  simp [firstKey, List.find?_eq_none]

theorem any_key_eq (k : String) :
    ∀ ss : List (String × Tree), ss.any (·.1 == k) = (ss.lookup k).isSome
  | [] => rfl
  | (a, b) :: ss => by
    by_cases h : a = k
    · subst h
      simp [List.lookup]
    · have h' : (k == a) = false := by simpa [beq_iff_eq] using Ne.symm h
      simp [List.lookup, h, h', any_key_eq k ss]

theorem firstMissing_eq (ss : List (String × Tree)) (p : List PathSeg) (req : List String) :
    missingKey ss p req =
      ((req.filter fun k => ss.lookup k = none).map fun k =>
          (⟨p ++ [.key k], .missingField⟩ : ManifestError)).head? := by
  have hf : (fun k => !ss.any (·.1 == k)) = (fun k => decide (ss.lookup k = none)) := by
    funext k
    rw [any_key_eq]
    cases ss.lookup k <;> simp
  simp only [missingKey, hf, List.head?_map, List.head?_filter]

theorem firstMissing_none_iff {ss : List (String × Tree)} {p : List PathSeg} {req : List String} :
    missingKey ss p req = none ↔ ∀ k ∈ req, k ∈ ss.map (·.1) := by
  rw [firstMissing_eq]
  simp only [List.head?_map, Option.map_eq_none_iff, List.head?_eq_none_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq]
  constructor
  · intro h k hk
    exact Classical.byContradiction fun hn => h k hk (lookup_none_iff.mpr hn)
  · intro h k hk hn
    exact lookup_none_iff.mp hn (h k hk)

theorem valuesCheck_eq (f : String → Tree → Option ManifestError)
    (g : String × Tree → List ManifestError) :
    ∀ ss : List (String × Tree),
      (∀ m ∈ ss, f m.1 m.2 = (g m).head?) → valuesCheck f ss = (ss.flatMap g).head?
  | [], _ => rfl
  | (k, v) :: ss, h => by
    simp only [valuesCheck, List.flatMap_cons, orElse_eq, head?_append']
    rw [h (k, v) (by simp), valuesCheck_eq f g ss fun m hm => h m (by simp [hm])]

theorem valuesCheck_none_iff {f : String → Tree → Option ManifestError} :
    ∀ {ss : List (String × Tree)}, valuesCheck f ss = none ↔ ∀ m ∈ ss, f m.1 m.2 = none
  | [] => by simp [valuesCheck]
  | (k, v) :: ss => by
    simp only [valuesCheck, orElse_eq, Option.or_eq_none_iff, List.mem_cons, forall_eq_or_imp]
    rw [valuesCheck_none_iff]

end FvdepAudit.Manifest.Proof
