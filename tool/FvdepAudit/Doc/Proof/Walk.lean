import FvdepAudit.Doc.Proof.Rules

/-! The shipped early-exit walk reports the first of the spec's violations, for every schema +
value (`walk_eq`). -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc FvdepAudit.Doc.Spec

theorem find_map_eq_lookup {β : Type} (k : String) :
    ∀ xs : List (String × β), (xs.find? (·.1 == k)).map (·.2) = xs.lookup k
  | [] => rfl
  | (a, b) :: xs => by
    by_cases h : a = k
    · subst h
      simp [List.lookup]
    · have h' : (k == a) = false := by simpa [beq_iff_eq] using Ne.symm h
      simp [List.lookup, h, h', find_map_eq_lookup k xs]

theorem member_eq (ms : List (String × Value)) (k : String) : member? ms k = ms.lookup k :=
  find_map_eq_lookup k ms

theorem resolve_eq (tag : String) (t : Ty) : resolve tag t = resolveSpec tag t := by
  cases t <;> simp [resolve, resolveSpec, find_map_eq_lookup]

theorem disc_eq (tag : String) (p : List PathSeg) (ms : List (String × Value)) (d : Option Disc) :
    discCheck tag p ms d = discSpec tag p ms d := by
  rcases d with _ | ⟨k, n⟩ | ⟨k, xs⟩
  · rfl
  · simp only [discCheck, discSpec, member_eq]
    cases ms.lookup k with
    | none => rfl
    | some x => cases x <;> simp [kindOf]
  · simp only [discCheck, discSpec, member_eq]
    cases ms.lookup k with
    | none => rfl
    | some x => cases x <;> simp

theorem unknown_eq (known : List String) (p : List PathSeg) :
    ∀ ms, firstUnknown known p ms = (unknownSpec known p ms).head?
  | [] => rfl
  | (k, x) :: ms => by
    by_cases h : k ∈ known
    · simp [firstUnknown, unknownSpec, h, unknown_eq known p ms]
    · simp [firstUnknown, unknownSpec, h]

theorem any_key_eq (k : String) :
    ∀ ms : List (String × Value), ms.any (·.1 == k) = (ms.lookup k).isSome
  | [] => rfl
  | (a, b) :: ms => by
    by_cases h : a = k
    · subst h
      simp [List.lookup]
    · have h' : (k == a) = false := by simpa [beq_iff_eq] using Ne.symm h
      simp [List.lookup, h, h', any_key_eq k ms]

theorem missing_eq (ms : List (String × Value)) (p : List PathSeg) :
    ∀ keys, firstMissing ms p keys = (missingSpec ms p keys).head?
  | [] => rfl
  | k :: ks => by
    by_cases h : (ms.lookup k).isSome = true
    · have hn : ms.lookup k ≠ none := Option.isSome_iff_ne_none.mp h
      simp only [firstMissing, missingSpec, any_key_eq, h, ite_true, List.filter_cons, hn,
        decide_false, Bool.false_eq_true, ite_false]
      exact missing_eq ms p ks
    · have hn : ms.lookup k = none := Option.not_isSome_iff_eq_none.mp h
      simp [firstMissing, missingSpec, any_key_eq, hn]

theorem leaf_eq (ks : List JKind) (r : Rule) (p : List PathSeg) (v : Value) :
    leaf ks r p v = (leafSpec ks r p v).head? := by
  unfold leaf leafSpec
  by_cases hk : kindOf v ∈ ks
  · by_cases hr : ruleHolds r v
    · simp [hk, hr, (check_iff r v).mpr hr]
    · have hc : r.check v = false := Bool.eq_false_iff.mpr fun hc => hr ((check_iff r v).mp hc)
      simp [hk, hr, hc]
  · simp [hk]

theorem kindMiss_eq (ks : List JKind) (p : List PathSeg) (v : Value) :
    kindMiss ks p v = (kindMissSpec ks p v).head? := by
  unfold kindMiss kindMissSpec
  by_cases hk : kindOf v ∈ ks <;> simp [hk]

theorem valueAt_eq : ∀ (path : List String) (v : Value), valueAt path v = atPath path v
  | [], _ => rfl
  | k :: ks, .obj ms => by
    simp only [valueAt, atPath, member_eq]
    cases ms.lookup k with
    | none => rfl
    | some x => exact valueAt_eq ks x
  | _ :: _, .null | _ :: _, .bool _ | _ :: _, .int _ | _ :: _, .str _ | _ :: _, .arr _ => rfl

theorem ascending_eq (p : List PathSeg) (path : List String) :
    ∀ (i : Nat) (xs : List Value),
      Order.check.ascendingFrom p path i xs = (descentsSpec p path i xs).head?
  | _, [] => rfl
  | _, [_] => rfl
  | i, a :: b :: rest => by
    have ih := ascending_eq p path (i + 1) (b :: rest)
    simp only [Order.check.ascendingFrom, descentsSpec, valueAt_eq]
    cases atPath path a with
    | none => simpa using ih
    | some va =>
      cases atPath path b with
      | none => cases va <;> simpa using ih
      | some vb =>
        cases va <;> cases vb <;> try simpa using ih
        rename_i x y
        by_cases h : x < y
        · simpa [h] using ih
        · simp [h]

theorem orElse_eq {α : Type} (a b : Option α) : a.orElse (fun _ => b) = a.or b := by cases a <;> rfl

theorem head?_append' {α : Type} (l₁ l₂ : List α) : (l₁ ++ l₂).head? = l₁.head?.or l₂.head? := by
  cases l₁ <;> rfl

theorem strsOf_eq_spec : ∀ xs : List Value, strsOf xs = strsSpec xs
  | [] => rfl
  | .str s :: xs => by simp [strsOf, strsSpec, strsOf_eq_spec xs]
  | .null :: _ | .bool _ :: _ | .int _ :: _ | .arr _ :: _ | .obj _ :: _ => rfl

theorem unique_eq (p : List PathSeg) (path : List String) :
    ∀ (i : Nat) (seen : List String) (xs : List Value),
      Order.check.uniqueFrom p path i seen xs = (nameRepeatsSpec p path i seen xs).head?
  | _, _, [] => rfl
  | i, seen, x :: xs => by
    have ih := unique_eq p path (i + 1) seen xs
    simp only [Order.check.uniqueFrom, nameRepeatsSpec, valueAt_eq]
    cases atPath path x with
    | none => exact ih
    | some v =>
      cases v with
      | str s =>
        by_cases h : s ∈ seen
        · simp [h]
        · simp [h, unique_eq p path (i + 1) (s :: seen) xs]
      | null => exact ih
      | bool _ => exact ih
      | int _ => exact ih
      | arr _ => exact ih
      | obj _ => exact ih

theorem cmp_lt_iff (x y : EntryVersion) : x.cmp y = .lt ↔ VersionBefore x y := by
  cases x with
  | mk a b c =>
    cases y with
    | mk a' b' c' =>
      have h₁ := cmp3_spec a a'
      have h₂ := cmp3_spec b b'
      have h₃ := cmp3_spec c c'
      simp only [EntryVersion.cmp, VersionBefore]
      cases hx : cmp3 a a' <;> cases hy : cmp3 b b' <;> cases hz : cmp3 c c' <;> simp_all

theorem idVersionBefore_iff (ia va ib vb : String) :
    idVersionBefore ia va ib vb = true ↔ IdVersionBefore ia va ib vb := by
  unfold idVersionBefore IdVersionBefore
  cases EntryVersion.parse va <;> cases EntryVersion.parse vb <;> simp [cmp_lt_iff]

theorem strAt_eq (path : List String) (v : Value) : strAt path v = strAtSpec path v := by
  simp only [strAt, strAtSpec, valueAt_eq]
  cases atPath path v with
  | none => rfl
  | some x => cases x <;> rfl

theorem idVersion_eq (p : List PathSeg) :
    ∀ (i : Nat) (xs : List Value), Order.check.idVersionFrom p i xs = (misordersSpec p i xs).head?
  | _, [] => rfl
  | _, [_] => rfl
  | i, a :: b :: rest => by
    have ih := idVersion_eq p (i + 1) (b :: rest)
    have hk : idVersionKeys a b = keysSpec a b := by simp only [idVersionKeys, keysSpec, strAt_eq]
    simp only [Order.check.idVersionFrom, misordersSpec, hk]
    cases keysSpec a b with
    | none => simpa using ih
    | some k =>
      obtain ⟨ia, va, ib, vb⟩ := k
      by_cases hb : IdVersionBefore ia va ib vb
      · simp [(idVersionBefore_iff ia va ib vb).mpr hb, hb, ih]
      · have hb' : idVersionBefore ia va ib vb = false := by
          cases h : idVersionBefore ia va ib vb
          · rfl
          · exact absurd ((idVersionBefore_iff _ _ _ _).mp h) hb
        simp [hb', hb]

theorem order_eq (p : List PathSeg) (xs : List Value) (o : Order) :
    o.check p xs = (orderSpec p xs o).head? := by
  cases o with
  | nonempty => cases xs <;> rfl
  | ascending path => exact ascending_eq p path 1 xs
  | any => rfl
  | empty => cases xs <;> rfl
  | ascendingHas
    s =>
    simp only [Order.check, orderSpec, orElse_eq, head?_append', ascending_eq, strsOf_eq_spec]
    congr 1
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases h : strsSpec (x :: xs) with
      | none => simp
      | some ns => by_cases hs : s ∈ ns <;> simp [hs]
  | ascendingWithout
    s =>
    simp only [Order.check, orderSpec, orElse_eq, head?_append', ascending_eq, strsOf_eq_spec]
    congr 1
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases h : strsSpec (x :: xs) with
      | none => simp
      | some ns => by_cases hs : s ∈ ns <;> simp [hs]
  | unique path => exact unique_eq p path 0 [] xs
  | idVersion => exact idVersion_eq p 1 xs

mutual
theorem walk_eq (tag : String) (t : Ty) (p : List PathSeg) :
    ∀ v : Value, walk tag t p v = (violations tag t p v).head?
  | .obj ms => by
    simp only [walk, violations, resolve_eq]
    cases resolveSpec tag t with
    | obj d fs =>
      simp only [disc_eq]
      cases discSpec tag p ms d with
      | error e => rfl
      | ok r =>
        obtain ⟨tag', extra⟩ := r
        simp only [unknown_eq, missing_eq, members_eq tag' fs p ms, orElse_eq, head?_append',
          Option.or_assoc]
    | scalar ks r => exact leaf_eq ks r p _
    | arr ks h tl o => exact kindMiss_eq ks p _
    | byTag cs => rfl
  | .arr xs => by
    simp only [walk, violations, resolve_eq]
    cases resolveSpec tag t with
    | arr ks h tl o => simp only [elems_eq tag h tl p 0 xs, order_eq, orElse_eq, head?_append']
    | scalar ks r => exact leaf_eq ks r p _
    | obj d fs => rfl
    | byTag cs => rfl
  | .null => by
    simp only [walk, violations, resolve_eq]
    cases resolveSpec tag t <;>
      first
      | exact leaf_eq _ _ _ _
      | exact kindMiss_eq _ _ _
      | rfl
  | .bool b => by
    simp only [walk, violations, resolve_eq]
    cases resolveSpec tag t <;>
      first
      | exact leaf_eq _ _ _ _
      | exact kindMiss_eq _ _ _
      | rfl
  | .int n => by
    simp only [walk, violations, resolve_eq]
    cases resolveSpec tag t <;>
      first
      | exact leaf_eq _ _ _ _
      | exact kindMiss_eq _ _ _
      | rfl
  | .str s => by
    simp only [walk, violations, resolve_eq]
    cases resolveSpec tag t <;>
      first
      | exact leaf_eq _ _ _ _
      | exact kindMiss_eq _ _ _
      | rfl
theorem members_eq (tag : String) (fs : List (String × Ty)) (p : List PathSeg) :
    ∀ ms : List (String × Value), walkMembers tag fs p ms = (memberViolations tag fs p ms).head?
  | [] => rfl
  | (k, x) :: ms => by
    simp only [walkMembers, memberViolations, find_map_eq_lookup]
    cases fs.lookup k with
    | none => simpa using members_eq tag fs p ms
    | some t =>
      simp only [walk_eq tag t (p ++ [.key k]) x, members_eq tag fs p ms, orElse_eq, head?_append']
theorem elems_eq (tag : String) (h tl : Ty) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List Value),
      walkElems tag h tl p i xs = (elemViolations tag h tl p i xs).head?
  | _, [] => rfl
  | i, x :: xs => by
    simp only [walkElems, elemViolations]
    rw [walk_eq tag (if i = 0 then h else tl) (p ++ [PathSeg.index i]) x,
      elems_eq tag h tl p (i + 1) xs, orElse_eq, head?_append']
end

end FvdepAudit.Doc.Proof
