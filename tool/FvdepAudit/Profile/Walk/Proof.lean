import FvdepAudit.Profile.Walk.Spec

/-! U6 C2: the walk = the head of the spec's ordered findings (`FvdepAudit.Profile.Walk.Spec`).
Layer (ii) first: each helper the walk calls = its restated rule (locations, layouts, slots, node,
atom + identifier rules, the role from the pending path); layer (i) = the traversal, by mutual
structural recursion over `Tree`. The table, the anchors + S stay opaque: one data fact is read —
every anchor path is non-empty with a wildcard only last (`anchors_well`, by `decide`). -/

namespace FvdepAudit.Profile.Walk.Proof

open FvdepCore.Profile FvdepAudit.Profile.Walk.Spec

/-! ## Pre-order subtrees + locations -/

mutual
/-- A tree's subtrees in pre-order. -/
def pre : Tree → List Tree
  | t@(.node _ kids) => t :: preList kids
  | t => [t]
def preList : List Tree → List Tree
  | [] => []
  | c :: cs => pre c ++ preList cs
end

mutual
theorem occs_tree : ∀ (t : Tree) (ch : List (Tree × Nat)), (occsOf ch t).map (·.1) = pre t
  | .node k kids, ch => by
    simp only [occsOf, pre, List.map_cons]
    rw [occs_kids kids (.node k kids) ch 0]
  | .atom _ _, _ => rfl
  | .ident _ _, _ => rfl
  | .missing, _ => rfl
theorem occs_kids :
    ∀ (ts : List Tree) (p : Tree) (ch : List (Tree × Nat)) (i : Nat),
      (occsKids p ch i ts).map (·.1) = preList ts
  | [], _, _, _ => rfl
  | c :: cs, p, ch, i => by
    simp only [occsKids, preList, List.map_append]
    rw [occs_tree c, occs_kids cs]
end

/-- A leaf's own position (an atom or an identifier). -/
def leafOf : Tree → Option Pos
  | .atom _ q => q
  | .ident _ q => q
  | _ => none

mutual
theorem firstPos_pre : ∀ (t : Tree), t.firstPos = (pre t).findSome? leafOf
  | .node k kids => by
    simp only [Tree.firstPos, pre, List.findSome?_cons, leafOf]
    exact firstPosList_pre kids
  | .atom _ _ => by simp [Tree.firstPos, pre, leafOf]
  | .ident _ _ => by simp [Tree.firstPos, pre, leafOf]
  | .missing => by simp [Tree.firstPos, pre, leafOf]
theorem firstPosList_pre : ∀ (ts : List Tree), firstPosList ts = (preList ts).findSome? leafOf
  | [] => by simp [firstPosList, preList]
  | c :: cs => by
    simp only [firstPosList, preList, List.findSome?_append]
    rw [firstPos_pre c, firstPosList_pre cs]
    cases (pre c).findSome? leafOf <;> rfl
end

/-- C1's location: the implementation's `firstPos` = the spec's first positioned leaf. -/
theorem firstPos_leafPos (t : Tree) : t.firstPos = leafPos t := by
  have h : leafPos t = ((occsOf [] t).map (·.1)).findSome? leafOf := by
    rw [List.findSome?_map]
    unfold leafPos
    congr 1
  rw [h, occs_tree, firstPos_pre]

theorem locate_eq (start : Pos) (t : Tree) (ch : List (Tree × Nat)) :
    locate start t (ch.map (·.1)) = locOf start t ch := by
  have h : (Tree.firstPos : Tree → Option Pos) = leafPos := funext firstPos_leafPos
  unfold locate locOf
  rw [h]
  cases (t :: ch.map (·.1)).findSome? leafPos <;> rfl

/-! ## Layer (ii): flat helpers -/

theorem transparent_iff (k : List String) : transparent k = true ↔ wrapper k := by
  simp [transparent, wrapper, or_assoc]

theorem found_eq (p : Pos) (r : String) (d : List String) : found p r d = some (mk p r d) := rfl

theorem ownershipBroken_eq (s : Subject) (full : List String) :
    ownershipBroken s full = ownBroken s full := by
  unfold ownershipBroken ownBroken
  cases full <;> cases s.role <;> rfl

theorem namespaceScope_eq (ns n : List String) : namespaceScope ns n = nsScoped ns n := by
  unfold namespaceScope nsScoped
  cases
      ((List.range n.length).map fun i => ns ++ n.take (i + 1)).find? scopedNamespaces.contains <;>
    rfl

theorem reservedComponent_eq (d : Bool) (n : List String) :
    reservedComponent d n = firstReserved d n := by
  induction n with
  | nil => rfl
  | cons c cs ih =>
    simp only [reservedComponent, firstReserved, List.find?_cons] at ih ⊢
    cases h : (c.startsWith "_" || (d && generated c)) <;> simp [ih]

theorem endsWith_eq (xs ys : List String) : endsWith xs ys = ys.isSuffixOf xs := by
  apply Bool.eq_iff_iff.2
  rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop]
  unfold endsWith
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    exact h.2.symm
  · intro h
    refine ⟨?_, h.symm⟩
    have hl := congrArg List.length h
    simp only [List.length_drop] at hl
    omega

theorem identFinding_eq (ns : List String) (role : IdRole) (n : List String) (p : Pos) :
    identFinding ns role n p = (identRulesAt ns role n p).head? := by
  simp only [identFinding, identRulesAt, endsWith_eq, reservedComponent_eq, found_eq]
  cases
      (role == .openName &&
        (n.contains "_root_" || scopedNamespaces.any fun x => n.isSuffixOf x)) <;>
    cases firstReserved (role == .slot || role == .declName) n <;>
    cases (role == .declName && ns ++ n == ["main"]) <;>
    cases (role == .derivName && !(derivingClasses.any fun c => n == [c])) <;>
    simp

theorem atomFinding_eq (start : Pos) (a : String) (q : Option Pos) (ch : List (Tree × Nat)) :
    atomFinding (ownerOf ch) a (locOf start (.atom a q) ch) =
      (atomRules start (.atom a q, ch)).head? := by
  unfold atomFinding atomRules
  cases ownerOf ch with
  | none => rfl
  | some r =>
    dsimp only
    cases r.shape <;> dsimp only <;>
      first
      | rfl
      | (split <;> simp_all [found_eq])

theorem nodeFinding_eq (s : Subject) (ns k : List String) (kids : List Tree) (p : Pos) :
    nodeFinding s ns k kids p = (roleRules s ns k kids p).head? := by
  unfold nodeFinding roleRules identAt present
  simp only [namespaceScope_eq, ownershipBroken_eq, found_eq]
  by_cases h1 : (k == kindNamespace) = true
  · simp only [h1]
    cases (kids[1]? : Option Tree) with
    | none => rfl
    | some t =>
      cases t with
      | ident n _ =>
        dsimp only
        cases nsScoped ns n with
        | some a => rfl
        | none => by_cases ho : ownBroken s (ns ++ n) = true <;> simp [ho]
      | _ => rfl
  · simp only [h1]
    by_cases h2 : (k == kindDeclId) = true
    · simp only [h2]
      cases (kids[0]? : Option Tree) with
      | none => rfl
      | some t =>
        cases t with
        | ident n _ =>
          dsimp only
          by_cases ho : ownBroken s (ns ++ n) = true <;> simp [ho]
        | _ => rfl
    · simp only [h2]
      cases (k == kindInstance && s.role == .library && ns.isEmpty)
      · simp
      · cases (kids[3]? : Option Tree) with
        | none => simp
        | some t =>
          cases t with
          | node _ ks => cases ks <;> simp
          | _ => simp

/-! ## Layer (ii): the role from the pending path -/

/-- The walk's pending step (`childPending`'s own). -/
def stepPend (i : Nat) : Path × IdRole → Option (Path × IdRole)
  | (s :: rest, r) => if s == none || s == some i then some (rest, r) else none
  | ([], _) => none

theorem childPending_eq (k : List String) (got : Option (Path × IdRole)) (i : Nat) :
    childPending k got i =
      match anchors.find? (·.1 == k) with
      | some (_, p, r, _) => stepPend i (p, r)
      | none => got.bind (stepPend i) := by
  unfold childPending
  cases anchors.find? (·.1 == k) with
  | some a => rcases a with ⟨_, _ | ⟨s, rest⟩, r, _⟩ <;> rfl
  | none =>
    cases got with
    | none => rfl
    | some g => rcases g with ⟨_ | ⟨s, rest⟩, r⟩ <;> rfl

/-- The pending path a chain's innermost occurrence receives (the walk's `pend`, from the chain). -/
def pendOf : List (Tree × Nat) → Option (Path × IdRole)
  | [] => none
  | (.node k _, i) :: rest => childPending k (pendOf rest) i
  | (_, i) :: rest => (pendOf rest).bind (stepPend i)

/-- A pending path read off at an identifier `below` further down. -/
def readRole (pd : Option (Path × IdRole)) (below : List Nat) : IdRole :=
  match pd with
  | some (p, r) => if pathMatches p below then r else .use
  | none => .use

theorem readRole_step (i : Nat) (p : Path) (r : IdRole) (below : List Nat) :
    readRole (stepPend i (p, r)) below = if pathMatches p (i :: below) then r else .use := by
  rcases p with _ | ⟨_ | j, p⟩
  · rfl
  · rfl
  · simp only [stepPend, readRole, pathMatches]
    by_cases h : j = i <;> simp [h]

theorem readRole_bind (pd : Option (Path × IdRole)) (i : Nat) (below : List Nat) :
    readRole (pd.bind (stepPend i)) below = readRole pd (i :: below) := by
  cases pd with
  | none => rfl
  | some pr =>
    rcases pr with ⟨p, r⟩
    exact readRole_step i p r below

theorem roleOf_go :
    ∀ (ch : List (Tree × Nat)) (below : List Nat), roleOf.go below ch = readRole (pendOf ch) below
  | [], _ => rfl
  | (.node k kids, i) :: rest, below => by
    simp only [roleOf.go, pendOf, childPending_eq]
    cases anchors.find? (·.1 == k) with
    | some a =>
      rcases a with ⟨_, p, r, _⟩
      exact (readRole_step i p r below).symm
    | none =>
      dsimp only
      rw [roleOf_go rest (i :: below), readRole_bind]
  | (.atom _ _, i) :: rest, below => by
    show roleOf.go (i :: below) rest = _
    rw [roleOf_go rest (i :: below)]
    exact (readRole_bind _ i below).symm
  | (.ident _ _, i) :: rest, below => by
    show roleOf.go (i :: below) rest = _
    rw [roleOf_go rest (i :: below)]
    exact (readRole_bind _ i below).symm
  | (.missing, i) :: rest, below => by
    show roleOf.go (i :: below) rest = _
    rw [roleOf_go rest (i :: below)]
    exact (readRole_bind _ i below).symm

/-- The walk's role at an identifier from its pending path. -/
def pendRole (pend : Option (Path × IdRole)) : IdRole :=
  match pend with
  | some ([], r) => r
  | _ => .use

theorem pendRole_roleOf (ch : List (Tree × Nat)) : pendRole (pendOf ch) = roleOf ch := by
  unfold roleOf
  rw [roleOf_go ch []]
  cases pendOf ch with
  | none => rfl
  | some pr => rcases pr with ⟨_ | ⟨_ | _, _⟩, _⟩ <;> rfl

/-! ## Layer (ii): the declaring slots -/

/-- Anchor paths the slot rule is exact on: non-empty, a wildcard only last. -/
def wellPath : Path → Bool
  | [] => false
  | [_] => true
  | some _ :: p => wellPath p
  | none :: _ => false

theorem anchors_well : anchors.all (fun a => wellPath a.2.1) = true := by decide

/-- The spec's slot condition at one occurrence. -/
def slotCond (p : Path) (o : Tree × List Nat) : Bool :=
  if o.2.length < p.length && pathMatches (p.take o.2.length) o.2 then (o.1 matches .node _ _)
  else if pathMatches p o.2 then (o.1 matches .ident _ _) else true

/-- The spec's slot check of `kids` against path `p`. -/
def slotSpec (req : Bool) (p : Path) (kids : List Tree) : Bool :=
  (insideKids 0 kids).all (slotCond p) &&
    (!req || (insideKids 0 kids).any fun o => pathMatches p o.2)

theorem slotCond_some (j m : Nat) (q : Path) (x : Tree) (r : List Nat) :
    slotCond (some j :: q) (x, m :: r) = if j == m then slotCond q (x, r) else true := by
  by_cases h : j = m
  · subst h
    by_cases h1 : r.length < q.length <;> by_cases h2 : pathMatches (q.take r.length) r = true <;>
      by_cases h3 : pathMatches q r = true <;>
      simp [slotCond, pathMatches, h1, h2, h3]
  · simp [slotCond, pathMatches, h]

theorem slotCond_none (m : Nat) (q : Path) (x : Tree) (r : List Nat) :
    slotCond (none :: q) (x, m :: r) = slotCond q (x, r) := by
  by_cases h1 : r.length < q.length <;> by_cases h2 : pathMatches (q.take r.length) r = true <;>
    by_cases h3 : pathMatches q r = true <;>
    simp [slotCond, pathMatches, h1, h2, h3]

mutual
theorem inside_path : ∀ (t : Tree) (o : Tree × List Nat), o ∈ inside t → o.2 ≠ []
  | .node _ kids, o, h => insideKids_path kids 0 o h
  | .atom _ _, _, h => by simp [inside] at h
  | .ident _ _, _, h => by simp [inside] at h
  | .missing, _, h => by simp [inside] at h
theorem insideKids_path :
    ∀ (cs : List Tree) (i : Nat) (o : Tree × List Nat), o ∈ insideKids i cs → o.2 ≠ []
  | [], _, _, h => by simp [insideKids] at h
  | c :: cs, i, o, h => by
    simp only [insideKids, List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨o', _, h⟩ | h
    · subst h
      simp
    · subst h
      simp
    · exact insideKids_path cs (i + 1) o h
end

/-- The occurrences of child `c` (itself first) with paths from it. -/
def selfIn (c : Tree) : List (Tree × List Nat) := (c, []) :: inside c

theorem all_insideKids (P : Tree × List Nat → Bool) :
    ∀ (cs : List Tree) (i : Nat),
      (insideKids i cs).all P = true ↔
        ∀ m c, cs[m]? = some c → ∀ o ∈ selfIn c, P (o.1, (i + m) :: o.2) = true
  | [], i => by simp [insideKids]
  | c :: cs, i => by
    rw [insideKids, List.all_append, Bool.and_eq_true, all_insideKids P cs (i + 1)]
    simp only [List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true, Function.comp_def,
      selfIn, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h0, hin⟩, hrest⟩ m c' hm
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
        subst hm
        exact ⟨by simpa using h0, fun o ho => by simpa using hin o ho⟩
      | succ m =>
        simp only [List.getElem?_cons_succ] at hm
        have h := hrest m c' hm
        rw [show i + (m + 1) = i + 1 + m by omega]
        exact h
    · intro h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa using (h 0 c rfl).1
      · intro o ho
        simpa using (h 0 c rfl).2 o ho
      · intro m c' hm
        have h' := h (m + 1) c' (by simpa using hm)
        rw [show i + 1 + m = i + (m + 1) by omega]
        exact h'

theorem any_insideKids (P : Tree × List Nat → Bool) :
    ∀ (cs : List Tree) (i : Nat),
      (insideKids i cs).any P = true ↔
        ∃ m c, cs[m]? = some c ∧ ∃ o ∈ selfIn c, P (o.1, (i + m) :: o.2) = true
  | [], i => by simp [insideKids]
  | c :: cs, i => by
    rw [insideKids, List.any_append, Bool.or_eq_true, any_insideKids P cs (i + 1)]
    simp only [List.any_cons, List.any_map, Bool.or_eq_true, List.any_eq_true, Function.comp_def,
      selfIn, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h0 | ⟨o, ho, hp⟩) | ⟨m, c', hm, hr⟩)
      · exact ⟨0, c, rfl, Or.inl (by simpa using h0)⟩
      · exact ⟨0, c, rfl, Or.inr ⟨o, ho, by simpa using hp⟩⟩
      · refine ⟨m + 1, c', by simpa using hm, ?_⟩
        rw [show i + (m + 1) = i + 1 + m by omega]
        exact hr
    · rintro ⟨m, c', hm, hr⟩
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
        subst hm
        rcases hr with h0 | ⟨o, ho, hp⟩
        · exact Or.inl (Or.inl (by simpa using h0))
        · exact Or.inl (Or.inr ⟨o, ho, by simpa using hp⟩)
      | succ m =>
        simp only [List.getElem?_cons_succ] at hm
        refine Or.inr ⟨m, c', hm, ?_⟩
        rw [show i + 1 + m = i + (m + 1) by omega]
        exact hr

/-- The child at a path's head, judged from the child itself: the slot holds there + is reached. -/
theorem slotSpec_some (req : Bool) (j : Nat) (q : Path) (kids : List Tree) :
    slotSpec req (some j :: q) kids =
      match kids[j]? with
      | some c => (selfIn c).all (slotCond q) && (!req || (selfIn c).any fun o => pathMatches q o.2)
      | none => !req := by
  apply Bool.eq_iff_iff.2
  unfold slotSpec
  simp only [Bool.and_eq_true, Bool.or_eq_true, all_insideKids, any_insideKids, Nat.zero_add]
  have hall :
    (∀ m c, kids[m]? = some c → ∀ o ∈ selfIn c, slotCond (some j :: q) (o.1, m :: o.2) = true) ↔
      ∀ c, kids[j]? = some c → ∀ o ∈ selfIn c, slotCond q o = true := by
    simp only [slotCond_some]
    constructor
    · intro h c hc o ho
      simpa using h j c hc o ho
    · intro h m c hm o ho
      by_cases hjm : j = m
      · subst hjm
        simpa using h c hm o ho
      · simp [hjm]
  have hany :
    (∃ m c, kids[m]? = some c ∧ ∃ o ∈ selfIn c, pathMatches (some j :: q) (m :: o.2) = true) ↔
      ∃ c, kids[j]? = some c ∧ ∃ o ∈ selfIn c, pathMatches q o.2 = true := by
    simp only [pathMatches, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨m, c, hm, o, ho, rfl, hp⟩
      exact ⟨c, hm, o, ho, hp⟩
    · rintro ⟨c, hc, o, ho, hp⟩
      exact ⟨j, c, hc, o, ho, rfl, hp⟩
  rw [hall, hany]
  cases kids[j]? with
  | none => simp
  | some c => simp [List.all_eq_true, List.any_eq_true]

theorem selfIn_all_last (c : Tree) : (selfIn c).all (slotCond []) = (c matches .ident _ _) := by
  have hin : (inside c).all (slotCond []) = true := by
    rw [List.all_eq_true]
    intro o ho
    have hne := inside_path c o ho
    rcases o with ⟨x, _ | ⟨y, ys⟩⟩
    · exact absurd rfl hne
    · simp [slotCond, pathMatches]
  simp only [selfIn, List.all_cons, hin, Bool.and_true]
  cases c <;> rfl

theorem selfIn_any_last (c : Tree) : (selfIn c).any (fun o => pathMatches [] o.2) = true := by
  simp [selfIn, pathMatches]

theorem slotSpec_none (req : Bool) (q : Path) (kids : List Tree) :
    slotSpec req (none :: q) kids =
      ((kids.all fun c => (selfIn c).all (slotCond q)) &&
        (!req || kids.any fun c => (selfIn c).any fun o => pathMatches q o.2)) := by
  apply Bool.eq_iff_iff.2
  unfold slotSpec
  simp only [Bool.and_eq_true, Bool.or_eq_true, all_insideKids, any_insideKids, Nat.zero_add,
    slotCond_none, pathMatches]
  simp only [List.all_eq_true, List.any_eq_true, Prod.eta]
  constructor
  · rintro ⟨hall, hreq⟩
    refine ⟨fun c hc => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hc
      exact hall m c hm
    · rcases hreq with h | ⟨m, c, hm, o, ho, hp⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, List.mem_iff_getElem?.2 ⟨m, hm⟩, o, ho, hp⟩
  · rintro ⟨hall, hreq⟩
    refine ⟨fun m c hm => hall c (List.mem_iff_getElem?.2 ⟨m, hm⟩), ?_⟩
    rcases hreq with h | ⟨c, hc, o, ho, hp⟩
    · exact Or.inl h
    · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hc
      exact Or.inr ⟨m, c, hm, o, ho, hp⟩

theorem slotOk_eq (req : Bool) :
    ∀ (p : Path) (kids : List Tree), wellPath p = true → slotOk req p kids = slotSpec req p kids
  | [], _, h => by simp [wellPath] at h
  | [some j], kids, _ => by
    rw [slotSpec_some]
    unfold slotOk
    cases kids[j]? with
    | none => rfl
    | some c =>
      dsimp only
      rw [selfIn_all_last, selfIn_any_last, Bool.or_true, Bool.and_true]
      cases c <;> rfl
  | [none], kids, _ => by
    rw [slotSpec_none]
    have hall :
      (kids.all fun c => (selfIn c).all (slotCond [])) =
        kids.all fun c => (c matches .ident _ _) := by
      congr 1
      funext c
      exact selfIn_all_last c
    have hany : (kids.any fun c => (selfIn c).any fun o => pathMatches [] o.2) = !kids.isEmpty := by
      cases kids <;> simp [selfIn_any_last]
    rw [hall, hany]
    unfold slotOk
    rw [Bool.and_comm]
    rfl
  | some j :: p :: rest, kids, h => by
    have hw : wellPath (p :: rest) = true := h
    rw [slotSpec_some]
    unfold slotOk
    cases kids[j]? with
    | none => rfl
    | some c =>
      cases c with
      | node k ks =>
        dsimp only
        rw [slotOk_eq req (p :: rest) ks hw]
        have h0 : slotCond (p :: rest) (Tree.node k ks, []) = true := by
          simp [slotCond, pathMatches]
        have h1 : pathMatches (p :: rest) ([] : List Nat) = false := by cases p <;> rfl
        simp [slotSpec, selfIn, inside, h0, h1]
      | atom _ _ => simp [selfIn, inside, slotCond, pathMatches]
      | ident _ _ => simp [selfIn, inside, slotCond, pathMatches]
      | missing => simp [selfIn, inside, slotCond, pathMatches]
  | none :: _ :: _, _, h => by simp [wellPath] at h

theorem anchorOk_eq (k : List String) (kids : List Tree) : anchorOk k kids = slotsHold k kids := by
  unfold anchorOk slotsHold
  cases h : anchors.find? (·.1 == k) with
  | none => rfl
  | some a =>
    rcases a with ⟨x, p, r, req⟩
    have hw : wellPath p = true := by
      have hm := List.mem_of_find?_eq_some h
      exact List.all_eq_true.1 anchors_well _ hm
    exact slotOk_eq req p kids hw

/-! ## Layer (i): the traversal -/

section Traversal

variable (s : Subject) (ns : List String) (start : Pos)

mutual
theorem walk_eq :
    ∀ (t : Tree) (ch : List (Tree × Nat)),
      walk s ns start (ownerOf ch) (pendOf ch) (ch.map (·.1)) t =
        ((occsOf ch t).flatMap (findingsAt s ns start)).head?
  | .node k kids, ch => by
    have hk := walkKids_eq kids k kids ch 0
    have hocc :
      occsOf ch (.node k kids) = (.node k kids, ch) :: occsKids (.node k kids) ch 0 kids := rfl
    have hat : atomRules start (.node k kids, ch) = [] := rfl
    have hid : identRules ns start (.node k kids, ch) = [] := rfl
    rw [hocc, List.flatMap_cons, findingsAt, hat, hid, List.append_nil, List.append_nil,
      List.head?_append, ← hk]
    simp only [walk, nodeRules, locate_eq]
    by_cases hw : wrapper k
    · have ht : transparent k = true := (transparent_iff k).2 hw
      have ho : ownerOf ((Tree.node k kids, 0) :: ch) = ownerOf ch := by simp [ownerOf, hw]
      simp [ht, hw, ho]
    · have ht : transparent k = false := by
        cases h : transparent k
        · rfl
        · exact absurd ((transparent_iff k).1 h) hw
      have ho : ownerOf ((Tree.node k kids, 0) :: ch) = lookupRule k := by simp [ownerOf, hw]
      rw [ho]
      cases hr : lookupRule k with
      | none => simp [ht, hw, found_eq]
      | some r =>
        simp only [ht, hw, anchorOk_eq, nodeFinding_eq, found_eq]
        by_cases hl : (shapeOk r.shape kids && slotsHold k kids) = true
        · simp only [Bool.and_eq_true] at hl
          simp only [hl, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
            Bool.and_self]
          cases (roleRules s ns k kids (locOf start (.node k kids) ch)).head? <;> rfl
        · have hl' : (!shapeOk r.shape kids || !slotsHold k kids) = true := by
            cases h1 : shapeOk r.shape kids <;> cases h2 : slotsHold k kids <;> simp_all
          simp [hl, hl']
  | .atom a q, ch => by
    show
      atomFinding (ownerOf ch) a (locate start (.atom a q) (ch.map (·.1))) =
        ([] ++ atomRules start (.atom a q, ch) ++ [] ++ []).head?
    rw [locate_eq, atomFinding_eq]
    simp only [List.append_nil, List.nil_append]
  | .ident n q, ch => by
    show
      identFinding ns (pendRole (pendOf ch)) n (locate start (.ident n q) (ch.map (·.1))) =
        ([] ++ [] ++ identRulesAt ns (roleOf ch) n (locOf start (.ident n q) ch) ++ []).head?
    rw [locate_eq, pendRole_roleOf, identFinding_eq]
    simp only [List.append_nil, List.nil_append]
  | .missing, ch => rfl
theorem walkKids_eq :
    ∀ (cs : List Tree) (k : List String) (kids : List Tree) (ch : List (Tree × Nat)) (i : Nat),
      walkKids s ns start (ownerOf ((.node k kids, 0) :: ch)) k (pendOf ch)
          (.node k kids :: ch.map (·.1)) i cs =
        ((occsKids (.node k kids) ch i cs).flatMap (findingsAt s ns start)).head?
  | [], _, _, _, _ => rfl
  | c :: cs, k, kids, ch, i => by
    have hc := walk_eq c ((.node k kids, i) :: ch)
    have hcs := walkKids_eq cs k kids ch (i + 1)
    have ho : ownerOf ((Tree.node k kids, i) :: ch) = ownerOf ((Tree.node k kids, 0) :: ch) := rfl
    have hp : pendOf ((Tree.node k kids, i) :: ch) = childPending k (pendOf ch) i := rfl
    rw [ho, hp] at hc
    simp only [List.map_cons] at hc
    simp only [walkKids, occsKids, List.flatMap_append, List.head?_append]
    rw [hc, hcs]
    cases ((occsOf ((Tree.node k kids, i) :: ch) c).flatMap (findingsAt s ns start)).head? <;> rfl
end

end Traversal

/-! ## The claims -/

/-- C1 + K0 + K0' + P4 + I2 + I3 + K4 (`walkFirst`). -/
theorem walk_first (s : Subject) (ns : List String) (start : Pos) (t : Tree) :
    walk s ns start none none [] t = (FvdepAudit.Profile.Walk.Spec.findings s ns start t).head? :=
  walk_eq s ns start t []

/-- C1 (`walkAccepts`). -/
theorem walk_accepts (s : Subject) (ns : List String) (start : Pos) (t : Tree) :
    walk s ns start none none [] t = none ↔
      ∀ o ∈ FvdepAudit.Profile.Walk.Spec.occsOf [] t,
        FvdepAudit.Profile.Walk.Spec.findingsAt s ns start o = [] := by
  rw [walk_first, FvdepAudit.Profile.Walk.Spec.findings, List.head?_eq_none_iff,
    List.flatMap_eq_nil_iff]

end FvdepAudit.Profile.Walk.Proof
