import FvdepAudit.Judge.Graph.Proof.Scan

/-! Proofs: the graph step (contract `docs/contracts/U7-judge.md` G3, G5, G6) + the axioms' texts
(A2) — on two exports the reader accepts, `graph` matches ⇒ e1's closure of G1's roots is declared
in e2 field for field (`GraphHolds`), reaches no opaque outside the reviewed list (`OpaqueHolds`),
the proof's closure in e2 is declared (`ProofHolds`) + the axioms returned = exactly those it
reaches; when all three hold it fails only by its work budget. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepAudit.Export.Spec FvdepAudit.Judge.Spec
  FvdepAudit.Judge.Statement.Spec FvdepAudit.Judge.Graph.Spec

/-- X8: a name's constant is the index's entry. -/
theorem named_eq {g v : String} {b : ByteArray} {t : Tables} (hb : readTables g v b = .ok t)
    {n : Lean.Name} {e e' : Entry} (he : (viewOf t).byName[n]? = some e) (h : Named t n e') :
    e' = e := named_unique hb h ((viewOf_get hb n e).1 he)

theorem named_none {g v : String} {b : ByteArray} {t : Tables} (hb : readTables g v b = .ok t)
    {n : Lean.Name} (he : (viewOf t).byName[n]? = none) (e : Entry) : ¬Named t n e := by
  intro h
  have := (viewOf_get hb n e).2 h
  rw [he] at this
  exact nomatch this

/-- A name popped from the walk: still checked or to check. -/
theorem skip_map {checked : Std.HashSet Lean.Name} {todo rest : List Lean.Name} {c : Lean.Name}
    (htd : todo = c :: rest) (hc : c ∈ checked) (c' : Lean.Name) :
    c' ∈ checked ∨ c' ∈ todo → c' ∈ checked ∨ c' ∈ rest := by
  rintro (h | h)
  · exact Or.inl h
  · rw [htd] at h
    rcases List.mem_cons.1 h with h | h
    · rw [h]
      exact Or.inl hc
    · exact Or.inr h

/-- A name checked: its uses join the names to check. -/
theorem step_map {checked : Std.HashSet Lean.Name} {todo rest ns : List Lean.Name} {c : Lean.Name}
    (htd : todo = c :: rest) (c' : Lean.Name) :
    c' ∈ ns ∨ (c' ∈ checked ∨ c' ∈ todo) → c' ∈ checked.insert c ∨ c' ∈ ns ++ rest := by
  rintro (h | h | h)
  · exact Or.inr (List.mem_append_left _ h)
  · exact Or.inl (Std.HashSet.mem_insert.2 (Or.inr h))
  · rw [htd] at h
    rcases List.mem_cons.1 h with h | h
    · rw [h]
      exact Or.inl (Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true c)))
    · exact Or.inr (List.mem_append_right _ h)

/-! ## G3 -/

/-- G3's walk invariant: e1's tables `t1`, e2's `t2`, roots `R`. -/
structure GraphInv (t1 t2 : Tables) (R : List Lean.Name) (w : Walk) : Prop where
  checked :
    ∀ c ∈ w.checked, Reach t1 R c ∧ ∃ e1 e2, Named t1 c e1 ∧ Named t2 c e2 ∧ EntryEq t1 t2 e1 e2
  todo : ∀ c ∈ w.todo, Reach t1 R c
  uses : ∀ c ∈ w.checked, ∀ e, Named t1 c e → ∀ c', Uses t1 e c' → c' ∈ w.checked ∨ c' ∈ w.todo
  roots : ∀ c ∈ R, c ∈ w.checked ∨ c ∈ w.todo
  seen :
    ∀ i ∈ w.seen,
      (∀ n ∈ (exprStep t1 i).1, ∀ c, t1.names[n]? = some c → c ∈ w.checked ∨ c ∈ w.todo) ∧
        ∀ k ∈ (exprStep t1 i).2, k ∈ w.seen
  order : ∀ c, c ∈ w.order ↔ c ∈ w.checked
  memo : ∀ p, w.memo.contains p = true → PairEq t1 t2 p

theorem graphInv_start (t1 t2 : Tables) (r : Request) (fuel : Nat) (memo : Std.HashSet Pair)
    (hm : ∀ p, memo.contains p = true → PairEq t1 t2 p) :
    GraphInv t1 t2 (graphRoots r) (walkStart r fuel memo)
    where
  checked _ hc := absurd hc Std.HashSet.not_mem_empty
  todo c hc := .root c hc
  uses _ hc := absurd hc Std.HashSet.not_mem_empty
  roots _ hc := Or.inr hc
  seen _ hi := absurd hi Std.HashSet.not_mem_empty
  order _ := ⟨fun h => (nomatch h), fun h => absurd h Std.HashSet.not_mem_empty⟩
  memo := hm

theorem graphInv_skip {t1 t2 : Tables} {R : List Lean.Name} {w : Walk} {c : Lean.Name}
    {rest : List Lean.Name} (hi : GraphInv t1 t2 R w) (htd : w.todo = c :: rest)
    (hc : c ∈ w.checked) (fuel : Nat) :
    GraphInv t1 t2 R
      { w with
        todo := rest, fuel } :=
  { checked := hi.checked
    todo := fun c' hc' =>
      hi.todo c'
        (by
          rw [htd]; exact List.mem_cons_of_mem _ hc')
    uses := fun c'' hc'' e he c' hu => skip_map htd hc c' (hi.uses c'' hc'' e he c' hu)
    roots := fun c' hc' => skip_map htd hc c' (hi.roots c' hc')
    seen := fun i hi' =>
      ⟨fun n hn c' hc' => skip_map htd hc c' ((hi.seen i hi').1 n hn c' hc'), (hi.seen i hi').2⟩
    order := hi.order
    memo := hi.memo }

theorem graphInv_step {g v : String} {b1 b2 : ByteArray} {t1 t2 : Tables}
    (hb1 : readTables g v b1 = .ok t1) (hb2 : readTables g v b2 = .ok t2) {R : List Lean.Name}
    {w : Walk} {c : Lean.Name} {rest : List Lean.Name} {e1 e2 : Entry} {fuel : Nat}
    {ns : List Lean.Name} {f' : Nat} {s' : Std.HashSet Nat} {m : Std.HashSet Pair}
    (hi : GraphInv t1 t2 R w) (htd : w.todo = c :: rest) (hv1 : (viewOf t1).byName[c]? = some e1)
    (hv2 : (viewOf t2).byName[c]? = some e2) (hee : EntryEq t1 t2 e1 e2)
    (hm : ∀ p, m.contains p = true → PairEq t1 t2 p)
    (hu : usesOf (viewOf t1).t e1 fuel w.seen = some (ns, f', s')) :
    GraphInv t1 t2 R
      { todo := ns ++ rest
        checked := w.checked.insert c
        order := c :: w.order
        seen := s'
        fuel := f'
        memo := m } := by
  have hn1 := (viewOf_get hb1 c e1).1 hv1
  have hn2 := (viewOf_get hb2 c e2).1 hv2
  have hrc : Reach t1 R c :=
    hi.todo c
      (by
        rw [htd]; exact List.mem_cons_self)
  obtain ⟨hL, hcomp, hseen⟩ :=
    usesOf_closed (rawOk_read hb1) (fun c' => c' ∈ w.checked ∨ c' ∈ w.todo) hu hi.seen
  refine
    { checked := fun c' hc' => ?_
      todo := fun c' hc' => ?_
      uses := fun c'' hc'' e he c' hu' => ?_
      roots := fun c' hc' => step_map htd c' (Or.inr (hi.roots c' hc'))
      seen := fun i hi' =>
        ⟨fun n hn c' hc' => step_map htd c' ((hseen i hi').1 n hn c' hc'), (hseen i hi').2⟩
      order := fun c' => ?_
      memo := hm }
  · rcases Std.HashSet.mem_insert.1 hc' with he | hc'
    · rw [← beq_iff_eq.1 he]
      exact ⟨hrc, e1, e2, hn1, hn2, hee⟩
    · exact hi.checked c' hc'
  · rcases List.mem_append.1 hc' with hc' | hc'
    · exact Reach.use c c' e1 hrc hn1 (hL c' hc')
    · exact
        hi.todo c'
          (by
            rw [htd]; exact List.mem_cons_of_mem _ hc')
  · rcases Std.HashSet.mem_insert.1 hc'' with he' | hc''
    · rw [← beq_iff_eq.1 he'] at he
      rw [named_eq hb1 hv1 he] at hu'
      exact step_map htd c' (hcomp c' hu')
    · exact step_map htd c' (Or.inr (hi.uses c'' hc'' e he c' hu'))
  · show c' ∈ c :: w.order ↔ c' ∈ w.checked.insert c
    rw [List.mem_cons, Std.HashSet.mem_insert, hi.order c', beq_iff_eq]
    exact
      ⟨fun h => h.elim (fun h => Or.inl h.symm) Or.inr, fun h =>
        h.elim (fun h => Or.inl h.symm) Or.inr⟩

/-- G3's walk: a match leaves the invariant with nothing to check; infrastructure = a reached
name e1 lacks; when every reached name is declared in both, field for field, the walk fails only
by its budget. -/
theorem graphWalk_spec {g v : String} {b1 b2 : ByteArray} {t1 t2 : Tables}
    (hb1 : readTables g v b1 = .ok t1) (hb2 : readTables g v b2 = .ok t2) (R : List Lean.Name) :
    ∀ (steps : Nat) (w : Walk) (o : Outcome) (w' : Walk),
      GraphInv t1 t2 R w →
        graphWalk (viewOf t1) (viewOf t2) steps w = (o, w') →
        (o = .matched → GraphInv t1 t2 R w' ∧ w'.todo = []) ∧
          (∀ d, o = .infra d → ∃ c, Reach t1 R c ∧ ∀ e, ¬Named t1 c e) ∧
          ((∀ c, Reach t1 R c → ∃ e1 e2, Named t1 c e1 ∧ Named t2 c e2 ∧ EntryEq t1 t2 e1 e2) →
            o = .matched ∨ o = .mismatch budget) := by
  intro steps
  induction steps with
  | zero =>
    intro w o w' hi hg
    by_cases he : w.todo.isEmpty = true
    · simp only [graphWalk, he, ↓reduceIte, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨fun _ => ⟨hi, List.isEmpty_iff.1 he⟩, fun _ hd => (nomatch hd), fun _ => Or.inl rfl⟩
    · simp only [graphWalk, he] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ => Or.inr rfl⟩
  | succ steps ih =>
    intro w o w' hi hg
    rcases htd : w.todo with _ | ⟨c, rest⟩
    · simp only [graphWalk, htd, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨fun _ => ⟨hi, htd⟩, fun _ hd => (nomatch hd), fun _ => Or.inl rfl⟩
    · have hrc : Reach t1 R c :=
        hi.todo c
          (by
            rw [htd]; exact List.mem_cons_self)
      rcases hfu : w.fuel with _ | fuel
      · simp only [graphWalk, htd, hfu, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ => Or.inr rfl⟩
      · simp only [graphWalk, htd, hfu] at hg
        by_cases hck : w.checked.contains c = true
        · simp only [hck, ↓reduceIte] at hg
          exact ih _ o w' (graphInv_skip hi htd (Std.HashSet.mem_iff_contains.2 hck) fuel) hg
        · simp only [hck] at hg
          rcases hv1 : (viewOf t1).byName[c]? with _ | e1
          · simp only [hv1] at hg
            obtain ⟨rfl, rfl⟩ := hg
            refine ⟨fun hm => (nomatch hm), fun _ _ => ⟨c, hrc, named_none hb1 hv1⟩, fun hall => ?_⟩
            obtain ⟨e1, _, he1, _⟩ := hall c hrc
            exact absurd he1 (named_none hb1 hv1 e1)
          · rcases hv2 : (viewOf t2).byName[c]? with _ | e2
            · simp only [hv1, hv2] at hg
              obtain ⟨rfl, rfl⟩ := hg
              refine ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun hall => ?_⟩
              obtain ⟨_, e2, _, he2, _⟩ := hall c hrc
              exact absurd he2 (named_none hb2 hv2 e2)
            · rcases hd : declEq (viewOf t1).t e1 (viewOf t2).t e2 fuel w.memo with ⟨r, f, m⟩
              have hde :=
                declEq_exact g v b1 b2 t1 t2 e1 e2 fuel w.memo (r, f, m) hb1 hb2 hi.memo hd
              cases r with
              | differ =>
                simp only [hv1, hv2, hd] at hg
                obtain ⟨rfl, rfl⟩ := hg
                refine ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun hall => ?_⟩
                obtain ⟨e1', e2', he1, he2, hee⟩ := hall c hrc
                rw [named_eq hb1 hv1 he1, named_eq hb2 hv2 he2] at hee
                exact absurd hee (hde.2 rfl)
              | exhausted =>
                simp only [hv1, hv2, hd] at hg
                obtain ⟨rfl, rfl⟩ := hg
                exact ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ => Or.inr rfl⟩
              | equal =>
                obtain ⟨hee, hm⟩ := hde.1 rfl
                rcases hu : usesOf (viewOf t1).t e1 f w.seen with _ | ⟨ns, f', s'⟩
                · simp only [hv1, hv2, hd, hu] at hg
                  obtain ⟨rfl, rfl⟩ := hg
                  exact ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ => Or.inr rfl⟩
                · simp only [hv1, hv2, hd, hu] at hg
                  exact ih _ o w' (graphInv_step hb1 hb2 hi htd hv1 hv2 hee hm hu) hg

/-- With nothing left to check, the checked names hold the whole closure. -/
theorem graphInv_closed {t1 t2 : Tables} {R : List Lean.Name} {w : Walk} (hi : GraphInv t1 t2 R w)
    (ht : w.todo = []) : ∀ c, Reach t1 R c → c ∈ w.checked := by
  intro c hc
  induction hc with
  | root c hc =>
    rcases hi.roots c hc with h | h
    · exact h
    · rw [ht] at h
      exact nomatch h
  | use c c' e _ hn hu ih =>
    rcases hi.uses c ih e hn c' hu with h | h
    · exact h
    · rw [ht] at h
      exact nomatch h

/-! ## G5 -/

theorem firstOpaque_none {v1 : View} {allowed : List Lean.Name} :
    ∀ (cs : List Lean.Name),
      firstOpaque v1 allowed cs = none →
        ∀ c ∈ cs,
          ∀ all u lps i ty val, v1.byName[c]? = some (.opaque all u lps i ty val) → c ∈ allowed
  | [], _, _, hc => (nomatch hc)
  | c :: cs, h, c', hc' => by
    intro all u lps i ty val hv
    have hrest :
      firstOpaque v1 allowed cs = none ∧
        ∀ all u lps i ty val, v1.byName[c]? = some (.opaque all u lps i ty val) → c ∈ allowed := by
      unfold firstOpaque at h
      split at h
      · by_cases ha : allowed.contains c = true
        · simp only [ha, ↓reduceIte] at h
          exact ⟨h, fun _ _ _ _ _ _ _ => List.contains_iff_mem.1 ha⟩
        · simp only [ha] at h
          exact nomatch h
      · rename_i hne
        exact ⟨h, fun all u lps i ty val hv => absurd hv (hne all u lps i ty val)⟩
    rcases List.mem_cons.1 hc' with hc' | hc'
    · rw [hc']
      exact hrest.2 all u lps i ty val (hc' ▸ hv)
    · exact firstOpaque_none cs hrest.1 c' hc' all u lps i ty val hv

theorem firstOpaque_eq_none {v1 : View} {allowed : List Lean.Name} :
    ∀ (cs : List Lean.Name),
      (∀ c ∈ cs,
          ∀ all u lps i ty val, v1.byName[c]? = some (.opaque all u lps i ty val) → c ∈ allowed) →
        firstOpaque v1 allowed cs = none
  | [], _ => rfl
  | c :: cs, h => by
    have ih := firstOpaque_eq_none cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    unfold firstOpaque
    split
    · rename_i all u lps i ty val heq
      have ha := List.contains_iff_mem.2 (h c List.mem_cons_self all u lps i ty val heq)
      simp only [ha, ↓reduceIte]
      exact ih
    · exact ih

/-! ## G6 -/

/-- G6's walk invariant: e2's tables `t2`, the proof constant `p0`. -/
structure ProofInv (t2 : Tables) (p0 : Lean.Name) (w : ProofWalk) : Prop where
  checked : ∀ c ∈ w.checked, Reach t2 [p0] c ∧ ∃ e, Named t2 c e
  todo : ∀ c ∈ w.todo, Reach t2 [p0] c
  uses : ∀ c ∈ w.checked, ∀ e, Named t2 c e → ∀ c', Uses t2 e c' → c' ∈ w.checked ∨ c' ∈ w.todo
  root : p0 ∈ w.checked ∨ p0 ∈ w.todo
  seen :
    ∀ i ∈ w.seen,
      (∀ n ∈ (exprStep t2 i).1, ∀ c, t2.names[n]? = some c → c ∈ w.checked ∨ c ∈ w.todo) ∧
        ∀ k ∈ (exprStep t2 i).2, k ∈ w.seen
  axioms : ∀ c, c ∈ w.axioms ↔ c ∈ w.checked ∧ ∃ u lps i ty, Named t2 c (.axiom u lps i ty)
  nodup : w.axioms.Nodup

theorem proofInv_start (t2 : Tables) (r : Request) (fuel : Nat) :
    ProofInv t2 r.proof (proofStart r fuel)
    where
  checked _ hc := absurd hc Std.HashSet.not_mem_empty
  todo c hc := .root c hc
  uses _ hc := absurd hc Std.HashSet.not_mem_empty
  root := Or.inr List.mem_cons_self
  seen _ hi := absurd hi Std.HashSet.not_mem_empty
  axioms _ := ⟨fun h => (nomatch h), fun h => absurd h.1 Std.HashSet.not_mem_empty⟩
  nodup := List.nodup_nil

theorem proofInv_skip {t2 : Tables} {p0 : Lean.Name} {w : ProofWalk} {c : Lean.Name}
    {rest : List Lean.Name} (hi : ProofInv t2 p0 w) (htd : w.todo = c :: rest) (hc : c ∈ w.checked)
    (fuel : Nat) :
    ProofInv t2 p0
      { w with
        todo := rest, fuel } :=
  { checked := hi.checked
    todo := fun c' hc' =>
      hi.todo c'
        (by
          rw [htd]; exact List.mem_cons_of_mem _ hc')
    uses := fun c'' hc'' e he c' hu => skip_map htd hc c' (hi.uses c'' hc'' e he c' hu)
    root := skip_map htd hc p0 hi.root
    seen := fun i hi' =>
      ⟨fun n hn c' hc' => skip_map htd hc c' ((hi.seen i hi').1 n hn c' hc'), (hi.seen i hi').2⟩
    axioms := hi.axioms
    nodup := hi.nodup }

theorem mem_recordAxiom {c c' : Lean.Name} {e : Entry} {ax : List Lean.Name} :
    c' ∈ recordAxiom c e ax ↔ c' ∈ ax ∨ c' = c ∧ ∃ u lps i ty, e = .axiom u lps i ty := by
  cases e with
  | «axiom» u lps i ty =>
    show c' ∈ c :: ax ↔ _
    rw [List.mem_cons]
    exact
      ⟨fun h => h.elim (fun h => Or.inr ⟨h, u, lps, i, ty, rfl⟩) Or.inl, fun h =>
        h.elim Or.inr fun ⟨h, _⟩ => Or.inl h⟩
  | _ => exact ⟨Or.inl, fun h => h.elim id fun ⟨_, _, _, _, _, h⟩ => (nomatch h)⟩

theorem proofInv_step {g v : String} {b2 : ByteArray} {t2 : Tables}
    (hb2 : readTables g v b2 = .ok t2) {p0 : Lean.Name} {w : ProofWalk} {c : Lean.Name}
    {rest : List Lean.Name} {e : Entry} {fuel : Nat} {ns : List Lean.Name} {f : Nat}
    {s : Std.HashSet Nat} (hi : ProofInv t2 p0 w) (htd : w.todo = c :: rest) (hck : c ∉ w.checked)
    (hv : (viewOf t2).byName[c]? = some e)
    (hu : usesOf (viewOf t2).t e fuel w.seen = some (ns, f, s)) :
    ProofInv t2 p0
      { todo := ns ++ rest
        checked := w.checked.insert c
        axioms := recordAxiom c e w.axioms
        seen := s
        fuel := f } := by
  have hn := (viewOf_get hb2 c e).1 hv
  have hrc : Reach t2 [p0] c :=
    hi.todo c
      (by
        rw [htd]; exact List.mem_cons_self)
  obtain ⟨hL, hcomp, hseen⟩ :=
    usesOf_closed (rawOk_read hb2) (fun c' => c' ∈ w.checked ∨ c' ∈ w.todo) hu hi.seen
  refine
    { checked := fun c' hc' => ?_
      todo := fun c' hc' => ?_
      uses := fun c'' hc'' e' he' c' hu' => ?_
      root := step_map htd p0 (Or.inr hi.root)
      seen := fun i hi' =>
        ⟨fun n hn' c' hc' => step_map htd c' ((hseen i hi').1 n hn' c' hc'), (hseen i hi').2⟩
      axioms := fun c' => ?_
      nodup := ?_ }
  · rcases Std.HashSet.mem_insert.1 hc' with he | hc'
    · rw [← beq_iff_eq.1 he]
      exact ⟨hrc, e, hn⟩
    · exact hi.checked c' hc'
  · rcases List.mem_append.1 hc' with hc' | hc'
    · exact Reach.use c c' e hrc hn (hL c' hc')
    · exact
        hi.todo c'
          (by
            rw [htd]; exact List.mem_cons_of_mem _ hc')
  · rcases Std.HashSet.mem_insert.1 hc'' with he | hc''
    · rw [← beq_iff_eq.1 he] at he'
      rw [named_eq hb2 hv he'] at hu'
      exact step_map htd c' (hcomp c' hu')
    · exact step_map htd c' (Or.inr (hi.uses c'' hc'' e' he' c' hu'))
  · show
      c' ∈ recordAxiom c e w.axioms ↔
        c' ∈ w.checked.insert c ∧ ∃ u lps i ty, Named t2 c' (.axiom u lps i ty)
    rw [mem_recordAxiom, hi.axioms c', Std.HashSet.mem_insert, beq_iff_eq]
    constructor
    · rintro (⟨h, hax⟩ | ⟨h, u, lps, i, ty, hax⟩)
      · exact ⟨Or.inr h, hax⟩
      · rw [h]
        rw [hax] at hn
        exact ⟨Or.inl rfl, u, lps, i, ty, hn⟩
    · rintro ⟨h | h, u, lps, i, ty, hax⟩
      · rw [← h] at hax
        exact Or.inr ⟨h.symm, u, lps, i, ty, (named_eq hb2 hv hax).symm⟩
      · exact Or.inl ⟨h, u, lps, i, ty, hax⟩
  · show (recordAxiom c e w.axioms).Nodup
    cases e with
    | «axiom» u lps i ty =>
      show (c :: w.axioms).Nodup
      exact List.nodup_cons.2 ⟨fun h => hck ((hi.axioms c).1 h).1, hi.nodup⟩
    | _ => exact hi.nodup

/-- G6's walk: a match leaves the invariant with nothing to check; never infrastructure; when the
proof's closure is declared in e2 the walk fails only by its budget. -/
theorem proofWalk_spec {g v : String} {b2 : ByteArray} {t2 : Tables}
    (hb2 : readTables g v b2 = .ok t2) (p0 : Lean.Name) :
    ∀ (steps : Nat) (w : ProofWalk) (o : Outcome) (w' : ProofWalk),
      ProofInv t2 p0 w →
        proofWalk (viewOf t2) steps w = (o, w') →
        (o = .matched → ProofInv t2 p0 w' ∧ w'.todo = []) ∧
          (∀ d, o ≠ .infra d) ∧
          ((∀ c, Reach t2 [p0] c → ∃ e, Named t2 c e) → o = .matched ∨ o = .mismatch budget) := by
  intro steps
  induction steps with
  | zero =>
    intro w o w' hi hg
    by_cases he : w.todo.isEmpty = true
    · simp only [proofWalk, he, ↓reduceIte, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨fun _ => ⟨hi, List.isEmpty_iff.1 he⟩, fun _ hd => (nomatch hd), fun _ => Or.inl rfl⟩
    · simp only [proofWalk, he] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ => Or.inr rfl⟩
  | succ steps ih =>
    intro w o w' hi hg
    rcases htd : w.todo with _ | ⟨c, rest⟩
    · simp only [proofWalk, htd, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨fun _ => ⟨hi, htd⟩, fun _ hd => (nomatch hd), fun _ => Or.inl rfl⟩
    · have hrc : Reach t2 [p0] c :=
        hi.todo c
          (by
            rw [htd]; exact List.mem_cons_self)
      rcases hfu : w.fuel with _ | fuel
      · simp only [proofWalk, htd, hfu, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ => Or.inr rfl⟩
      · simp only [proofWalk, htd, hfu] at hg
        by_cases hck : w.checked.contains c = true
        · simp only [hck, ↓reduceIte] at hg
          exact ih _ o w' (proofInv_skip hi htd (Std.HashSet.mem_iff_contains.2 hck) fuel) hg
        · simp only [hck] at hg
          have hck' : c ∉ w.checked := fun h => hck (Std.HashSet.mem_iff_contains.1 h)
          rcases hv : (viewOf t2).byName[c]? with _ | e
          · simp only [hv] at hg
            obtain ⟨rfl, rfl⟩ := hg
            refine ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun hall => ?_⟩
            obtain ⟨e, he⟩ := hall c hrc
            exact absurd he (named_none hb2 hv e)
          · rcases hu : usesOf (viewOf t2).t e fuel w.seen with _ | ⟨ns, f, s⟩
            · simp only [hv, hu] at hg
              obtain ⟨rfl, rfl⟩ := hg
              exact ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ => Or.inr rfl⟩
            · simp only [hv, hu] at hg
              exact ih _ o w' (proofInv_step hb2 hi htd hck' hv hu) hg

theorem proofInv_closed {t2 : Tables} {p0 : Lean.Name} {w : ProofWalk} (hi : ProofInv t2 p0 w)
    (ht : w.todo = []) : ∀ c, Reach t2 [p0] c → c ∈ w.checked := by
  intro c hc
  induction hc with
  | root c hc =>
    rw [List.mem_singleton.1 hc]
    rcases hi.root with h | h
    · exact h
    · rw [ht] at h
      exact nomatch h
  | use c c' e _ hn hu ih =>
    rcases hi.uses c ih e hn c' hu with h | h
    · exact h
    · rw [ht] at h
      exact nomatch h

theorem nodup_rev {l : List Lean.Name} (h : l.Nodup) : l.reverse.Nodup := by
  unfold List.Nodup
  rw [List.pairwise_reverse]
  exact h.imp fun hne heq => hne heq.symm

/-! ## G -/

/-- U7 G3 + G5 + G6 `graphExact`. -/
theorem graph_exact (githash version : String) (b1 b2 : ByteArray) (t1 t2 : Tables) (r : Request)
    (opaques : List Lean.Name) (fuel : Nat) (seen : Std.HashSet Pair)
    (o : Outcome × List Lean.Name × Nat × Std.HashSet Pair) :
    readTables githash version b1 = .ok t1 →
      readTables githash version b2 = .ok t2 →
      (∀ p, seen.contains p = true → PairEq t1 t2 p) →
      graph (viewOf t1) (viewOf t2) r opaques fuel seen = o →
      (o.1 = .matched →
          GraphHolds t1 t2 r ∧
            OpaqueHolds t1 r opaques ∧
            ProofHolds t2 r ∧
            (∀ c, c ∈ o.2.1 ↔ ReachedAxiom t2 r c) ∧
            o.2.1.Nodup ∧ ∀ p, o.2.2.2.contains p = true → PairEq t1 t2 p) ∧
        (∀ d, o.1 = .infra d → ∃ c, Reach t1 (graphRoots r) c ∧ ∀ e, ¬Named t1 c e) ∧
        (GraphHolds t1 t2 r →
          OpaqueHolds t1 r opaques →
          ProofHolds t2 r →
          o.1 = .matched ∨ o.1 = .mismatch "the comparison passes its work budget") := by
  intro hb1 hb2 hs ho
  unfold graph at ho
  rcases hw : graphWalk (viewOf t1) (viewOf t2) (fuel + 1) (walkStart r fuel seen) with ⟨o1, w⟩
  obtain ⟨ga, gb, gc⟩ :=
    graphWalk_spec hb1 hb2 (graphRoots r) (fuel + 1) _ o1 w (graphInv_start t1 t2 r fuel seen hs) hw
  cases o1 with
  | mismatch d =>
    simp only [hw] at ho
    subst ho
    refine ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun hg _ _ => ?_⟩
    rcases gc hg with h | h
    · exact nomatch h
    · cases h
      exact Or.inr rfl
  | infra d =>
    simp only [hw] at ho
    subst ho
    refine ⟨fun hm => (nomatch hm), fun _ _ => gb d rfl, fun hg _ _ => ?_⟩
    rcases gc hg with h | h
    · exact nomatch h
    · exact nomatch h
  | matched =>
    obtain ⟨hgi, hgt⟩ := ga rfl
    have hcl := graphInv_closed hgi hgt
    have hgh : GraphHolds t1 t2 r := fun c hc => (hgi.checked c (hcl c hc)).2
    simp only [hw] at ho
    rcases hfo : firstOpaque (viewOf t1) opaques w.order.reverse with _ | c
    · simp only [hfo] at ho
      have hoh : OpaqueHolds t1 r opaques := fun c hc all u lps i ty val hn =>
        firstOpaque_none _ hfo c (List.mem_reverse.2 ((hgi.order c).2 (hcl c hc))) all u lps i ty
          val ((viewOf_get hb1 c _).2 hn)
      rcases hp : proofWalk (viewOf t2) (w.fuel + 1) (proofStart r w.fuel) with ⟨o2, p⟩
      obtain ⟨pa, pb, pc⟩ :=
        proofWalk_spec hb2 r.proof (w.fuel + 1) _ o2 p (proofInv_start t2 r w.fuel) hp
      cases o2 with
      | matched =>
        simp only [hp] at ho
        subst ho
        obtain ⟨hpi, hpt⟩ := pa rfl
        have hpc := proofInv_closed hpi hpt
        refine
          ⟨fun _ =>
            ⟨hgh, hoh, fun c hc => (hpi.checked c (hpc c hc)).2, fun c => ?_, nodup_rev hpi.nodup,
              hgi.memo⟩,
            fun _ hd => (nomatch hd), fun _ _ _ => Or.inl rfl⟩
        show c ∈ p.axioms.reverse ↔ ReachedAxiom t2 r c
        rw [List.mem_reverse, hpi.axioms c]
        exact ⟨fun ⟨h, hax⟩ => ⟨(hpi.checked c h).1, hax⟩, fun ⟨h, hax⟩ => ⟨hpc c h, hax⟩⟩
      | mismatch d =>
        simp only [hp] at ho
        subst ho
        refine ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ _ hph => ?_⟩
        rcases pc hph with h | h
        · exact nomatch h
        · cases h
          exact Or.inr rfl
      | infra d => exact absurd rfl (pb d)
    · simp only [hfo] at ho
      subst ho
      refine ⟨fun hm => (nomatch hm), fun _ hd => (nomatch hd), fun _ hoh _ => ?_⟩
      have hnone :=
        firstOpaque_eq_none (v1 := viewOf t1) (allowed := opaques) w.order.reverse
          fun c' hc' all u lps i ty val hv =>
          hoh c' (hgi.checked c' ((hgi.order c').1 (List.mem_reverse.1 hc'))).1 all u lps i ty val
            ((viewOf_get hb1 c' _).1 hv)
      rw [hfo] at hnone
      exact nomatch hnone

/-! ## A2 -/

theorem quoted_head (s : String) : ("«" ++ s ++ "»").toList.head? = some '«' := by simp

theorem quoted_ne {s lit : String} (h : lit.toList.head? ≠ some '«') : "«" ++ s ++ "»" ≠ lit := by
  intro he
  apply h
  rw [← he]
  exact quoted_head s

/-- U7 A2 `axiomTextExact`. -/
theorem axiomText_exact (n : Lean.Name) :
    axiomText n ∈ ["propext", "Classical.choice", "Quot.sound"] ↔
      n ∈ FvdepCore.Index.Statuses.std := by
  unfold axiomText
  split
  · rename_i h
    rw [beq_iff_eq] at h
    subst h
    exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
  · rename_i h1
    split
    · rename_i h
      rw [beq_iff_eq] at h
      subst h
      exact
        ⟨fun _ => List.mem_cons_of_mem _ List.mem_cons_self, fun _ =>
          List.mem_cons_of_mem _ List.mem_cons_self⟩
    · rename_i h2
      split
      · rename_i h
        rw [beq_iff_eq] at h
        subst h
        exact
          ⟨fun _ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ =>
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      · rename_i h3
        constructor
        · intro hm
          exfalso
          rcases List.mem_cons.1 hm with hm | hm
          · exact quoted_ne (by simp) hm
          · rcases List.mem_cons.1 hm with hm | hm
            · exact quoted_ne (by simp) hm
            · exact quoted_ne (by simp) (List.mem_singleton.1 hm)
        · intro hn
          exfalso
          rcases List.mem_cons.1 hn with hn | hn
          · exact h1 (beq_iff_eq.2 hn)
          · rcases List.mem_cons.1 hn with hn | hn
            · exact h2 (beq_iff_eq.2 hn)
            · exact h3 (beq_iff_eq.2 (List.mem_singleton.1 hn))

end FvdepAudit.Judge.Proof
