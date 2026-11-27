import FvdepAudit.Judge.Proof.Raw
import FvdepAudit.Judge.Statement.Spec

/-! Proofs: one export's name index (contract `docs/contracts/U7-judge.md` X6 + X8) — on every
export the reader accepts, the index finds exactly the constant of a name (X8: one declaration per
name). -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepAudit.Export.Spec FvdepAudit.Export.Proof
  FvdepAudit.Judge.Statement.Spec

/-- A constant's type (an index). -/
def entryType : Entry → Nat
  | .axiom _ _ _ ty => ty
  | .defn _ _ _ _ _ ty _ => ty
  | .thm _ _ _ ty _ => ty
  | .opaque _ _ _ _ ty _ => ty
  | .quot _ _ _ ty => ty
  | .induct x => x.type
  | .ctor c => c.type
  | .recursor r => r.type

/-- The records' constants beside the declarations: their names + types denote the declarations'
names + types in order, no name twice. -/
structure EntriesOk (t : Tables) : Prop where
  names :
    (t.rawDecls.toList.flatMap entries).map (fun e => t.names[e.name]?) =
      t.decls.toList.map fun d => some d.name
  types :
    (t.rawDecls.toList.flatMap entries).map (fun e => t.exprs[entryType e]?) =
      t.decls.toList.map fun d => some d.type
  nodup : (t.decls.toList.map (·.name)).Nodup

/-- X6's split = the reader's: the same names + types, record by record. -/
theorem entries_names (d : DeclF) : (entries d).map Entry.name = (itemsOf d).map (·.name) := by
  cases d <;> simp [entries, itemsOf, Entry.name, Function.comp_def]

theorem entries_types (d : DeclF) : (entries d).map entryType = (itemsOf d).map (·.type) := by
  cases d <;> simp [entries, itemsOf, entryType, Function.comp_def]

theorem map_zip_eq {α β γ : Type} (f : α → γ) (g : β → γ) :
    ∀ (xs : List α) (ys : List β),
      xs.length = ys.length → (∀ p ∈ xs.zip ys, f p.1 = g p.2) → xs.map f = ys.map g
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact
      ⟨h (x, y) List.mem_cons_self,
        map_zip_eq f g xs ys (by simpa using hl) fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem entriesOk_initial : EntriesOk initial where
  names := by simp [initial]
  types := by simp [initial]
  nodup := by simp [initial]

/-- Every constant name of the records is bound (the map holds `some` alone). -/
theorem entriesOk_bound {t : Tables} (h : EntriesOk t) :
    ∀ e ∈ t.rawDecls.toList.flatMap entries, (t.names[e.name]?).isSome := by
  intro e he
  have := congrArg (fun l => (fun e => t.names[e.name]?) e ∈ l) h.names
  simp only [List.mem_map] at this
  obtain ⟨d, _, hd⟩ := this.mp ⟨e, he, rfl⟩
  rw [← hd]
  rfl

/-- Every constant type of the records is bound. -/
theorem entriesOk_typed {t : Tables} (h : EntriesOk t) :
    ∀ e ∈ t.rawDecls.toList.flatMap entries, (t.exprs[entryType e]?).isSome := by
  intro e he
  have := congrArg (fun l => (fun e => t.exprs[entryType e]?) e ∈ l) h.types
  simp only [List.mem_map] at this
  obtain ⟨d, _, hd⟩ := this.mp ⟨e, he, rfl⟩
  rw [← hd]
  rfl

theorem entriesOk_apply {t : Tables} {r : Raw} {t' : Tables} (hr : EntriesOk t)
    (h : ApplySpec t r t') : EntriesOk t' := by
  cases r with
  | name i f =>
    obtain ⟨_, n, _, rfl⟩ := h
    refine ⟨?_, hr.types, hr.nodup⟩
    rw [← hr.names]
    apply List.map_congr_left
    intro e he
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (entriesOk_bound hr e he)
    exact (get_push hx).trans hx.symm
  | level i f =>
    obtain ⟨_, _, _, rfl⟩ := h
    exact ⟨hr.names, hr.types, hr.nodup⟩
  | expr i f =>
    obtain ⟨_, _, _, rfl⟩ := h
    refine ⟨hr.names, ?_, hr.nodup⟩
    rw [← hr.types]
    apply List.map_congr_left
    intro e he
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (entriesOk_typed hr e he)
    exact (get_push hx).trans hx.symm
  | decl d =>
    obtain ⟨os, hl, hp, hn, hs, rfl⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · show
        ((t.rawDecls.push d).toList.flatMap entries).map (fun e => t.names[e.name]?) =
          (t.decls ++ os.toArray).toList.map fun d => some d.name
      simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_append, Array.toList_append, hr.names]
      congr 1
      have he :
        (entries d).map (fun e => t.names[e.name]?) =
          ((itemsOf d).map (·.name)).map (fun i => t.names[i]?) := by
        rw [← entries_names, List.map_map]
        rfl
      rw [he, List.map_map]
      apply map_zip_eq _ _ _ _ hl
      intro p hp'
      exact (hp p hp').2.2.1
    · show
        ((t.rawDecls.push d).toList.flatMap entries).map (fun e => t.exprs[entryType e]?) =
          (t.decls ++ os.toArray).toList.map fun d => some d.type
      simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_append, Array.toList_append, hr.types]
      congr 1
      have he :
        (entries d).map (fun e => t.exprs[entryType e]?) =
          ((itemsOf d).map (·.type)).map (fun i => t.exprs[i]?) := by
        rw [← entries_types, List.map_map]
        rfl
      rw [he, List.map_map]
      apply map_zip_eq _ _ _ _ hl
      intro p hp'
      exact (hp p hp').2.2.2.2.2.1
    · show ((t.decls ++ os.toArray).toList.map (·.name)).Nodup
      simp only [Array.toList_append, List.map_append]
      refine List.nodup_append.2 ⟨hr.nodup, hn, ?_⟩
      intro a ha b hb hab
      subst hab
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hb
      exact hs o ho ha

theorem entriesOk_run {g v : String} {k : Nat} {t : Tables} {ls : List (List UInt8)}
    {o : Except (Nat × Class) Tables} (h : Run g v k t ls o) :
    EntriesOk t → ∀ t', o = .ok t' → EntriesOk t' := by
  induction h with
  | noHeader => exact fun _ _ h => by cases h
  | done k t _ =>
    intro hr t' h
    cases h
    exact hr
  | json => exact fun _ _ h => by cases h
  | headerBad => exact fun _ _ h => by cases h
  | header _ _ _ _ _ _ _ _ ih => exact ih
  | recordBad => exact fun _ _ h => by cases h
  | record _ _ _ _ _ _ _ _ _ hr _ ih =>
    intro h0 t'' ho
    cases hr with
    | ok r _ _ ha => exact ih (entriesOk_apply h0 ha) t'' ho

theorem entriesOk_read {g v : String} {b : ByteArray} {t : Tables}
    (h : readTables g v b = .ok t) : EntriesOk t :=
  entriesOk_run ((read_tables g v b t).1 h) entriesOk_initial t rfl

/-! ## The index -/

/-- A map without repeats is injective on its list. -/
theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with hxa | hxl
    · rcases List.mem_cons.1 hy with hya | hyl
      · exact hxa.trans hya.symm
      · rw [hxa] at he
        exact absurd (List.mem_map.2 ⟨y, hyl, he.symm⟩) h.1
    · rcases List.mem_cons.1 hy with hya | hyl
      · rw [hya] at he
        exact absurd (List.mem_map.2 ⟨x, hxl, he⟩) h.1
      · exact inj_of_nodup_map h.2 hxl hyl he

/-- The index over `es` from `m`: a name of `es` finds its constant, any other name `m`'s. -/
theorem nameIndex_fold (t : Tables) :
    ∀ (es : List Entry) (m : Std.HashMap Lean.Name Entry),
      (es.map fun e => t.names[e.name]?).Nodup →
        (∀ e ∈ es, (t.names[e.name]?).isSome) →
          ∀ n,
            (es.foldl (indexStep t) m)[n]? =
              match es.find? (fun e => t.names[e.name]? == some n) with
              | some e => some e
              | none => m[n]?
  | [], _, _, _, _ => rfl
  | e :: es, m, hn, hb, n => by
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hb e List.mem_cons_self)
    simp only [List.foldl_cons, indexStep, hx]
    rw [nameIndex_fold t es (m.insert x e) hn.2
        (fun e' he' => hb e' (List.mem_cons_of_mem _ he')) n]
    simp only [List.find?_cons, hx]
    by_cases hxn : x = n
    · subst hxn
      have hnone : es.find? (fun e' => t.names[e'.name]? == some x) = none := by
        rw [List.find?_eq_none]
        intro e' he' heq
        simp only [beq_iff_eq] at heq
        exact hn.1 (List.mem_map.2 ⟨e', he', heq.trans hx.symm⟩)
      simp [hnone]
    · have hne : (some x == some n) = false := by simp [hxn]
      simp only [hne]
      cases es.find? (fun e' => t.names[e'.name]? == some n) with
      | some e' => rfl
      | none =>
        simp only [Std.HashMap.getElem?_insert, beq_iff_eq, hxn, ↓reduceIte]

/-- X6's split = `EntryOf`: a record's constants are exactly its own fields' constants. -/
theorem mem_entries (d : DeclF) (e : Entry) : e ∈ entries d ↔ EntryOf d e := by
  cases d with
  | induct cs rs ts =>
    simp only [entries, EntryOf, List.mem_append, List.mem_map]
    constructor
    · rintro ((⟨x, hx, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨r, hr, rfl⟩)
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
      · exact Or.inr (Or.inr ⟨r, hr, rfl⟩)
    · rintro (⟨x, hx, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨r, hr, rfl⟩)
      · exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
      · exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
      · exact Or.inr ⟨r, hr, rfl⟩
  | _ => simp [entries, EntryOf]

/-- `Named` = membership in the records' constants (the index's input). -/
theorem named_iff {t : Tables} {n : Lean.Name} {e : Entry} :
    Named t n e ↔ e ∈ t.rawDecls.toList.flatMap entries ∧ t.names[e.name]? = some n := by
  simp only [Named, List.mem_flatMap, mem_entries]

/-- On an export the reader accepts, the index finds exactly the named constant. -/
theorem viewOf_get {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    (n : Lean.Name) (e : Entry) : (viewOf t).byName[n]? = some e ↔ Named t n e := by
  have ho := entriesOk_read h
  have hn : ((t.rawDecls.toList.flatMap entries).map fun e => t.names[e.name]?).Nodup := by
    rw [ho.names]
    have h2 := List.nodup_iff_pairwise_ne.1 ho.nodup
    rw [List.pairwise_map] at h2
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact h2.imp fun hne heq => hne (Option.some.inj heq)
  have key := @inj_of_nodup_map _ _ _ _ hn
  rw [named_iff]
  show (nameIndex t (t.rawDecls.toList.flatMap entries))[n]? = some e ↔ _
  unfold nameIndex
  rw [nameIndex_fold t _ {} hn (entriesOk_bound ho) n]
  constructor
  · intro hg
    cases hf : (t.rawDecls.toList.flatMap entries).find? (fun e => t.names[e.name]? == some n) with
    | none =>
      rw [hf] at hg
      simp at hg
    | some e' =>
      rw [hf] at hg
      cases hg
      exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  · rintro ⟨he, hn'⟩
    have hs :
        ((t.rawDecls.toList.flatMap entries).find? fun e => t.names[e.name]? == some n).isSome :=
      List.find?_isSome.2 ⟨e, he, by simp [hn']⟩
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hs
    rw [he']
    have hm := List.mem_of_find?_eq_some he'
    have hp := List.find?_some he'
    simp only [beq_iff_eq] at hp
    rw [key hm he (hp.trans hn'.symm)]

/-- U7 X6 + X8 `viewLookup`. -/
theorem view_lookup (githash version : String) (b : ByteArray) (t : Tables) (n : Lean.Name)
    (e : Entry) :
    readTables githash version b = .ok t → ((viewOf t).byName[n]? = some e ↔ Named t n e) :=
  fun h => viewOf_get h n e

end FvdepAudit.Judge.Proof
