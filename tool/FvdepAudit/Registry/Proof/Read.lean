import FvdepAudit.Registry.Proof.Decode

/-! The typed readers (`readRegistry`, `readProofs`) = the spec's denotation through the records'
layouts; the certificate's literals decode back to the values they write. -/

namespace FvdepAudit.Registry.Proof

open Lean FvdepCore.Index.Registry FvdepAudit.Registry.Spec

/-! ## Shapes -/

theorem strOnly_foldl : ∀ (ts : List String) {n : Name}, StrOnly n → StrOnly (ts.foldl Name.str n)
  | [], _, h => h
  | _ :: ts, _, h => strOnly_foldl ts (.str h)

theorem strOnly_of_nameLit {e : Expr} {n : Name} (h : NameLit e n) : StrOnly n := by
  induction h with
  | mdata _ ih => exact ih
  | anonymous => exact .anonymous
  | str _ _ _ ih => exact .str ih
  | mkStrs => exact strOnly_foldl _ .anonymous

theorem fits_vappend {f : Form} {a b : Val} (ha : Fits (.list f) a) (hb : Fits (.list f) b) :
    Fits (.list f) (vappend a b) := by
  generalize hl : Form.list f = l at ha
  induction ha with
  | nil =>
    cases hl
    exact hb
  | cons hh _ _ iht =>
    cases hl
    exact .cons hh (iht rfl)
  | _ => cases hl

theorem fits_of_denotes {F : Facts} {f : Form} {e : Expr} {env : List Expr} {p : List Name}
    {v : Val} (h : Denotes F f e env p v) : Fits f v := by
  induction h with
  | any => exact .any
  | mdata _ _ ih => exact ih
  | letE _ _ ih => exact ih
  | bvar _ _ _ ih => exact ih
  | root _ _ _ _ ih => exact ih
  | str => exact .str
  | anonymous => exact .name .anonymous
  | name hn => exact .name (strOnly_of_nameLit hn)
  | enum hc => exact .enum hc
  | ctor => exact .ctor
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | none => exact .none
  | some _ ih => exact .some ih
  | entry _ _ ih => exact .entry ih
  | nil => exact .nil
  | cons _ _ ihh iht => exact .cons ihh iht
  | append _ _ _ iha ihb => exact fits_vappend iha ihb

/-! ## Lists -/

theorem revElems_listVal : ∀ vs : List Val, revElems (listVal vs) = vs.reverse
  | [] => rfl
  | v :: vs => by simp [listVal, revElems, revElems_listVal vs]

theorem isList_listVal : ∀ vs : List Val, IsList (listVal vs)
  | [] => .nil
  | _ :: vs => .cons (isList_listVal vs)

theorem listVal_revElems {w : Val} (h : IsList w) : listVal (revElems w).reverse = w := by
  induction h with
  | nil => rfl
  | cons _ ih => simp [revElems, listVal, ih]

theorem fits_listVal {f : Form} :
    ∀ {vs : List Val}, Fits (.list f) (listVal vs) → ∀ v ∈ vs, Fits f v
  | [], _ => by simp
  | _ :: _, h => by
    cases h with
    | cons hh ht =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hh
      · exact fits_listVal ht v hv

theorem defValue_iff (F : Facts) (c : Name) (e : Expr) :
    defValue? F c = some e ↔
      ∃ d, F.decls.find? (·.name == c) = some d ∧ d.kind = .defn ∧ d.value = some e := by
  unfold defValue?
  cases hd : F.decls.find? (·.name == c) with
  | none => simp
  | some d =>
    by_cases hk : d.kind = .defn
    · simp [hk]
    · simp [hk]

theorem listOf_exact (F : Facts) (f : Form) (c : Name) (vs : List Val) :
    listOf F f c = .ok vs ↔ ListAt F f c vs := by
  unfold listOf ListAt
  constructor
  · intro h
    split at h
    · rename_i e he
      obtain ⟨d, hd, hk, hv⟩ := (defValue_iff F c e).mp he
      split at h
      · rename_i acc hs
        cases h
        obtain ⟨w, hw, hacc⟩ := (sound F).2 f e [] [c] [] acc hs
        subst hacc
        have hl := (complete hw).1 f rfl
        rw [List.append_nil, listVal_revElems hl]
        exact ⟨d, e, hd, hk, hv, hw⟩
      · cases h
    · cases h
  · rintro ⟨d, e, hd, hk, hv, hw⟩
    have hs := (complete hw).2.1 f rfl []
    rw [(defValue_iff F c e).mpr ⟨d, hd, hk, hv⟩]
    dsimp only
    rw [hs, List.append_nil, revElems_listVal]
    simp

/-! ## Records -/

theorem elems_go_listVal : ∀ (vs acc : List Val), Val.elems.go (listVal vs) acc = acc.reverse ++ vs
  | [], acc => by simp [Val.elems.go, listVal]
  | v :: vs, acc => by simp [Val.elems.go, listVal, elems_go_listVal vs]

theorem elems_listVal (vs : List Val) : (listVal vs).elems = vs := by
  simp [Val.elems, elems_go_listVal]

theorem optD_optVal {α β : Type} (g : α → Val) (f : Val → β) (o : Option α) :
    (optVal g o).optD f = o.map (f ∘ g) := by cases o <;> rfl

theorem entryOf_entryVal (e : Entry) : entryOf (entryVal e) = e := by
  rcases e with ⟨m, id, ver, spec, obls, abi, compat⟩
  simp only [entryOf, entryVal, Val.argD, Val.args, Val.args.go, List.getD_cons_zero,
    List.getD_cons_succ, Val.strD, Val.nameD, elems_listVal, List.map_map, optD_optVal]
  simp [Function.comp_def, Val.nameD, Val.strD, Option.map_id']

theorem noticeOf_noticeVal (n : Notice) : noticeOf (noticeVal n) = n := by
  rcases n with ⟨id, ver, reason, repl⟩
  simp only [noticeOf, noticeVal, Val.argD, Val.args, Val.args.go, List.getD_cons_zero,
    List.getD_cons_succ, Val.strD, optD_optVal]
  simp [Function.comp_def, Val.strD, Option.map_id']

theorem kindOf_kindVal (k : Kind) : kindOf (kindVal k) = k := by cases k <;> decide

theorem removedOf_removedVal (r : Removed) : removedOf (removedVal r) = r := by
  rcases r with ⟨id, ver, k, dig, tc, lc⟩
  simp only [removedOf, removedVal, Val.argD, Val.args, Val.args.go, List.getD_cons_zero,
    List.getD_cons_succ, Val.strD, kindOf_kindVal]

theorem proofsOf_proofsVal (pr : Proofs) : proofsOf (proofsVal pr) = pr := by
  rcases pr with ⟨obls, compat⟩
  simp only [proofsOf, proofsVal, Val.argD, Val.args, Val.args.go, List.getD_cons_zero,
    List.getD_cons_succ, elems_listVal, List.map_map, optD_optVal]
  simp [Function.comp_def, pairOf, pairVal, Val.argD, Val.args, Val.args.go, Val.nameD,
    Option.map_id']

theorem names_of_fits :
    ∀ {w : Val}, Fits (.list .name) w → ∃ ns : List Name, w = listVal (ns.map .name) := by
  intro w h
  generalize hl : Form.list .name = l at h
  induction h with
  | nil => exact ⟨[], rfl⟩
  | cons hh _ _ iht =>
    cases hl
    obtain ⟨ns, rfl⟩ := iht rfl
    cases hh
    exact ⟨_ :: ns, rfl⟩
  | _ => cases hl

theorem optName_of_fits {w : Val} (h : Fits (.opt .name) w) : ∃ o, w = optVal .name o := by
  cases h with
  | none => exact ⟨none, rfl⟩
  | some h' =>
    cases h'
    exact ⟨some _, rfl⟩

theorem optStr_of_fits {w : Val} (h : Fits (.opt .str) w) : ∃ o, w = optVal .str o := by
  cases h with
  | none => exact ⟨none, rfl⟩
  | some h' =>
    cases h'
    exact ⟨some _, rfl⟩

theorem entry_of_fits {v : Val} (h : Fits (.entry moduleFormSpec) v) : ∃ e, v = entryVal e := by
  cases h with
  | @entry _ m w hw =>
    cases hw with
    | app h₁ hcompat =>
      cases h₁ with
      | app h₂ habi =>
        cases h₂ with
        | app h₃ hobls =>
          cases h₃ with
          | app h₄ hspec =>
            cases h₄ with
            | app h₅ hver =>
              cases h₅ with
              | app h₆ hid =>
                cases h₆
                cases hid
                cases hver
                cases hspec
                obtain ⟨ns, rfl⟩ := names_of_fits hobls
                obtain ⟨abi, rfl⟩ := optName_of_fits habi
                obtain ⟨compat, rfl⟩ := optStr_of_fits hcompat
                exact ⟨⟨m, _, _, _, ns, abi, compat⟩, rfl⟩

theorem notice_of_fits {v : Val} (h : Fits noticeFormSpec v) : ∃ n, v = noticeVal n := by
  cases h with
  | app h₁ hrepl =>
    cases h₁ with
    | app h₂ hreason =>
      cases h₂ with
      | app h₃ hver =>
        cases h₃ with
        | app h₄ hid =>
          cases h₄
          cases hid
          cases hver
          cases hreason
          obtain ⟨repl, rfl⟩ := optStr_of_fits hrepl
          exact ⟨⟨_, _, _, repl⟩, rfl⟩

theorem removed_of_fits {v : Val} (h : Fits removedFormSpec v) : ∃ r, v = removedVal r := by
  cases h with
  | app h₁ hlc =>
    cases h₁ with
    | app h₂ htc =>
      cases h₂ with
      | app h₃ hdig =>
        cases h₃ with
        | app h₄ hkind =>
          cases h₄ with
          | app h₅ hver =>
            cases h₅ with
            | app h₆ hid =>
              cases h₆
              cases hid
              cases hver
              cases hdig
              cases htc
              cases hlc
              cases hkind with
              | enum hc =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl
                · exact ⟨⟨_, _, .operation, _, _, _⟩, rfl⟩
                · exact ⟨⟨_, _, .profile, _, _, _⟩, rfl⟩

theorem pairs_of_fits :
    ∀ {w : Val},
      Fits (.list (.app (.app (.app (.app (.ctor ``Prod.mk) .any) .any) .name) .name)) w →
        ∃ xs : List (Name × Name), w = listVal (xs.map pairVal) := by
  intro w h
  generalize hl : Form.list (.app (.app (.app (.app (.ctor ``Prod.mk) .any) .any) .name) .name) =
    l at h
  induction h with
  | nil => exact ⟨[], rfl⟩
  | cons hh _ _ iht =>
    cases hl
    obtain ⟨xs, rfl⟩ := iht rfl
    cases hh with
    | app h₁ hb =>
      cases h₁ with
      | app h₂ ha =>
        cases h₂ with
        | app h₃ ht₂ =>
          cases h₃ with
          | app h₄ ht₁ =>
            cases h₄
            cases ht₁
            cases ht₂
            cases ha
            cases hb
            exact ⟨(_, _) :: xs, rfl⟩
  | _ => cases hl

theorem proofs_of_fits {v : Val} (h : Fits proofsFormSpec v) : ∃ pr, v = proofsVal pr := by
  cases h with
  | app h₁ hcompat =>
    cases h₁ with
    | app h₂ hobls =>
      cases h₂
      obtain ⟨xs, rfl⟩ := pairs_of_fits hobls
      obtain ⟨compat, rfl⟩ := optName_of_fits hcompat
      exact ⟨⟨xs, compat⟩, rfl⟩

/-! ## The typed readers -/

theorem forms_eq :
    moduleForm = moduleFormSpec ∧
      noticeForm = noticeFormSpec ∧
      removedForm = removedFormSpec ∧ proofsForm = proofsFormSpec := ⟨rfl, rfl, rfl, rfl⟩

theorem map_inv {α : Type} (of : Val → α) (val : α → Val) (P : Val → Prop)
    (hinv : ∀ v, P v → val (of v) = v) :
    ∀ (ms : List Val), (∀ m ∈ ms, P m) → (ms.map of).map val = ms
  | [], _ => rfl
  | m :: ms, h => by
    simp only [List.map_cons, hinv m (h m (by simp)),
      map_inv of val P hinv ms (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem fits_of_listAt {F : Facts} {f : Form} {c : Name} {vs : List Val} (h : ListAt F f c vs) :
    ∀ v ∈ vs, Fits f v := by
  obtain ⟨_, _, _, _, _, hw⟩ := h
  exact fits_listVal (fits_of_denotes hw)

theorem readRegistry_exact (F : Facts) (r : Lists) :
    readRegistry F = .ok r ↔ RegistryDenotes F r := by
  unfold readRegistry readRaw RegistryDenotes
  constructor
  · intro h
    cases hm : listOf F (.entry moduleForm) modulesName with
    | error n => simp [hm, bind, Except.bind, Except.map] at h
    | ok ms =>
      cases hp : listOf F .any profilesName with
      | error n => simp [hm, hp, bind, Except.bind, Except.map] at h
      | ok ps =>
        cases hn : listOf F noticeForm noticesName with
        | error n => simp [hm, hp, hn, bind, Except.bind, Except.map] at h
        | ok ns =>
          cases hr : listOf F removedForm removedName with
          | error n => simp [hm, hp, hn, hr, bind, Except.bind, Except.map] at h
          | ok
            rs =>
            simp only [hm, hp, hn, hr, bind, Except.bind, Except.map, pure, Except.pure,
              Except.ok.injEq] at h
            subst h
            have hM := (listOf_exact F _ _ ms).mp hm
            have hN := (listOf_exact F _ _ ns).mp hn
            have hR := (listOf_exact F _ _ rs).mp hr
            refine ⟨?_, ⟨ps, (listOf_exact F _ _ ps).mp hp, rfl⟩, ?_, ?_⟩
            · rw [show (Lists.ofRaw ⟨ms, ps, ns, rs⟩).entries.map entryVal = ms from
                  map_inv entryOf entryVal (Fits (.entry moduleFormSpec))
                    (fun v hv => by
                      obtain ⟨e, rfl⟩ := entry_of_fits hv; rw [entryOf_entryVal])
                    ms (fits_of_listAt hM)]
              exact hM
            · rw [show (Lists.ofRaw ⟨ms, ps, ns, rs⟩).notices.map noticeVal = ns from
                  map_inv noticeOf noticeVal (Fits noticeFormSpec)
                    (fun v hv => by
                      obtain ⟨n, rfl⟩ := notice_of_fits hv; rw [noticeOf_noticeVal])
                    ns (fits_of_listAt hN)]
              exact hN
            · rw [show (Lists.ofRaw ⟨ms, ps, ns, rs⟩).removed.map removedVal = rs from
                  map_inv removedOf removedVal (Fits removedFormSpec)
                    (fun v hv => by
                      obtain ⟨x, rfl⟩ := removed_of_fits hv; rw [removedOf_removedVal])
                    rs (fits_of_listAt hR)]
              exact hR
  · rintro ⟨hM, ⟨ps, hP, hlen⟩, hN, hR⟩
    have hM' : listOf F (.entry moduleForm) modulesName = .ok _ := (listOf_exact F _ _ _).mpr hM
    have hP' : listOf F .any profilesName = .ok _ := (listOf_exact F _ _ _).mpr hP
    have hN' : listOf F noticeForm noticesName = .ok _ := (listOf_exact F _ _ _).mpr hN
    have hR' : listOf F removedForm removedName = .ok _ := (listOf_exact F _ _ _).mpr hR
    rw [hM', hP', hN', hR']
    simp only [bind, Except.bind, Except.map, pure, Except.pure, Except.ok.injEq, Lists.ofRaw,
      List.map_map]
    rcases r with ⟨es, np, nts, rms⟩
    simp only at hlen
    subst hlen
    simp [Function.comp_def, entryOf_entryVal, noticeOf_noticeVal, removedOf_removedVal]

theorem readProofs_exact (F : Facts) (c : Name) (pr : Proofs) :
    readProofs F c = .ok pr ↔ ProofsAt F c pr := by
  unfold readProofs ProofsAt
  constructor
  · intro h
    split at h
    · rename_i e he
      obtain ⟨d, hd, hk, hv⟩ := (defValue_iff F c e).mp he
      cases hdec : decode F proofsForm e [] [c] with
      | error n => simp [hdec, Except.map] at h
      | ok v =>
        simp only [hdec, Except.map, Except.ok.injEq] at h
        have hD := (decode_exact F _ e [] [c] v).mp hdec
        obtain ⟨pr', rfl⟩ := proofs_of_fits (fits_of_denotes hD)
        rw [proofsOf_proofsVal] at h
        subst h
        exact ⟨d, e, hd, hk, hv, hD⟩
    · cases h
  · rintro ⟨d, e, hd, hk, hv, hD⟩
    rw [(defValue_iff F c e).mpr ⟨d, hd, hk, hv⟩]
    dsimp only
    have hd' : decode F proofsForm e [] [c] = .ok (proofsVal pr) :=
      (decode_exact F _ e [] [c] _).mpr hD
    rw [hd']
    simp [Except.map, proofsOf_proofsVal]

/-! ## Re-encoding -/

theorem nameLit_nameExpr {n : Name} (h : StrOnly n) : nameLit? (nameExpr n) = some n := by
  induction h with
  | anonymous => simp [nameExpr, nameLit?]
  | @str p s _ ih =>
    simp only [nameExpr]
    unfold nameLit?
    simp [strLit?, ih]

theorem isList_of_fits {f : Form} {v : Val} (h : Fits (.list f) v) : IsList v := by
  generalize hl : Form.list f = l at h
  induction h with
  | nil => exact .nil
  | cons _ _ _ iht =>
    cases hl
    exact .cons (iht rfl)
  | _ => cases hl

theorem reencode_exact (F : Facts) {f : Form} {v : Val} (hf : Fits f v) (hp : Plain f) :
    (∀ env p, decode F f (reencode f v) env p = .ok v) ∧
      (∀ fe,
        f = .list fe →
          ∀ env p acc, spine F fe (reencode f v) env p acc = .ok (revElems v ++ acc)) := by
  induction hf with
  | str => exact ⟨fun env p => by rw [reencode, decode.eq_def], by simp⟩
  | @name n hn =>
    refine ⟨fun env p => ?_, by simp⟩
    cases hn with
    | anonymous =>
      rw [reencode]
      show decode F .name (.const ``Name.anonymous []) env p = _
      rw [decode.eq_def]
      simp [ownsConst]
    | @str q t hq =>
      have hl := nameLit_nameExpr (n := q.str t) (.str hq)
      simp only [nameExpr] at hl
      rw [reencode, nameExpr, decode.eq_def]
      dsimp only
      rw [hl]
  | enum hc =>
    exact
      ⟨fun env p => by
        rw [reencode, decode.eq_def]; simp [ownsConst, hc], by simp⟩
  | ctor =>
    exact
      ⟨fun env p => by
        rw [reencode, decode.eq_def]; simp [ownsConst], by simp⟩
  | app _ _ ih₁ ih₂ =>
    refine ⟨fun env p => ?_, by simp⟩
    rw [reencode, decode.eq_def]
    simp only [(ih₁ hp.1).1, (ih₂ hp.2).1]
  | none =>
    exact
      ⟨fun env p => by
        rw [reencode, decode.eq_def]; rfl, by simp⟩
  | some _ ih =>
    refine ⟨fun env p => ?_, by simp⟩
    rw [reencode, decode.eq_def]
    simp only [(ih hp).1]
  | @nil
    f =>
    have hn : reencode (.list f) .nil = .app (.const ``List.nil [.zero]) (tyOf f) := by
      simp [reencode, reencodeList]
    have hs :
      ∀ env p acc, spine F f (reencode (.list f) .nil) env p acc = .ok (revElems .nil ++ acc) :=
      fun env p acc => by
      rw [hn, spine]
      rfl
    exact
      ⟨fun env p => decode_of_spine .nil (hs env p), fun fe hfe => by
        cases hfe; exact hs⟩
  | @cons f h t _ ht ihh
    iht =>
    have hl : IsList (.cons h t) := .cons (isList_of_fits ht)
    have hs :
      ∀ env p acc,
        spine F f (reencode (.list f) (.cons h t)) env p acc =
          .ok (revElems (.cons h t) ++ acc) := by
      intro env p acc
      have hh := (ihh hp).1 env p
      have htl := (iht hp).2 f rfl env p (h :: acc)
      rw [reencode] at htl
      rw [reencode, reencodeList, spine, hh]
      dsimp only
      rw [htl]
      simp [revElems]
    exact
      ⟨fun env p => decode_of_spine hl (hs env p), fun fe hfe => by
        cases hfe; exact hs⟩
  | entry => exact absurd hp id
  | any => exact absurd hp id

theorem listLiteral_eq (f : Form) :
    ∀ vs : List Val, listLiteral f vs = reencode (.list f) (listVal vs)
  | [] => by simp [listLiteral, listVal, reencode, reencodeList]
  | v :: vs => by
    have ih := listLiteral_eq f vs
    rw [reencode] at ih
    rw [reencode]
    unfold listLiteral at ih ⊢
    simp only [List.map_cons, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      listVal, reencodeList, ih]

theorem fits_of_elems {f : Form} :
    ∀ {vs : List Val}, (∀ v ∈ vs, Fits f v) → Fits (.list f) (listVal vs)
  | [], _ => .nil
  | v :: vs, h =>
    .cons (h v (by simp)) (fits_of_elems (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- C8 `ReencodeExact`: a list literal the certificate writes decodes back to the values written. -/
theorem listLiteral_exact (F : Facts) (f : Form) (vs : List Val) (env : List Expr) (p : List Name)
    (hp : Plain f) (hv : ∀ v ∈ vs, Fits f v) :
    decode F (.list f) (listLiteral f vs) env p = .ok (listVal vs) := by
  rw [listLiteral_eq]
  exact (reencode_exact F (fits_of_elems hv) hp).1 env p

theorem fits_payload {f : Form} {v : Val} (h : Fits (.entry f) v) : Fits f v.payload := by
  cases h with
  | entry hv => exact hv

theorem listLiteral_nil (F : Facts) (f : Form) (env : List Expr) (p : List Name) :
    decode F (.list f) (listLiteral f []) env p = .ok (listVal []) :=
  (decode_exact F _ _ env p _).mpr Denotes.nil

theorem plain_forms : Plain moduleForm ∧ Plain noticeForm ∧ Plain removedForm := by
  simp [Plain, moduleForm, noticeForm, removedForm, kindForm]

/-- C2's certificate: every list it writes back decodes from its literal to exactly the values
written. -/
theorem certificate_exact (F : Facts) (r : RawLists) (env : List Expr) (p : List Name)
    (h : readRaw F = .ok r) (c : Name) (f : Form) (vs : List Val)
    (hc : (c, f, vs) ∈ certificate r) :
    decode F (.list f) (listLiteral f vs) env p = .ok (listVal vs) := by
  unfold readRaw at h
  cases hm : listOf F (.entry moduleForm) modulesName with
  | error n => simp [hm, bind, Except.bind] at h
  | ok ms =>
    cases hp : listOf F .any profilesName with
    | error n => simp [hm, hp, bind, Except.bind] at h
    | ok ps =>
      cases hn : listOf F noticeForm noticesName with
      | error n => simp [hm, hp, hn, bind, Except.bind] at h
      | ok ns =>
        cases hr : listOf F removedForm removedName with
        | error n => simp [hm, hp, hn, hr, bind, Except.bind] at h
        | ok
          rs =>
          simp only [hm, hp, hn, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hM := fits_of_listAt ((listOf_exact F _ _ ms).mp hm)
          have hN := fits_of_listAt ((listOf_exact F _ _ ns).mp hn)
          have hR := fits_of_listAt ((listOf_exact F _ _ rs).mp hr)
          obtain ⟨pM, pN, pR⟩ := plain_forms
          unfold certificate at hc
          rcases List.mem_append.mp hc with hc | hc
          · rcases List.mem_append.mp hc with hc | hc
            · simp only [List.mem_singleton, Prod.mk.injEq] at hc
              obtain ⟨-, rfl, rfl⟩ := hc
              exact
                listLiteral_exact F _ _ env p pM fun v hv => by
                  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
                  exact fits_payload (hM w hw)
            · split at hc
              · simp only [List.mem_singleton, Prod.mk.injEq] at hc
                obtain ⟨-, rfl, rfl⟩ := hc
                exact listLiteral_nil F _ env p
              · simp at hc
          · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
            rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
            · exact listLiteral_exact F _ _ env p pN hN
            · exact listLiteral_exact F _ _ env p pR hR

end FvdepAudit.Registry.Proof
