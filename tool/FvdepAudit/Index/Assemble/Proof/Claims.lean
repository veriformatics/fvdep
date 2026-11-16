import FvdepAudit.Index.Assemble.Proof.Basic

/-! `assemble` against the layout written apart (`AssembleSpec`): after `validate` accepted the
lists, it returns exactly the index value + warnings the spec describes; it refuses exactly when no
such statuses exist (C-rules-b `StatusExact`). Header = the ledger statement. -/

namespace FvdepAudit.Index.Assemble.Proof

open Lean FvdepCore.Json FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Statuses FvdepCore.Index.Assemble
open FvdepAudit.Doc.Spec FvdepAudit.Index.Spec FvdepAudit.Index.Rules.Spec
open FvdepAudit.Index.Statuses.Spec FvdepAudit.Index.Assemble.Spec
open FvdepAudit.Index.Statuses.Proof FvdepAudit.Index.Rules.Proof

theorem notice_eq : NoticeV = noticeValue := by
  funext n
  obtain ⟨_, _, _, r⟩ := n
  cases r <;> rfl

theorem removed_eq : RemovedV = removedValue := by
  funext r
  obtain ⟨_, _, k, _, _, _⟩ := r
  cases k <;> rfl

/-- C6's order on the sorted statuses of a validated registry. -/
theorem sortOps_before {F : Facts} {ax : List (Name × List Name)} {l : Lists}
    {rs : List (Entry × EntryStatus)} (hv : RegistryValid F l) (hs : StatusesSpec F ax l rs) :
    (sortOps rs).Pairwise fun a b => IdVersionBefore a.1.id a.1.version b.1.id b.1.version := by
  have hmem : ∀ a ∈ sortOps rs, EntryVersion.parse a.1.version ≠ none := fun a ha =>
    version_canonical hv (statuses_member hs ((sortOps_perm rs).mem_iff.mp ha)).1
  have hnodup : ((sortOps rs).map fun a => (a.1.id, a.1.version)).Nodup := by
    rw [((sortOps_perm rs).map _).nodup_iff]
    have e :
      (rs.map fun a => (a.1.id, a.1.version)) = l.entries.map fun e => (e.id, e.version) := by
      rw [← statuses_fst hs, List.map_map]
      rfl
    rw [e]
    exact entries_distinct hv
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hnodup
  exact
    ((sortOps_keyed rs).and hnodup).imp_of_mem fun ha hb h =>
      before_of_keyLe (hmem _ ha) (hmem _ hb) h.2 h.1

/-- U4 C4 + C6 + C9 + C8 `AssembleExact`: after `validate` accepted the lists, `assemble` returns
exactly the index value + warnings written apart (`AssembleSpec`). -/
theorem assemble_exact (F : Facts) (ax : List (Name × List Name)) (l : Lists) (raw : String)
    (h : ByteArray → String) (hv : validate F l = none) (v : Value) (ws : List Warning) :
    assemble F ax l raw h = .ok (v, ws) ↔ AssembleSpec F ax l raw h v ws := by
  have hr := (validate_accepts F l).mp hv
  have hops :
    ∀ rs,
      StatusesSpec F ax l rs →
        ∀ x ∈ sortOps rs,
          ∀ o ∈ x.2.obligations.map (·.1), ∃ name, o = .str (specModule x.1) name := by
    intro rs hs x hx o ho
    obtain ⟨hx₁, hx₂⟩ := statuses_member hs ((sortOps_perm rs).mem_iff.mp hx)
    rw [entrySpec_names hx₂] at ho
    exact obligation_shape hr hx₁ o ho
  constructor
  · intro hA
    unfold assemble at hA
    cases hs : statuses F ax l with
    | error f => simp [hs, Except.map] at hA
    | ok rs =>
      simp only [hs, Except.map, Except.ok.injEq, Prod.mk.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      have hspec := (statuses_exact F ax l hv rs).mp hs
      refine
        ⟨rs, sortOps rs, (sortOps rs).map (operationValue h F), trimText raw, hspec,
          sortOps_perm rs, sortOps_before hr hspec, by simp, fun p hp => ?_, trimText_trimmed raw,
          ?_, rfl⟩
      · obtain ⟨hp₁, hp₂⟩ := zip_map_self (operationValue h F) (sortOps rs) p hp
        exact (operationV_iff h F p.1 (hops rs hspec p.1 hp₁) p.2).mpr hp₂
      · rw [notice_eq, removed_eq]
        rfl
  · rintro ⟨rs, ps, ops, tc, hspec, hperm, hpair, hlen, hall, htrim, rfl, rfl⟩
    have hs := (statuses_exact F ax l hv rs).mpr hspec
    have hps : ps = sortOps rs :=
      List.Perm.eq_of_pairwise (le := fun a b =>
        IdVersionBefore a.1.id a.1.version b.1.id b.1.version)
        (fun _ _ _ _ h₁ h₂ => absurd h₂ (before_asymm h₁)) hpair (sortOps_before hr hspec)
        (hperm.trans (sortOps_perm rs).symm)
    subst hps
    have hops' : ops = (sortOps rs).map (operationValue h F) := by
      apply List.ext_getElem (by simp [hlen])
      intro n h₁ h₂
      have hm : ((sortOps rs)[n]'(by omega), ops[n]) ∈ (sortOps rs).zip ops := by
        rw [List.mem_iff_getElem]
        exact
          ⟨n, by
            simp; omega, by simp⟩
      have := (operationV_iff h F _ (hops rs hspec _ (List.getElem_mem _)) _).mp (hall _ hm)
      simpa using this
    subst hops'
    have htc := trimmed_eq htrim
    subst htc
    unfold assemble
    rw [hs, notice_eq, removed_eq]
    rfl

end FvdepAudit.Index.Assemble.Proof
