import FvdepAudit.Judge.Graph.Proof
import FvdepCore.Judge.Plan

/-! Proofs: J's stages (contract `docs/contracts/U7-judge.md` J1, X8) — the kernel phase is reached
only on two read + parsed exports whose statement, graph + axioms hold (S, G, A's specs), and on
such exports it is reached unless a stage ran out of W (completeness up to the budget). -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Evidence FvdepCore.Export FvdepCore.Judge FvdepAudit.Judge.Spec
  FvdepAudit.Judge.Statement.Spec FvdepAudit.Judge.Graph.Spec

/-- U7 J1 `stagesSound`. -/
theorem stages_sound (p : VProfile) (githash version : String) (r : Request) (d1 d2 : Digest)
    (e1 e2 : Read) :
    (stages p githash version r d1 d2 e1 e2).kernels = true →
      ∃ b1 b2 t1 t2 names,
        e1 = .ok b1 ∧
          e2 = .ok b2 ∧
          readTables githash version b1 = .ok t1 ∧
          readTables githash version b2 = .ok t2 ∧
          Holds t1 t2 r ∧
          GraphHolds t1 t2 r ∧
          OpaqueHolds t1 r p.opaques ∧
          ProofHolds t2 r ∧
          (stages p githash version r d1 d2 e1 e2).obs =
            [.statement d1 d2 true, .graph d1 d2 true, .axioms d2 names] ∧
          (∀ a, a ∈ names ↔ ∃ c, ReachedAxiom t2 r c ∧ axiomText c = a) ∧
          (∀ a ∈ names, a ∈ p.allowlist) ∧
          ∀ c, ReachedAxiom t2 r c → axiomText c ∈ p.allowlist := by
  intro hk
  rcases e1 with why | b1
  · simp [stages] at hk
  rcases h1 : readTables githash version b1 with f | t1
  · simp [stages, h1] at hk
  rcases e2 with why | b2
  · simp [stages, h1] at hk
  rcases h2 : readTables githash version b2 with f | t2
  · simp [stages, h1, h2] at hk
  rcases hs : statement (viewOf t1) (viewOf t2) r p.work {} with ⟨_ | c | c | _, fuel, memo⟩
  rotate_left
  · simp [stages, h1, h2, hs] at hk
  · simp [stages, h1, h2, hs] at hk
  · simp [stages, h1, h2, hs] at hk
  have S :=
    statement_exact githash version b1 b2 t1 t2 r p.work {} (.matched, fuel, memo) h1 h2 (by simp)
      hs
  obtain ⟨hH, hMemo⟩ := S.2.1 rfl
  rcases hg : graph (viewOf t1) (viewOf t2) r p.opaques fuel memo with
    ⟨_ | c | c | _, axs, fuel', memo'⟩
  rotate_left
  · simp [stages, h1, h2, hs, hg] at hk
  · simp [stages, h1, h2, hs, hg] at hk
  · simp [stages, h1, h2, hs, hg] at hk
  have G :=
    graph_exact githash version b1 b2 t1 t2 r p.opaques fuel memo (.matched, axs, fuel', memo') h1
      h2 hMemo hg
  obtain ⟨gH, oH, pH, hax, _, _⟩ := G.1 rfl
  have hall : ∀ a ∈ axs.map axiomText, a ∈ p.allowlist := by
    simp only [stages, h1, h2, hs, hg, List.all_eq_true] at hk
    intro a ha
    simpa using hk a ha
  refine ⟨b1, b2, t1, t2, axs.map axiomText, rfl, rfl, h1, h2, hH, gH, oH, pH, ?_, ?_, hall, ?_⟩
  · simp [stages, h1, h2, hs, hg]
  · intro a
    simp only [List.mem_map]
    exact ⟨fun ⟨c, hc, he⟩ => ⟨c, (hax c).1 hc, he⟩, fun ⟨c, hc, he⟩ => ⟨c, (hax c).2 hc, he⟩⟩
  · intro c hc
    exact hall _ (List.mem_map.2 ⟨c, (hax c).2 hc, rfl⟩)

/-- U7 J1 `stagesComplete`. -/
theorem stages_complete (p : VProfile) (githash version : String) (r : Request) (d1 d2 : Digest)
    (b1 b2 : ByteArray) (t1 t2 : Tables) :
    readTables githash version b1 = .ok t1 →
      readTables githash version b2 = .ok t2 →
      Holds t1 t2 r →
      GraphHolds t1 t2 r →
      OpaqueHolds t1 r p.opaques →
      ProofHolds t2 r →
      (∀ c, ReachedAxiom t2 r c → axiomText c ∈ p.allowlist) →
      (stages p githash version r d1 d2 (.ok b1) (.ok b2)).kernels = true ∨
        (statement (viewOf t1) (viewOf t2) r p.work {}).1 = .exhausted ∨
        ∃ fuel memo,
          statement (viewOf t1) (viewOf t2) r p.work {} = (.matched, fuel, memo) ∧
            (graph (viewOf t1) (viewOf t2) r p.opaques fuel memo).1 = .exhausted := by
  intro h1 h2 hH gH oH pH hA
  rcases hs : statement (viewOf t1) (viewOf t2) r p.work {} with ⟨o, fuel, memo⟩
  have S :=
    statement_exact githash version b1 b2 t1 t2 r p.work {} (o, fuel, memo) h1 h2 (by simp) hs
  rcases S.2.2 hH with hm | he
  · simp only at hm
    subst hm
    obtain ⟨_, hMemo⟩ := S.2.1 rfl
    rcases hg : graph (viewOf t1) (viewOf t2) r p.opaques fuel memo with ⟨og, axs, fuel', memo'⟩
    have G :=
      graph_exact githash version b1 b2 t1 t2 r p.opaques fuel memo (og, axs, fuel', memo') h1 h2
        hMemo hg
    rcases G.2.2 gH oH pH with hm' | he'
    · simp only at hm'
      subst hm'
      obtain ⟨_, _, _, hax, _, _⟩ := G.1 rfl
      left
      simp only [stages, h1, h2, hs, hg, List.all_eq_true]
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      simpa using hA a ((hax a).1 ha)
    · simp only at he'
      subst he'
      exact Or.inr (Or.inr ⟨fuel, memo, rfl, by simp [hg]⟩)
  · simp only at he
    subst he
    exact Or.inr (Or.inl rfl)

end FvdepAudit.Judge.Proof
