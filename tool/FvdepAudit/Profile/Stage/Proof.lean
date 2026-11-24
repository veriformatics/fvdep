import FvdepAudit.Profile.Stage.Spec
import FvdepAudit.Profile.Walk.Proof

/-! U6 C2 at a module's stages: the folded body step = the spec's body event (over `walk_first`),
the header stage = the head of the spec's header findings. -/

namespace FvdepAudit.Profile.Stage.Proof

open FvdepCore.Profile FvdepAudit.Profile.Walk.Spec FvdepAudit.Profile.Stage.Spec
open FvdepAudit.Profile.Walk.Proof

/-! ## The body stage -/

theorem next_eq (sc : Scopes) : ∀ t : Tree, next sc t = nextScopes sc t
  | .node _ _ => rfl
  | .atom _ _ => rfl
  | .ident _ _ => rfl
  | .missing => rfl

theorem fold_event (s : Subject) :
    ∀ (items : List Item) (st : State),
      (items.foldl (step s) st).event =
        match st.event with
        | some e => some e
        | none => bodyEvent s st.scopes items
  | [], st => by
    simp only [List.foldl_nil]
    cases st.event <;> rfl
  | it :: rest, st => by
    rw [List.foldl_cons, fold_event s rest (step s st it)]
    cases he : st.event with
    | some e =>
      have hs : step s st it = st := by cases it <;> simp [step, he]
      rw [hs, he]
    | none =>
      cases it with
      | tree t start =>
        simp only [step, he, walk_first, Scopes.ns, bodyEvent]
        cases (findings s st.scopes.flatten start t).head? with
        | some f => rfl
        | none => simp [next_eq]
      | stop e => simp [step, he, bodyEvent]

/-- C1 (`bodyFirst`). -/
theorem body_first (s : Subject) (items : List Item) :
    (items.foldl (step s) State.init).event =
      FvdepAudit.Profile.Stage.Spec.bodyEvent s [] items := fold_event s items State.init

/-! ## The header stage -/

theorem nameOk_eq (role : Role) (m : String) : nameOk role m = nameAdmitted role m := by
  unfold nameOk nameAdmitted
  cases role <;> cases m.splitOn "." <;> simp [Bool.not_or]

theorem importOk_eq (role : Role) (lib batch : List String) (self : String) (n : List String) :
    importOk role lib batch self n = importAdmitted role lib batch self n := by
  cases role <;> simp [importOk, importAdmitted, Bool.or_assoc]

/-- The header stage's location = the spec's (`locate` reads `firstPos` = `leafPos`). -/
theorem locate_headerLoc (t : Tree) (anc : List Tree) : locate ⟨1, 0⟩ t anc = headerLoc t anc := by
  have h : (Tree.firstPos : Tree → Option Pos) = leafPos := funext firstPos_leafPos
  unfold locate headerLoc
  rw [h]
  cases (t :: anc).findSome? leafPos <;> rfl

theorem importFinding_eq (role : Role) (lib batch : List String) (self : String) (anc : List Tree)
    (t : Tree) :
    importFinding role lib batch self ⟨1, 0⟩ anc t =
      (importRules role lib batch self anc t).head? := by
  simp only [importFinding, importRules, locate_headerLoc, importOk_eq, reservedComponent_eq,
    found_eq]
  cases importParts t with
  | none => rfl
  | some x =>
    rcases x with ⟨md, n, q⟩
    cases md with
    | some a => simp
    | none =>
      by_cases ha : importAdmitted role lib batch self n = true <;>
        rcases hr : firstReserved false n with _ | c <;>
        simp [ha, hr]

/-- C1 + I1 + I2 + I3 (a) + K0' (`headerFirst`). -/
theorem header_first (role : Role) (lib batch : List String) (self : String) (h : Tree) :
    header role lib batch self h =
      (FvdepAudit.Profile.Stage.Spec.headerRules role lib batch self h).head? := by
  simp only [header, headerRules, nameOk_eq, found_eq, locate_headerLoc]
  by_cases hn : nameAdmitted role self = true
  · simp only [hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    cases headerParts h with
    | none => rfl
    | some x =>
      rcases x with ⟨m, p, imps⟩
      simp only [slotRules]
      cases optSlot m with
      | none => rfl
      | some om =>
        cases om with
        | some t => rfl
        | none =>
          cases optSlot p with
          | none => rfl
          | some op =>
            cases op with
            | some t => rfl
            | none =>
              simp only [List.nil_append, List.head?_flatMap]
              congr 1
              funext t
              exact importFinding_eq role lib batch self [.node ["null"] imps, h] t
  · simp [hn]

end FvdepAudit.Profile.Stage.Proof
