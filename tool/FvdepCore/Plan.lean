/-! Effect plans (contract `docs/contracts/U2-core.md` X1): what fvdep does, as data. A command
builds a `Plan`; `FvdepIO.execute` runs it; theorems quantify over every response an effect may get
(`Runs`), so they hold whatever the file system or the terminal does. Effects + responses are plain
(not indexed by a response type): inverting a run then never meets an equation between two types. -/

namespace FvdepCore

/-- The project files fvdep writes (Decisions `Data formats`). -/
inductive ProjectFile where
  | lock
  | manifest
  deriving DecidableEq, Repr

/-- One effect. Output writes have no failure response: a failed write of fvdep's own output
interrupts the run (`docs/interface.md` §2: exit 2). An ordinary file failure is an `Except` the
plan handles. -/
inductive Eff where
  | out (s : String)
  | err (s : String)
  | read (f : ProjectFile)
  | replace (f : ProjectFile) (bytes : ByteArray)

/-- What an effect answered. -/
inductive Response where
  | done
  | read (r : Except String (Option ByteArray))
  | replace (r : Except String Unit)

/-- The responses an effect may get: `done` for an output write, a read result for a read, a
replace result for a replace. -/
def Fits : Eff → Response → Prop
  | .out _, .done | .err _, .done => True
  | .read _, .read _ => True
  | .replace _ _, .replace _ => True
  | _, _ => False

/-- A program over `Eff`: a result, or one effect + what to do with its response. -/
inductive Plan (α : Type) where
  | pure (a : α)
  | step (e : Eff) (k : Response → Plan α)

namespace Plan

def bind {α β : Type} : Plan α → (α → Plan β) → Plan β
  | .pure a, f => f a
  | .step e k, f => .step e fun r => bind (k r) f

instance : Monad Plan where
  pure := .pure
  bind := bind

/-- `Runs p evs r`: running `p` may perform exactly the effects of `evs`, each getting the response
beside it (any response that fits), and end with `r`: `some a` when it completes, `none` when
interrupted (a failed output write, a signal) after that prefix. -/
inductive Runs {α : Type} : Plan α → List (Eff × Response) → Option α → Prop where
  | done (a : α) : Runs (.pure a) [] (some a)
  | stop (e : Eff) (k : Response → Plan α) : Runs (.step e k) [] none
  |
  step (e : Eff) (k : Response → Plan α) (resp : Response) (evs : List (Eff × Response))
    (r : Option α) : Fits e resp → Runs (k resp) evs r → Runs (.step e k) ((e, resp) :: evs) r

/-- A finished plan: no effect, its value. -/
theorem runs_pure_iff {α : Type} (a : α) (evs : List (Eff × Response)) (r : Option α) :
    Runs (.pure a) evs r ↔ evs = [] ∧ r = some a := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .done a

/-- One step: interrupted before the effect, or the effect with a fitting response, then the
rest. -/
theorem runs_step_iff {α : Type} (e : Eff) (k : Response → Plan α) (evs : List (Eff × Response))
    (r : Option α) :
    Runs (.step e k) evs r ↔
      evs = [] ∧ r = none ∨
        ∃ resp rest, evs = (e, resp) :: rest ∧ Fits e resp ∧ Runs (k resp) rest r := by
  constructor
  · intro h
    cases h with
    | stop => exact .inl ⟨rfl, rfl⟩
    | step _ _ resp rest _ hf hr => exact .inr ⟨resp, rest, rfl, hf, hr⟩
  · rintro (⟨rfl, rfl⟩ | ⟨resp, rest, rfl, hf, hr⟩)
    · exact .stop e k
    · exact .step e k resp rest r hf hr

theorem fits_out (s : String) (resp : Response) : Fits (.out s) resp ↔ resp = .done := by
  cases resp <;> simp [Fits]

theorem fits_err (s : String) (resp : Response) : Fits (.err s) resp ↔ resp = .done := by
  cases resp <;> simp [Fits]

/-- A completed run of `p >>= f` = a completed run of `p`, then a completed run of `f` on its
value. -/
theorem runs_bind_some {α β : Type} (p : Plan α) (f : α → Plan β) (evs : List (Eff × Response))
    (b : β) :
    Runs (p.bind f) evs (some b) ↔
      ∃ evs₁ evs₂ a, evs = evs₁ ++ evs₂ ∧ Runs p evs₁ (some a) ∧ Runs (f a) evs₂ (some b) := by
  induction p generalizing evs with
  | pure a =>
    constructor
    · intro h
      exact ⟨[], evs, a, rfl, .done a, h⟩
    · rintro ⟨e₁, e₂, a', rfl, hp, hf⟩
      cases hp
      exact hf
  | step e k ih =>
    constructor
    · intro h
      cases h with
      | step _ _ resp rest _ hf
        hr =>
        obtain ⟨e₁, e₂, a, rfl, hp, hq⟩ := (ih resp rest).mp hr
        exact ⟨(e, resp) :: e₁, e₂, a, rfl, .step e k resp e₁ (some a) hf hp, hq⟩
    · rintro ⟨e₁, e₂, a, rfl, hp, hq⟩
      cases hp with
      | step _ _ resp rest _ hf hr =>
        exact
          .step e _ resp (rest ++ e₂) (some b) hf
            ((ih resp (rest ++ e₂)).mpr ⟨rest, e₂, a, rfl, hr, hq⟩)

/-- An interrupted run of `p >>= f` = an interrupted run of `p`, or a completed run of `p` followed
by an interrupted run of `f` on its value. -/
theorem runs_bind_none {α β : Type} (p : Plan α) (f : α → Plan β) (evs : List (Eff × Response)) :
    Runs (p.bind f) evs none ↔
      Runs p evs none ∨
        ∃ evs₁ evs₂ a, evs = evs₁ ++ evs₂ ∧ Runs p evs₁ (some a) ∧ Runs (f a) evs₂ none := by
  induction p generalizing evs with
  | pure a =>
    constructor
    · intro h
      exact .inr ⟨[], evs, a, rfl, .done a, h⟩
    · rintro (hp | ⟨e₁, e₂, a', rfl, hp, hf⟩)
      · cases hp
      · cases hp
        exact hf
  | step e k ih =>
    constructor
    · intro h
      cases h with
      | stop => exact .inl (.stop e k)
      | step _ _ resp rest _ hf
        hr =>
        rcases (ih resp rest).mp hr with hp | ⟨e₁, e₂, a, rfl, hp, hq⟩
        · exact .inl (.step e k resp rest none hf hp)
        · exact .inr ⟨(e, resp) :: e₁, e₂, a, rfl, .step e k resp e₁ (some a) hf hp, hq⟩
    · rintro (hp | ⟨e₁, e₂, a, rfl, hp, hq⟩)
      · cases hp with
        | stop => exact .stop e _
        | step _ _ resp rest _ hf hr =>
          exact .step e _ resp rest none hf ((ih resp rest).mpr (.inl hr))
      · cases hp with
        | step _ _ resp rest _ hf hr =>
          exact
            .step e _ resp (rest ++ e₂) none hf
              ((ih resp (rest ++ e₂)).mpr (.inr ⟨rest, e₂, a, rfl, hr, hq⟩))

end Plan

end FvdepCore
