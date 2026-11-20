import FvdepCore.Evidence
import FvdepCore.Index.Registry
import FvdepCore.Library.Limits
import FvdepCore.Manifest.Tree
import FvdepCore.Project

/-! Effect plans (contract `docs/contracts/U2-core.md` X1): what fvdep does, as data. A command
builds a `Plan`; `FvdepIO.execute` runs it; theorems quantify over every response an effect may get
(`Runs`), so they hold whatever the file system or the terminal does. Effects + responses are plain
(not indexed by a response type): inverting a run then never meets an equation between two types. -/

namespace FvdepCore.Index

open Lean FvdepCore.Index.Registry

/-- Why `libraryFacts` (contract U4 C1) produced no observations: the build's first error line, or
the load's reason. -/
inductive FactsFailure where
  | build (line : String)
  | load (reason : String)

/-- `libraryFacts`' observations (U4 C8 boundary): the facts (C2–C5; ABI application types +
spec-type comparisons included), each `FvdepProofs` theorem's `collectAxioms`, the structure fields
of the registry record types, and the kernel's verdict on each certificate literal (C2: by list
constant). -/
structure Observed where
  facts : Facts
  axioms : List (Name × List Name)
  fields : List (Name × Option (List String))
  certified : List (Name × Bool)

end FvdepCore.Index

namespace FvdepCore.Oracle

/-- A bounded read (a project's `fvdep.toml`, stdin): its bytes, absent, more than the cap, or the
failure's reason. -/
inductive FileRead where
  | bytes (b : ByteArray)
  | absent
  | tooLarge
  | failed (reason : String)

/-- U5b L: a served snapshot: its commit, published tree, the notice (a head served after a
transport failure), `lean-toolchain`'s + `index.json`'s bytes. -/
structure Snap where
  commit : String
  tree : String
  notice : Option String
  toolchain : ByteArray
  index : ByteArray

/-- One library module as K's discovery read it (K2): its name, source bytes + direct imports. -/
structure Src where
  module : String
  bytes : ByteArray
  imports : List String

/-- An infrastructure cause (U5 P5, K): its interface code + detail. -/
structure Cause where
  code : FvdepCore.Evidence.Infra
  detail : String

end FvdepCore.Oracle

namespace FvdepCore

/-- The project files fvdep writes (Decisions `Data formats`; `index` = a library working copy's
`index.json`, contract U4 C1). -/
inductive ProjectFile where
  | lock
  | manifest
  | index
  deriving DecidableEq, Repr

/-- One effect. Output writes have no failure response: a failed write of fvdep's own output
interrupts the run (`docs/interface.md` §2: exit 2). An ordinary file failure is an `Except` the
plan handles. -/
inductive Eff where
  | out (s : String)
  | err (s : String)
  | read (f : ProjectFile)
  | replace (f : ProjectFile) (bytes : ByteArray)
  /-- U4 C1: is the working directory a library working copy (`lean-toolchain` +
  `Fvdep/Registry.lean`), + `lean-toolchain`'s bytes. -/
  | probe
  /-- U4 C1 `libraryFacts`: build the working copy afresh, load it, observe it. -/
  | libraryFacts
  /-- U4 C1 `replay`: the toolchain's `leanchecker` over the built library's modules. -/
  | replay
  /-- U5b P1: `fvdep.toml` as `lstat` sees it in `--project <dir>`, else in each ancestor of the
  working directory, nearest first. -/
  | project (explicit : Option String)
  /-- U5b P2: the chosen project's `fvdep.toml` (at most 64 KiB + 1 bytes). -/
  | manifest (dir : String)
  /-- U3 T1: Lake's parse of `fvdep.toml`'s text, then `ofLake`. -/
  | parse (text : String)
  /-- U5b L: the snapshot of `pin` (`none` = the source's head) under the library limits. -/
  | snapshot (pin : Option String) (lim : FvdepCore.Library.Limits)
  /-- U5b E2 + K2: the library modules `roots` reach in the served tree (sources + imports). -/
  | closure (tree : String) (roots : List String)
  /-- U5b O1 + K: T1's tools, the closure of `roots` filled, one view (its handle back). -/
  | view (tree : String) (roots : List String)
  /-- U5b E3–E4 + U5 P4: an export step over the view `view`. -/
  | leanexport (view : String) (imports roots : List String)
  /-- U5b V1: stdin to its end, at most `cap` bytes. -/
  | stdin (cap : Nat)
  /-- U5b V3: the evaluation step over the view `view` (`driver` + `requests`, `seconds`). -/
  | evaluate (view : String) (driver : String) (requests : ByteArray) (seconds : Nat)
  /-- Bytes on stdout (the oracle's replies). -/
  | outBytes (b : ByteArray)

/-- What an effect answered. -/
inductive Response where
  | done
  | read (r : Except String (Option ByteArray))
  | replace (r : Except String Unit)
  /-- `none` = no library working copy here; `some` = `lean-toolchain`'s bytes. -/
  | probe (r : Except String (Option ByteArray))
  | facts (r : Except FvdepCore.Index.FactsFailure FvdepCore.Index.Observed)
  /-- `none` = every module replayed; `some (module, kernel line)` = a rejection. -/
  | replay (r : Except String (Option (String × String)))
  | project (seen : FvdepCore.Project.Seen)
  | manifest (r : FvdepCore.Oracle.FileRead)
  | parse (r : Except FvdepCore.Manifest.ParseError FvdepCore.Manifest.Tree)
  | snapshot (r : Except String FvdepCore.Oracle.Snap)
  | closure (r : Except String (List FvdepCore.Oracle.Src))
  | view (r : Except FvdepCore.Oracle.Cause String)
  | leanexport (r : Except FvdepCore.Oracle.Cause ByteArray)
  | stdin (r : FvdepCore.Oracle.FileRead)
  | evaluate (r : Except FvdepCore.Oracle.Cause ByteArray)

/-- The responses an effect may get: `done` for an output write, a read result for a read, a
replace result for a replace, an observation effect's own kind for it. -/
def Fits : Eff → Response → Prop
  | .out _, .done | .err _, .done => True
  | .read _, .read _ => True
  | .replace _ _, .replace _ => True
  | .probe, .probe _ => True
  | .libraryFacts, .facts _ => True
  | .replay, .replay _ => True
  | .project _, .project _ => True
  | .manifest _, .manifest _ => True
  | .parse _, .parse _ => True
  | .snapshot _ _, .snapshot _ => True
  | .closure _ _, .closure _ => True
  | .view _ _, .view _ => True
  | .leanexport _ _ _, .leanexport _ => True
  | .stdin _, .stdin _ => True
  | .evaluate _ _ _ _, .evaluate _ => True
  | .outBytes _, .done => True
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

theorem fits_outBytes (b : ByteArray) (resp : Response) :
    Fits (.outBytes b) resp ↔ resp = .done := by cases resp <;> simp [Fits]

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
