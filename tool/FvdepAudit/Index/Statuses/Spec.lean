import FvdepAudit.Index.Rules.Spec
import FvdepAudit.Registry.Spec
import FvdepCore.Index.Statuses

/-! C5's statuses + C9's warnings + C4's framed input, written apart (contract
`docs/contracts/U4-library.md` C4, C5, C9): a mapped theorem's outcome = the first failing C5
condition, else its status from the observed axioms outside the standard three, strictly ascending
(`Judged`); an obligation's + the compat edge's outcome under the entry's proof registry
(`RegistryOf`: C2's `ProofsAt`); an entry's statuses + warnings in C9's order (`EntrySpec`). Shared
with the shipped code: `proofsName` (naming data), `Why` + `Warning` (C9's vocabulary), `subject`,
`libDecl?`, `listedAt?`, `erase`, `modulePath`, `modFacts?` (C-rules-a). -/

namespace FvdepAudit.Index.Statuses.Spec

open Lean FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses
open FvdepAudit.Registry.Spec FvdepAudit.Index.Rules.Spec

/-- `d` = the facts' first declaration named `t`. -/
def DeclOf (F : Facts) (t : Name) (d : Decl) : Prop :=
  ∃ pre post, F.decls = pre ++ d :: post ∧ d.name = t ∧ ∀ x ∈ pre, x.name ≠ t

/-- `raw` = the axiom list observed first for `t`. -/
def AxiomsOf (ax : List (Name × List Name)) (t : Name) (raw : List Name) : Prop :=
  ∃ pre post, ax = pre ++ (t, raw) :: post ∧ ∀ x ∈ pre, x.1 ≠ t

/-- C5 + C6: `a` = the printed names of `raw` outside {propext, Classical.choice, Quot.sound},
strictly ascending (code point order = UTF-8 byte order). -/
def Extra (raw : List Name) (a : List String) : Prop :=
  a.Pairwise (· < ·) ∧
    ∀ s,
      s ∈ a ↔ ∃ n ∈ raw, n ≠ ``propext ∧ n ≠ ``Classical.choice ∧ n ≠ ``Quot.sound ∧ n.toString = s

/-- C5: `sorryAx` among the axioms → open; none → proven; else trusts. -/
def StatusOf (a : List String) (s : Status) : Prop :=
  "sorryAx" ∈ a ∧ s = .«open» ∨
    "sorryAx" ∉ a ∧ a = [] ∧ s = .proven ∨ "sorryAx" ∉ a ∧ a ≠ [] ∧ s = .trusts

/-- C5: a mapped theorem `t` against the statement `Ok`: the first failing condition (a name the
facts lack: outside both libraries ⇒ outside `FvdepProofs`), else (status, axioms) from its observed
axiom list. -/
inductive Judged (F : Facts) (ax : List (Name × List Name)) (t : Name) (Ok : Expr → Prop) :
    Status × List String × Option Why → Prop
  | absent : (∀ d ∈ F.decls, d.name ≠ t) → Judged F ax t Ok (.«open», [], some (.outside t))
  |
  notTheorem {d : Decl} :
    DeclOf F t d → d.kind ≠ .thm → Judged F ax t Ok (.«open», [], some (.notTheorem t))
  |
  outside {d : Decl} :
    DeclOf F t d →
      d.kind = .thm →
      d.module.getRoot ≠ `FvdepProofs → Judged F ax t Ok (.«open», [], some (.outside t))
  |
  other {d : Decl} :
    DeclOf F t d →
      d.kind = .thm →
      d.module.getRoot = `FvdepProofs →
      ¬Ok d.type → Judged F ax t Ok (.«open», [], some (.otherStatement t))
  |
  counted {d : Decl} {raw : List Name} {a : List String} {s : Status} :
    DeclOf F t d →
      d.kind = .thm →
      d.module.getRoot = `FvdepProofs →
      Ok d.type → AxiomsOf ax t raw → Extra raw a → StatusOf a s → Judged F ax t Ok (s, a, none)

/-- C5's proof registry of `e`: none declared; declared, outside C2's forms; its proofs. -/
inductive RegistryOf (F : Facts) (e : Entry) : Except Why Proofs → Prop
  | absent : (∀ d ∈ F.decls, d.name ≠ proofsName e.module) → RegistryOf F e (.error .noRegistry)
  |
  unreadable :
    (∃ d ∈ F.decls, d.name = proofsName e.module) →
      (∀ p, ¬ProofsAt F (proofsName e.module) p) → RegistryOf F e (.error .unreadable)
  |
  read {p : Proofs} :
    (∃ d ∈ F.decls, d.name = proofsName e.module) →
      ProofsAt F (proofsName e.module) p → RegistryOf F e (.ok p)

/-- C5: obligation `o`'s statement = the constant `o` (alpha-equivalence). -/
def ObligationOk (o : Name) (ty : Expr) : Prop := erase ty = .const o []

/-- C5: an obligation's outcome under its entry's registry. -/
inductive ObligationJudged (F : Facts) (ax : List (Name × List Name)) (o : Name) :
    Except Why Proofs → Status × List String × Option Why → Prop
  | registry {w : Why} : ObligationJudged F ax o (.error w) (.«open», [], some w)
  |
  unmapped {p : Proofs} :
    (∀ x ∈ p.obligations, x.1 ≠ o) → ObligationJudged F ax o (.ok p) (.«open», [], some .unmapped)
  |
  twice {p : Proofs} :
    2 ≤ p.obligations.countP (·.1 == o) →
      ObligationJudged F ax o (.ok p) (.«open», [], some .mappedTwice)
  |
  one {p : Proofs} {t : Name} {r : Status × List String × Option Why} :
    p.obligations.countP (·.1 == o) = 1 →
      (o, t) ∈ p.obligations → Judged F ax t (ObligationOk o) r → ObligationJudged F ax o (.ok p) r

/-- C5: the compat statement `@Eq.{u} T new old`, `u` = the theorem's own level. -/
def CompatOk (T : Expr) (new old : Name) (ty : Expr) : Prop :=
  ∃ u, erase ty = erase (.app (.app (.app (.const ``Eq [u]) T) (.const new [])) (.const old []))

/-- C5: the compat edge's outcome under its entry's registry. -/
inductive CompatJudged (F : Facts) (ax : List (Name × List Name)) (T : Expr) (new old : Name) :
    Except Why Proofs → Status × List String × Option Why → Prop
  | registry {w : Why} : CompatJudged F ax T new old (.error w) (.«open», [], some w)
  |
  unmapped {p : Proofs} :
    p.compat = none → CompatJudged F ax T new old (.ok p) (.«open», [], some .unmapped)
  |
  one {p : Proofs} {t : Name} {r : Status × List String × Option Why} :
    p.compat = some t → Judged F ax t (CompatOk T new old) r → CompatJudged F ax T new old (.ok p) r

/-- C5 + C9 for a validated entry `e`: its obligations' outcomes in entry order, its compat edge
(T = its spec's declared type, `old` = the compat version's listed spec), its warnings in C9's order
(obligations, compat, a mapped compat theorem with no compat declared). -/
def EntrySpec (F : Facts) (ax : List (Name × List Name)) (l : Lists) (e : Entry) (s : EntryStatus) :
    Prop :=
  ∃ pr,
    RegistryOf F e pr ∧
      ∃ rs : List (Status × List String × Option Why),
        e.obligations.length = rs.length ∧
          (∀ x ∈ e.obligations.zip rs, ObligationJudged F ax x.1 pr x.2) ∧
          s.obligations = (e.obligations.zip rs).map (fun x => (x.1, x.2.1, x.2.2.1)) ∧
          ∃ edge : Option (String × Status × List String × Option Why),
            (e.compat = none ∧ edge = none ∨
                ∃ c d old r,
                  e.compat = some c ∧
                    libDecl? F e.spec = some d ∧
                    listedAt? l e.id c = some old ∧
                    CompatJudged F ax d.type e.spec old.spec pr r ∧ edge = some (c, r)) ∧
              s.compat = edge.map (fun x => (x.1, x.2.1, x.2.2.1)) ∧
              ∃ ignored : List Warning,
                (e.compat = none ∧
                      (∃ p t,
                        pr = .ok p ∧
                          p.compat = some t ∧ ignored = [.ignored (subject e.id e.version) t]) ∨
                    ¬(e.compat = none ∧ ∃ p t, pr = .ok p ∧ p.compat = some t) ∧ ignored = []) ∧
                  s.warnings =
                    (e.obligations.zip rs).filterMap
                        (fun x => x.2.2.2.map (Warning.obligation (subject e.id e.version) x.1)) ++
                      (edge.bind fun x =>
                          x.2.2.2.map (Warning.compat (subject e.id e.version))).toList ++
                      ignored

/-- C5 + C9: the entries' statuses in `modules` order. -/
def StatusesSpec (F : Facts) (ax : List (Name × List Name)) (l : Lists)
    (rs : List (Entry × EntryStatus)) : Prop :=
  l.entries.length = rs.length ∧ ∀ x ∈ l.entries.zip rs, x.2.1 = x.1 ∧ EntrySpec F ax l x.1 x.2.2

/-! ## C4: the entry digest's framed input -/

/-- A module name as Lean derives it from a source path: non-empty, string components without
`/`. -/
def PlainModule : Name → Prop
  | .str p s => (p = .anonymous ∨ PlainModule p) ∧ '/' ∉ s.toList
  | _ => False

end FvdepAudit.Index.Statuses.Spec
