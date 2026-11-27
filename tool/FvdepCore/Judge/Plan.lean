import FvdepCore.Judge.Axioms
import FvdepCore.Judge.Profile

/-! U7 J (contract `docs/contracts/U7-judge.md` J1, J2, J4; X8): the judge's stages over one request
— one parse of e1 + e2 (X8), then S → G → A, the first failure or infrastructure stopping every
later stage; past A the kernel phase (IO: `FvdepIO.Judge.run`) runs all three kernels on e2; the
observations per U2 E2 (their key = the caller's: the request's challenge key) + J4's causes, one
per stage that recorded one. Pure. -/

namespace FvdepCore.Judge

open FvdepCore.Evidence FvdepCore.Export

/-- J3: phase 1's export roots in the comparator's order (Lean #15643: false rejects depend on the
primitives' order) — the quotient family, `Eq`, the implementation, the spec (+ the ABI shape), then
the allowlisted axioms + the primitives (G1's inventory past its quotient family). -/
def exportRoots1 (r : Request) : List Lean.Name :=
  mandatory.take 4 ++ [`Eq, r.impl, r.spec] ++ r.abi.toList ++ mandatory.drop 4

/-- J3: phase 2's export roots — the quotient family, the proof, the axioms + the primitives. -/
def exportRoots2 (r : Request) : List Lean.Name := mandatory.take 4 ++ [r.proof] ++ mandatory.drop 4

/-- J3 + U5 P4's split: the trusted roots (absent → infrastructure) = phase 1's roots but the
implementation; the consumer's (absent → the phase's `failed`) = the implementation, the proof. -/
def trustedRoots (r : Request) : List Lean.Name := (exportRoots1 r).filter (· != r.impl)

/-- J1: an export as read (its bytes, or why the read failed). -/
abbrev Read := Except String ByteArray

/-- J1: the stages before K — their observations, J4's causes, whether the kernel phase runs. -/
structure Pre where
  obs : List Obs
  details : List String
  kernels : Bool
  deriving DecidableEq

/-- F8: an exhausted stage's cause (J4). -/
def budgetCause : String := "the comparison passes its work budget"

/-- J1 + X8: e1 + e2 read once each (fvdep's own Lean `githash` + `version`), then S, G (W =
`p.work`, G5's list = `p.opaques`), A (an axiom outside `p.allowlist` = A's failure); a trusted-side
fault = infrastructure, the solution's = its stage's negative observation. -/
def stages (p : VProfile) (githash version : String) (r : Request) (d1 d2 : Digest) (e1 e2 : Read) :
    Pre :=
  match e1 with
  | .error why => ⟨[.infra .io s!"the trusted export could not be read: {why}"], [], false⟩
  | .ok b1 =>
    match readTables githash version b1 with
    | .error f =>
      ⟨[.infra .io s!"the trusted export is unreadable: line {f.line}: {f.reason}"], [], false⟩
    | .ok t1 =>
      match e2 with
      | .error why => ⟨[.infra .io s!"the solution export could not be read: {why}"], [], false⟩
      | .ok b2 =>
        match readTables githash version b2 with
        | .error f =>
          ⟨[.statement d1 d2 false],
            [s!"the solution export is unreadable: line {f.line}: {f.reason}"], false⟩
        | .ok t2 =>
          let w1 := viewOf t1
          let w2 := viewOf t2
          match statement w1 w2 r p.work {} with
          | (.infra c, _, _) => ⟨[.infra .io c], [], false⟩
          | (.mismatch c, _, _) => ⟨[.statement d1 d2 false], [c], false⟩
          | (.exhausted, _, _) => ⟨[.statement d1 d2 false], [budgetCause], false⟩
          | (.matched, fuel, memo) =>
            match graph w1 w2 r p.opaques fuel memo with
            | (.infra c, _, _, _) => ⟨[.statement d1 d2 true, .infra .io c], [], false⟩
            | (.mismatch c, _, _, _) => ⟨[.statement d1 d2 true, .graph d1 d2 false], [c], false⟩
            | (.exhausted, _, _, _) =>
              ⟨[.statement d1 d2 true, .graph d1 d2 false], [budgetCause], false⟩
            | (.matched, axs, _, _) =>
              let names := axs.map axiomText
              ⟨[.statement d1 d2 true, .graph d1 d2 true, .axioms d2 names],
                names.filter fun a => !p.allowlist.contains a, names.all p.allowlist.contains⟩

/-- J2: one kernel's observation on e2 (a per-kernel infrastructure = `infra`). -/
def kernelObs (d2 : Digest) (k : Kernel) : KResult → Obs
  | .status s => .kernel d2 k s
  | .infra c d => .infra c d

/-- J1 + J2: the stages' observations, then — the kernel phase reached — one per kernel in K's
order. -/
def judgeObs (pre : Pre) (d2 : Digest) (ks : List (Kernel × KResult)) : List Obs :=
  pre.obs ++ if pre.kernels then ks.map fun x => kernelObs d2 x.1 x.2 else []

end FvdepCore.Judge
