import Lean

/-! Q2's freeze digest (contract `docs/contracts/U6-profile.md` Q2; gate stage `coverage`, through
`fvdep-ledger --check … --freeze <record>`): one hash over the profile's normative content — the
deep roots (every constant of the profile's spec modules + its table + types modules, the
converter's cap logic, I1's presence read, the recipes + their options, `profileId`) hashed by
type + value, each constant they reach in a profile module (`FvdepCore.Profile*`,
`FvdepAudit.Profile*`, `FvdepIO.Parse`) likewise, every other reached constant by name alone
(toolchain + shared codecs: their own claims + the toolchain commit cover them); a recursive
`partial def` = an opaque constant ⇒ its `_unsafe_rec` companion's value is hashed too; + the
claim statements' own terms (shallow: a claim names the implementation it constrains, whose
refactors leave the profile unchanged) + the toolchain's commit. `Expr.hash` ignores binder
names + docstrings: an alpha-renaming or a comment edit keeps the digest. A change without a new
version id → `ledger: profile: freeze: …`. -/

open Lean

namespace FvdepLedger.Freeze

/-- Modules whose constants are the profile's own: hashed by body when reached. -/
def profileModule (m : Name) : Bool :=
  [`FvdepCore.Profile, `FvdepAudit.Profile, `FvdepIO.Parse].any fun p => p.isPrefixOf m

/-- Modules every constant of which is a deep root. -/
def rootModules : List Name :=
  [`FvdepAudit.Profile.Walk.Spec, `FvdepAudit.Profile.Stage.Spec, `FvdepAudit.Profile.Barrier.Spec,
    `FvdepAudit.Profile.Spec, `FvdepCore.Profile.Table, `FvdepCore.Profile.Types]

/-- Named deep roots: the converter's cap logic + tie order, I1's presence read + its path rule,
the recipes + their options, the id. -/
def rootNames : List Name :=
  [`FvdepIO.Parse.loop, `FvdepIO.Parse.capAt, `FvdepIO.Parse.convert, `FvdepIO.Parse.optionsOf,
    `FvdepIO.Parse.presence, `FvdepIO.Parse.oleanAt, `FvdepCore.Build.consumer,
    `FvdepCore.Build.library, `FvdepCore.Build.libraryOptions, `FvdepCore.Profile.Role.recipe,
    `FvdepCore.Profile.profileId]

/-- The claim statements: shallow roots. -/
def claimNamespace : Name := `FvdepLedger.Rows.ProfileClaims

def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

/-- A constant's hashed terms: its type, its value (an opaque's + its `_unsafe_rec` companion's). -/
def terms (env : Environment) (n : Name) : List Expr :=
  match env.find? n with
  | some (.defnInfo d) => [d.type, d.value]
  | some (.opaqueInfo o) =>
    match env.find? (n ++ `_unsafe_rec) with
    | some (.defnInfo d) => [o.type, o.value, d.type, d.value]
    | _ => [o.type, o.value]
  | some (.thmInfo t) => [t.type]
  | some ci => [ci.type]
  | none => []

/-- The digest over `deep` (closure inside profile modules) + `shallow` (own terms alone); a
closure past `bound` steps fails closed (a digest over part of it would vouch for less). -/
def digest (env : Environment) (deep shallow : List Name) (bound : Nat := 1000000) :
    Except String UInt64 :=
  Id.run do
    let mut seen : NameSet := {}
    let mut todo := deep
    let mut lines : Array (Name × UInt64) := #[]
    let mut steps := 0
    while !todo.isEmpty && steps < bound do
      steps := steps + 1
      match todo with
      | [] =>
        pure ()
      | n :: rest =>
        todo := rest
        unless seen.contains n do
          seen := seen.insert n
          let bodied := deep.contains n || (moduleOf env n).any profileModule
          if bodied then
            let ts := terms env n
            lines := lines.push (n, ts.foldl (fun h e => mixHash h e.hash) 7)
            for e in ts do
              for c in e.getUsedConstants do
                unless seen.contains c do
                  todo := c :: todo
            if (env.find? (n ++ `_unsafe_rec)).isSome then
              todo := (n ++ `_unsafe_rec) :: todo
          else
            lines := lines.push (n, 0)
    if !todo.isEmpty then
      return .error s!"the profile's closure passes {bound} steps"
    for n in shallow do
      lines := lines.push (`shallow ++ n, (terms env n).foldl (fun h e => mixHash h e.hash) 11)
    let sorted := lines.qsort fun a b => a.1.toString < b.1.toString
    return .ok (sorted.foldl (fun h x => mixHash (mixHash h (hash x.1)) x.2) (hash Lean.githash))

/-- The profile's id (`profileId`'s string literal) + its digest, or why they cannot be read. -/
def current (env : Environment) : Except String (String × String) := do
  let some (.defnInfo d) := env.find? `FvdepCore.Profile.profileId
    | throw "FvdepCore.Profile.profileId not found"
  let .lit (.strVal id) := d.value.consumeMData
    | throw "FvdepCore.Profile.profileId is not a string literal"
  let consts :=
    env.constants.fold (init := #[]) fun acc n _ =>
      if (moduleOf env n).any (rootModules.contains ·) then acc.push n else acc
  let deep := consts.toList ++ rootNames
  for n in deep do
    unless env.contains n do
      throw s!"root {n} not found"
  let shallow :=
    (env.constants.fold (init := #[]) fun acc n _ =>
        if claimNamespace.isPrefixOf n && !n.isInternal then acc.push n else acc).toList
  let h ← digest env deep shallow
  let hex := String.ofList ((Nat.toDigits 16 h.toNat).leftpad 16 '0')
  return (id, hex)

end FvdepLedger.Freeze
