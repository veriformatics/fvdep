#!/usr/bin/env python3
"""Regenerate independent U2 L1–L9 fixtures; checker implementation is not an input."""

from dataclasses import dataclass, field
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MODULES = ROOT / "tool" / "FvdepLedgerFixtures"
TESTS = ROOT / "tests" / "ledger"
PREFIX = "FvdepLedgerFixtures"
RULING = "Fixture interpreter mapping is trusted."
LITERAL_RULING = "Fixture literal data is structurally checked."


@dataclass
class Row:
    subject: str = "plan"
    claims: list[tuple[str, str]] = field(default_factory=lambda: [("statement", "proof")])
    path: list[str] = field(default_factory=lambda: ["main", "plan"])
    no_caller: str = ""
    residue: list[str] = field(default_factory=list)
    unproven: list[str] = field(default_factory=list)
    component: str = ""


@dataclass
class Fixture:
    name: str
    plan: str = "def plan (args : List String) : Nat := args.length"
    extra: str = ""
    imports: list[str] = field(default_factory=list)
    main: str = "def main (args : List String) : Nat := interpret (plan args)"
    interpreter: str = "def interpret (value : Nat) : Nat := value"
    statement: str = "def statement : Prop := ∀ args : List String, plan args = args.length"
    proof: str = (
        "theorem proof : ∀ args : List String, plan args = args.length := by\n"
        "  intro args\n  rfl"
    )
    rows: list[Row] = field(default_factory=lambda: [Row()])
    interpreter_row: bool = True
    ruling: str = RULING
    boundary: list[str] = field(default_factory=list)
    extra_residue: str = ""
    libs: list[str] = field(default_factory=list)
    extra_ledger: str = ""


def name_term(name: str, fixture: Fixture) -> str:
    # Single-backtick literals intentionally admit missing names: checker, not elaborator, decides.
    full = name if "." in name else f"{PREFIX}.{fixture.name}.{name}"
    return f"`{full}"


def strings(values: list[str]) -> str:
    return "[" + ", ".join(f'"{value}"' for value in values) + "]"


def names(values: list[str], fixture: Fixture) -> str:
    return "[" + ", ".join(name_term(value, fixture) for value in values) + "]"


def row_term(row: Row, fixture: Fixture) -> str:
    component = row.component or f"{PREFIX}.{fixture.name}"
    claims = ", ".join(
        f"({name_term(statement, fixture)}, {name_term(theorem, fixture)})"
        for statement, theorem in row.claims
    )
    return (
        f"  {{ component := `{component}\n"
        '    contract := "docs/contracts/U2-core.md L1–L9"\n'
        '    claim := "The named statement holds for the executed subject."\n'
        f"    claims := [{claims}]\n"
        f"    subject := {name_term(row.subject, fixture)}\n"
        f"    path := {names(row.path, fixture)}\n"
        f'    noCaller := "{row.no_caller}"\n'
        f"    residue := {strings(row.residue)}\n"
        f"    unproven := {strings(row.unproven)} }}"
    )


def render(fixture: Fixture) -> str:
    imports = "\n".join(["import FvdepLedger.Types", *fixture.imports])
    all_rows = list(fixture.rows)
    if fixture.interpreter_row:
        all_rows.append(
            Row(
                subject="interpret",
                claims=[],
                path=["main", "interpret"],
                unproven=["runtime"],
            )
        )
    rows = ",\n".join(row_term(row, fixture) for row in all_rows)
    libraries = fixture.libs or [f"{PREFIX}.{fixture.name}"]
    return (
        f"{imports}\n\n"
        f"/-! Contract-only fixture: {fixture.name}. Each checker invocation loads this module alone. -/\n\n"
        f"namespace {PREFIX}.{fixture.name}\n\n"
        f"{fixture.extra}\n\n"
        f"{fixture.plan}\n\n"
        f"{fixture.interpreter}\n\n"
        f"{fixture.main}\n\n"
        f"{fixture.statement}\n\n"
        f"{fixture.proof}\n\n"
        "def ledger : FvdepLedger.Ledger :=\n"
        f"{{ main := {name_term('main', fixture)}\n"
        f"  interpreter := {name_term('interpret', fixture)}\n"
        f"  plan := {name_term('plan', fixture)}\n"
        f"  libs := {names(libraries, fixture)}\n"
        f"  rows := [\n{rows}]\n"
        "  residue := [\n"
        '  { id := "runtime"\n'
        '    what := "Fixture interpreter and optional primitive boundary."\n'
        '    reason := "The effect-to-primitive mapping is tested residue."\n'
        f'    ruling := "{fixture.ruling}"\n'
        f"    boundary := {names(fixture.boundary, fixture)} }}{fixture.extra_residue}] }}\n\n"
        f"{fixture.extra_ledger}\n\n"
        f"end {PREFIX}.{fixture.name}\n"
    )


def fixtures() -> list[Fixture]:
    base = [Fixture("Clean")]
    base.append(
        Fixture(
            "Bypass",
            extra=(
                "def subject (args : List String) : Nat := args.length\n\n"
                "def other (args : List String) : Nat := args.length + 1\n\n"
                "def subjectStatement : Prop := ∀ args : List String, subject args = args.length\n\n"
                "theorem subjectProof : ∀ args : List String, subject args = args.length := by\n"
                "  intro args\n  rfl"
            ),
            plan="def plan (args : List String) : Nat := other args",
            statement="def statement : Prop := ∀ args : List String, plan args = other args",
            proof="theorem proof : ∀ args : List String, plan args = other args := by\n  intro args\n  rfl",
            rows=[
                Row(),
                Row(
                    subject="subject",
                    claims=[("subjectStatement", "subjectProof")],
                    path=["main", "plan", "subject"],
                ),
            ],
        )
    )
    base.append(
        Fixture(
            "UnusedReference",
            extra="def subject (args : List String) : Nat := args.length",
            plan="def plan (args : List String) : Nat :=\n  let _ := subject args\n  0",
            statement="def statement : Prop := ∀ args : List String, plan args = subject args",
            proof="theorem proof : ∀ args : List String, plan args = 0 := by\n  intro args\n  rfl",
            rows=[Row(), Row(subject="subject", path=["main", "plan", "subject"])],
        )
    )
    base.extend(
        [
            Fixture(
                "WrongTheoremType",
                proof="theorem proof : ∀ args : List String, plan args = plan args := by\n  intro args\n  rfl",
            ),
            Fixture(
                "Sorry",
                proof="theorem proof : ∀ args : List String, plan args = args.length := by\n  sorry",
            ),
            Fixture(
                "ForeignAxiom",
                extra="axiom oracle : ∀ args : List String, args.length = args.length",
                proof=(
                    "theorem proof : ∀ args : List String, plan args = args.length := by\n"
                    "  intro args\n  exact oracle args"
                ),
            ),
            Fixture(
                "Forged",
                imports=[f"import {PREFIX}.ForgedImport"],
                proof=(
                    "theorem proof : ∀ args : List String, plan args = args.length :=\n"
                    f"  False.elim {PREFIX}.ForgedImport.falseProof"
                ),
            ),
            Fixture("UncoveredDefinition", interpreter_row=False),
            Fixture(
                "MissingReachableModule",
                imports=[f"import {PREFIX}.MissingModuleImport"],
                plan=(
                    "def plan (args : List String) : Nat :=\n"
                    f"  {PREFIX}.MissingModuleImport.step args.length"
                ),
            ),
            Fixture("EmptyWaiver", rows=[Row(claims=[])]),
            Fixture("UnknownResidue", rows=[Row(residue=["absent"])]),
            Fixture("MissingRuling", ruling="This ruling does not occur in the spec fixture."),
            Fixture("StaleNoCaller", rows=[Row(path=[], no_caller="U8")]),
        ]
    )
    base.append(
        Fixture(
            "Detached",
            extra=(
                "def parked (args : List String) : Nat := args.length\n\n"
                "def parkedStatement : Prop := ∀ args : List String, parked args = args.length\n\n"
                "theorem parkedProof : ∀ args : List String, parked args = args.length := by\n"
                "  intro args\n  rfl"
            ),
            rows=[
                Row(),
                Row(
                    subject="parked",
                    claims=[("parkedStatement", "parkedProof")],
                    path=[],
                    no_caller="U8",
                ),
            ],
        )
    )
    base.extend(
        [
            Fixture(
                "ImplementedBy",
                extra="def replacement (args : List String) : Nat := args.length + 1",
                plan="@[implemented_by replacement]\ndef plan (args : List String) : Nat := args.length",
            ),
            Fixture(
                "Extern",
                plan='@[extern "fvdep_ledger_fixture_plan"]\ndef plan (args : List String) : Nat := args.length',
            ),
            Fixture(
                "Partial",
                plan=(
                    "partial def plan (args : List String) : Nat :=\n"
                    "  if args.isEmpty then 0 else plan args.tail"
                ),
                statement="def statement : Prop := ∀ args : List String, plan args = plan args",
                proof="theorem proof : ∀ args : List String, plan args = plan args := by\n  intro args\n  rfl",
            ),
            Fixture("BrokenRoot", main="def main (args : List String) : Nat := interpret (plan args + 1)"),
            Fixture("NotAboutSubject", statement="def statement : Prop := True", proof="theorem proof : True := True.intro"),
            Fixture("PathStart", rows=[Row(path=["plan"])]),
            Fixture("PathEnd", rows=[Row(path=["main", "interpret"])]),
            Fixture("WrongComponent", rows=[Row(component="FvdepLedger.Types")]),
            Fixture(
                "NotTheorem",
                proof="def proof : ∀ args : List String, plan args = args.length := by\n  intro args\n  rfl",
            ),
        ]
    )
    for name, step in [
        ("ExternBoundary", '@[extern "fvdep_ledger_fixture_step"]\ndef step (n : Nat) : Nat := n'),
        ("OpaqueBoundary", "opaque step (n : Nat) : Nat := n"),
        ("ImplementedBoundary", "def replacement (n : Nat) : Nat := n + 1\n\n@[implemented_by replacement]\ndef step (n : Nat) : Nat := n"),
    ]:
        base.append(
            Fixture(
                name,
                extra=step,
                plan="def plan (args : List String) : Nat := step args.length",
                statement="def statement : Prop := ∀ args : List String, plan args = step args.length",
                proof="theorem proof : ∀ args : List String, plan args = step args.length := by\n  intro args\n  rfl",
                boundary=["step"],
                rows=[Row(residue=["runtime"])],
            )
        )
    base.extend(
        [
            Fixture("Nonliteral", extra_ledger="opaque hiddenLedger : FvdepLedger.Ledger := ledger"),
            Fixture(
                "MissingUnusedLibrary",
                imports=[f"import {PREFIX}.UnusedLib.Child"],
                libs=[f"{PREFIX}.MissingUnusedLibrary", f"{PREFIX}.UnusedLib"],
            ),
            Fixture("UnknownUnproven", rows=[Row(claims=[], unproven=["absent"])]),
            Fixture("StatementNotProp", statement="def statement : Nat := 7"),
            Fixture("StatementNotDefinition", statement="theorem statement : True := True.intro"),
            Fixture("MissingStatement", rows=[Row(claims=[("absentStatement", "proof")])]),
            Fixture("MissingTheorem", rows=[Row(claims=[("statement", "absentTheorem")])]),
            Fixture("MissingSubject", rows=[Row(subject="absentSubject")]),
            Fixture("EmptyNoCaller", rows=[Row(path=[])]),
            Fixture("RuledWaiver", rows=[Row(claims=[], unproven=["runtime"])]),
            Fixture(
                "AlphaEquivalent",
                proof="theorem proof : ∀ input : List String, plan input = input.length := by\n  intro input\n  rfl",
            ),
            Fixture(
                "DefeqNotAlpha",
                proof="theorem proof : ∀ args : List String, args.length = args.length := by\n  intro args\n  rfl",
            ),
            Fixture(
                "Opaque",
                plan="opaque plan (args : List String) : Nat := args.length",
                statement="def statement : Prop := ∀ args : List String, plan args = plan args",
                proof="theorem proof : ∀ args : List String, plan args = plan args := by\n  intro args\n  rfl",
            ),
        ]
    )
    for name, path, claim in [
        ("MainEdge", ["main", "subject"], "edgeStatement"),
        ("UnprovedEdge", ["main", "plan", "subject"], "subjectStatement"),
    ]:
        base.append(
            Fixture(
                name,
                extra=(
                    "def subject (args : List String) : Nat := args.length\n\n"
                    "def subjectStatement : Prop := ∀ args : List String, subject args = args.length\n\n"
                    "theorem subjectProof : ∀ args : List String, subject args = args.length := by\n"
                    "  intro args\n  rfl"
                ),
                plan="def plan (args : List String) : Nat := subject args",
                statement="def statement : Prop := ∀ args : List String, plan args = subject args",
                proof="theorem proof : ∀ args : List String, plan args = subject args := by\n  intro args\n  rfl",
                rows=[Row(), Row(subject="subject", claims=[("statement" if claim == "edgeStatement" else claim, "proof" if claim == "edgeStatement" else "subjectProof")], path=path)],
            )
        )
    for name, boundary, cited in [
        ("UncitedBoundary", ["step"], []),
        ("AncestorBoundary", ["plan"], ["runtime"]),
    ]:
        base.append(
            Fixture(
                name,
                extra="opaque step (n : Nat) : Nat := n",
                plan="def plan (args : List String) : Nat := step args.length",
                statement="def statement : Prop := ∀ args : List String, plan args = step args.length",
                proof="theorem proof : ∀ args : List String, plan args = step args.length := by\n  intro args\n  rfl",
                rows=[Row(residue=cited)],
                boundary=boundary,
            )
        )
    base.extend(
        [
            Fixture(
                "StdChoice",
                proof=(
                    "theorem proof : ∀ args : List String, plan args = args.length := by\n"
                    "  intro args\n  exact Classical.choice ⟨Eq.refl (plan args)⟩"
                ),
            ),
            Fixture(
                "UniverseMismatch",
                statement=(
                    "def statement.{u} : Prop :=\n"
                    "  ∀ (α : Type u) (x : α), x = x ∧ plan [] = 0"
                ),
                proof=(
                    "theorem proof : ∀ (α : Type) (x : α), x = x ∧ plan [] = 0 := by\n"
                    "  intro α x\n  exact ⟨rfl, rfl⟩"
                ),
            ),
            Fixture(
                "NestedExtern",
                extra='@[extern "fvdep_ledger_fixture_step"]\ndef step (n : Nat) : Nat := n',
                plan="def plan (args : List String) : Nat := step args.length",
            ),
            Fixture(
                "NestedImplementedBy",
                extra=(
                    "def replacement (n : Nat) : Nat := n + 1\n\n"
                    "@[implemented_by replacement]\ndef step (n : Nat) : Nat := n"
                ),
                plan="def plan (args : List String) : Nat := step args.length",
            ),
            Fixture(
                "ForgedUnusedImport",
                imports=[f"import {PREFIX}.ForgedImport"],
            ),
            Fixture(
                "InterpreterExempt",
                interpreter='@[extern "fvdep_ledger_fixture_interpret"]\ndef interpret (value : Nat) : Nat := value',
            ),
            Fixture(
                "TransitiveEdge",
                extra=(
                    "def subject (args : List String) : Nat := args.length\n\n"
                    "def via (args : List String) : Nat := subject args"
                ),
                plan="def plan (args : List String) : Nat := via args",
                statement="def statement : Prop := ∀ args : List String, plan args = subject args",
                proof="theorem proof : ∀ args : List String, plan args = subject args := by\n  intro args\n  rfl",
                rows=[Row(), Row(subject="subject", path=["main", "plan", "subject"])],
            ),
            Fixture(
                "PathClosureExtern",
                extra=(
                    "def subject (args : List String) : Nat := args.length\n\n"
                    '@[extern "fvdep_ledger_fixture_bridge"]\n'
                    "def bridge (args : List String) : Nat := subject args"
                ),
                plan="def plan (args : List String) : Nat := bridge args",
                statement="def statement : Prop := ∀ args : List String, plan args = subject args",
                proof="theorem proof : ∀ args : List String, plan args = subject args := by\n  intro args\n  rfl",
                rows=[Row(claims=[], unproven=["runtime"]), Row(subject="subject", path=["main", "plan", "subject"])],
            ),
            Fixture(
                "MetadataOwned",
                imports=[f"import {PREFIX}.MetadataImport"],
                plan="def plan (args : List String) : Nat := LooksForeign.step args.length",
            ),
            Fixture(
                "MetadataSubject",
                extra="def _root_.LooksForeign.subject (args : List String) : Nat := args.length",
                plan="def plan (args : List String) : Nat := LooksForeign.subject args",
                statement="def statement : Prop := ∀ args : List String, plan args = LooksForeign.subject args",
                proof="theorem proof : ∀ args : List String, plan args = LooksForeign.subject args := by\n  intro args\n  rfl",
                rows=[Row(), Row(subject="LooksForeign.subject", path=["main", "plan", "LooksForeign.subject"])],
            ),
            Fixture(
                "Unsafe",
                plan="unsafe def plan (args : List String) : Nat := args.length",
                main="unsafe def main (args : List String) : Nat := interpret (plan args)",
                imports=["import Lean"],
                statement=(
                    "open Lean Elab Term Meta in\n"
                    "set_option debug.skipKernelTC true in\n"
                    "run_elab do\n"
                    "  let listTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``String)\n"
                    "  withLocalDeclD `args listTy fun args => do\n"
                    f"    let call := mkApp (mkConst `{PREFIX}.Unsafe.plan) args\n"
                    "    let prop ← mkForallFVars #[args] (← mkEq call call)\n"
                    "    let value ← mkLambdaFVars #[args] (← mkEqRefl call)\n"
                    "    addDecl (.defnDecl {\n"
                    f"      name := `{PREFIX}.Unsafe.statement\n"
                    "      levelParams := []\n"
                    "      type := mkSort Level.zero\n"
                    "      value := prop\n"
                    "      hints := .abbrev\n"
                    "      safety := .safe })\n"
                    "    addDecl (.thmDecl {\n"
                    f"      name := `{PREFIX}.Unsafe.proof\n"
                    "      levelParams := []\n"
                    "      type := prop\n"
                    "      value := value })"
                ),
                proof="",
            ),
        ]
    )
    base.extend(
        [
            Fixture(
                "NestedOpaque",
                extra=(
                    "opaque hidden (n : Nat) : Nat := n\n\n"
                    "def helper (args : List String) : Nat := hidden args.length"
                ),
                plan="def plan (args : List String) : Nat := helper args",
                statement="def statement : Prop := ∀ args : List String, plan args = helper args",
                proof="theorem proof : ∀ args : List String, plan args = helper args := by\n  intro args\n  rfl",
            ),
            Fixture(
                "NestedPartial",
                extra=(
                    "partial def hidden (n : Nat) : Nat :=\n"
                    "  if n == 0 then 0 else hidden (n - 1)\n\n"
                    "def helper (args : List String) : Nat := hidden args.length"
                ),
                plan="def plan (args : List String) : Nat := helper args",
                statement="def statement : Prop := ∀ args : List String, plan args = helper args",
                proof="theorem proof : ∀ args : List String, plan args = helper args := by\n  intro args\n  rfl",
            ),
            Fixture(
                "NestedUnsafe",
                imports=["import Lean"],
                extra=(
                    "unsafe def hidden (n : Nat) : Nat := n\n\n"
                    "open Lean Elab Term Meta in\n"
                    "set_option debug.skipKernelTC true in\n"
                    "run_elab do\n"
                    "  let listTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``String)\n"
                    "  let fnTy ← mkArrow listTy (mkConst ``Nat)\n"
                    "  withLocalDeclD `args listTy fun args => do\n"
                    "    let len := mkApp2 (mkConst ``List.length [Level.zero]) (mkConst ``String) args\n"
                    f"    let hidden := mkApp (mkConst `{PREFIX}.NestedUnsafe.hidden) len\n"
                    "    let helperValue ← mkLambdaFVars #[args] hidden\n"
                    "    addAndCompile (.defnDecl {\n"
                    f"      name := `{PREFIX}.NestedUnsafe.helper\n"
                    "      levelParams := []\n"
                    "      type := fnTy\n"
                    "      value := helperValue\n"
                    "      hints := .abbrev\n"
                    "      safety := .safe })\n"
                    f"    let helper := mkApp (mkConst `{PREFIX}.NestedUnsafe.helper) args\n"
                    "    let planValue ← mkLambdaFVars #[args] helper\n"
                    "    addAndCompile (.defnDecl {\n"
                    f"      name := `{PREFIX}.NestedUnsafe.plan\n"
                    "      levelParams := []\n"
                    "      type := fnTy\n"
                    "      value := planValue\n"
                    "      hints := .abbrev\n"
                    "      safety := .safe })"
                ),
                plan="",
                statement="def statement : Prop := ∀ args : List String, plan args = plan args",
                proof="theorem proof : ∀ args : List String, plan args = plan args := by\n  intro args\n  rfl",
            ),
            Fixture(
                "RootSubject",
                statement=(
                    "def statement : Prop := ∀ args : List String, plan args = args.length\n\n"
                    "def rootStatement : Prop := ∀ args : List String, main args = interpret (plan args)\n\n"
                    "theorem rootProof : ∀ args : List String, main args = interpret (plan args) := by\n"
                    "  intro args\n  rfl"
                ),
                rows=[Row(), Row(subject="main", claims=[("rootStatement", "rootProof")], path=["main"])],
            ),
            Fixture("RulingOutside"),
        ]
    )
    support_extra = (
        "def helper (args : List String) : Nat := args.length\n\n"
        "def helperStatement : Prop := ∀ args : List String, helper args = args.length\n\n"
        "theorem helperProof : ∀ args : List String, helper args = args.length := by\n"
        "  intro args\n  rfl"
    )
    support_row = Row(
        subject="helper",
        claims=[("helperStatement", "helperProof")],
        path=[],
        no_caller="support",
    )
    base.extend(
        [
            Fixture(
                "Support",
                extra=support_extra,
                plan="def plan (args : List String) : Nat := helper args",
                proof="theorem proof : ∀ args : List String, plan args = args.length := by\n  intro args\n  exact helperProof args",
                rows=[Row(), support_row],
            ),
            Fixture("SupportOrphan", extra=support_extra, rows=[Row(), support_row]),
            Fixture(
                "SupportUnusedProof",
                extra=support_extra,
                plan="def plan (args : List String) : Nat := helper args",
                rows=[Row(), support_row],
            ),
            Fixture(
                "SupportLiteral",
                extra="def literal : List String := []",
                plan="def plan (args : List String) : Nat := (literal ++ args).length",
                rows=[
                    Row(),
                    Row(subject="literal", claims=[], path=[], no_caller="support", unproven=["literal"]),
                ],
                extra_residue=(
                    ',\n  { id := "literal"\n'
                    '    what := "Fixture literal data."\n'
                    '    reason := "Literal data has a structural check, not a theorem."\n'
                    f'    ruling := "{LITERAL_RULING}"\n'
                    '    boundary := [] }'
                ),
            ),
            Fixture(
                "SupportBadPath",
                extra=support_extra,
                plan="def plan (args : List String) : Nat := helper args",
                proof="theorem proof : ∀ args : List String, plan args = args.length := by\n  intro args\n  exact helperProof args",
                rows=[Row(path=["plan"]), support_row],
            ),
        ]
    )
    deep_prop = "deepTail = deepTail"
    deep_proof = "Eq.refl deepTail"
    for _ in range(160):
        deep_prop = f"True ∧ ({deep_prop})"
        deep_proof = f"And.intro True.intro ({deep_proof})"
    proposition = f"∀ args : List String, plan args = args.length ∧ ({deep_prop})"
    base.append(
        Fixture(
            "DeepStatement",
            extra="set_option maxRecDepth 4096\n\ndef deepTail : Nat := 314159",
            statement=f"def statement : Prop := {proposition}",
            proof=f"theorem proof : {proposition} := by\n  intro args\n  exact And.intro rfl ({deep_proof})",
        )
    )
    return base


def main() -> None:
    MODULES.mkdir(parents=True, exist_ok=True)
    for fixture in fixtures():
        (MODULES / f"{fixture.name}.lean").write_text(render(fixture))
    (MODULES / "ForgedImport.lean").write_text(
        "import Lean\n\n"
        "/-! Invalid proof hidden in an owned import; axiom inspection alone cannot detect it. -/\n\n"
        "open Lean Elab Term Meta in\n"
        "set_option debug.skipKernelTC true in\n"
        "run_elab do\n"
        "  addDecl (.thmDecl {\n"
        f"    name := `{PREFIX}.ForgedImport.falseProof\n"
        "    levelParams := []\n"
        "    type := mkConst ``False\n"
        "    value := mkConst ``True.intro })\n"
    )
    (MODULES / "MissingModuleImport.lean").write_text(
        f"namespace {PREFIX}.MissingModuleImport\n\n"
        "def step (value : Nat) : Nat := value\n\n"
        f"end {PREFIX}.MissingModuleImport\n"
    )
    (MODULES / "DocHashOracle.lean").write_text(
        f"import {PREFIX}.Clean\n"
        "import Lean\n\n"
        "/-! Independent L7 oracle: the committed fixture statement, not checker code. -/\n\n"
        "open Lean Elab Term in\n"
        "run_elab do\n"
        f"  let info ← getConstInfo ``{PREFIX}.Clean.statement\n"
        "  match info with\n"
        "  | .defnInfo value =>\n"
        '    logInfo m!"ORACLE_HASH_DECIMAL={value.value.hash.toNat}"\n'
        '  | _ => throwError "The fixture statement must be a definition."\n'
    )
    (MODULES / "MetadataImport.lean").write_text(
        "namespace LooksForeign\n\n"
        "def step (value : Nat) : Nat := value\n\n"
        "end LooksForeign\n"
    )
    (MODULES / "UnusedLib.lean").write_text("/-! Shipped library root; child module is loaded but unused. -/\n")
    (MODULES / "UnusedLib").mkdir(exist_ok=True)
    (MODULES / "UnusedLib" / "Child.lean").write_text(
        f"namespace {PREFIX}.UnusedLib.Child\n\n"
        "def dormant (value : Nat) : Nat := value + 1\n\n"
        f"end {PREFIX}.UnusedLib.Child\n"
    )
    spec_dir = TESTS / "fixtures"
    spec_dir.mkdir(parents=True, exist_ok=True)
    for name, tasks in [
        ("open", "- [ ] U8 wire the parked function"),
        ("closed", "- [x] abc1234 U8 wire the parked function"),
        ("absent", "- [ ] U9 another unit"),
        ("prefix", "- [ ] U80 a different unit"),
    ]:
        (spec_dir / f"{name}.spec").write_text(
            f"## Decisions\n\n- {RULING}\n\n## Tasks\n\n{tasks}\n"
        )
    (spec_dir / "outside.spec").write_text(
        f"## Notes\n\n- {RULING}\n\n"
        "## Decisions\n\n- No fixture interpreter ruling is recorded here.\n\n"
        f"## Tasks\n\n- [ ] U8 wire the parked function\n- {RULING}\n"
    )
    (spec_dir / "support-data.spec").write_text(
        f"## Decisions\n\n- {RULING}\n- {LITERAL_RULING}\n\n"
        "## Tasks\n\n- [ ] U8 wire the parked function\n"
    )
    print(f"Generated {len(fixtures()) + 6} Lean modules and 6 spec files.")


if __name__ == "__main__":
    main()
