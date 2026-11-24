"""Header/ownership rules, stage order, cap edges, and accepted source batches."""
from __future__ import annotations

import os
import random

from tests.profile.harness import (
    INIT, LIBRARY_HEADERS, ROOT, SEED, SIMPLE, SPEC_MODULE, STD, Context, Grammars, Result,
    case, check, module_path, need, put, refusal, sources,
)
from tests.profile.syntax_cases import COMMAND, TERM, at, accepted, finding

SORRY = "kind " + TERM + "sorry"
EOF = "parse unexpected end of input; expected ')', ',' or ':'"
TIME = (*INIT, "Std.Time")
DATE = 'def f (date : String → Nat) := date("2024-01-01")\n'
DATE_SPACE = DATE.replace('date("', 'date ("')
SOURCE_FILE_BYTES = 2**20
SOURCE_BATCH_BYTES = 2**24


def batch_case(id_: str, clause: str, raw: dict[str, str], want: str, grammar: Grammars,
               *, role: str = "consumer", library: Grammars | None = None) -> None:
    @case(id_, clause, f"{0 if want == 'accepted' else 1}; {want}")
    def run(c: Context) -> None:
        batch = sources(raw)
        lib = None
        if library is not None:
            lib = c.library(body="".join(f"import {m}\n" for m in library[SPEC_MODULE])
                            + "def Fvdep.Trial.sample : Nat := 1\n")
            put(lib, "FvdepPreview.lean", "def FvdepPreview.sample := 1\n")
            put(lib, "FvdepProofs/Registry.lean", "def FvdepProofs.Registry.sample := 1\n")
        check(c, batch, want, role=role, grammar=grammar, library=lib, headers=library)


for name, text, why in (
    ("module", "module\nimport Init\n", "header module"),
    ("prelude", "prelude\nimport Init.Core\n", "header prelude"),
    ("public", "public import Std\n", "parse cannot use `public import` without `module`"),
    ("module-before-modifier", "module\npublic import Std\n", "header module"),
):
    batch_case("header." + name, "R/I1", {"Impl": text}, refusal(1, 0, why), {})

for mod in ("Lean.Elab.Command", "Lake", "FvdepPreview", "FvdepProofs.Registry", "Init.Core",
            "FVdep.Trial", "Fvdep.Missing", "AnotherImpl"):
    batch_case("header.import." + mod, "R/I1/P5a", {"Impl": f"import {mod}\n{SIMPLE}"},
               refusal(1, 0, "header import " + mod), {}, library=LIBRARY_HEADERS)

for mod in ("Fvdep.Impl", "Lean.Impl", "Std.Impl", "Init.Impl", "Lake.Impl", "FvdepX.Impl", "Impl._x", "_Impl"):
    batch_case("header.name." + mod, "R/I2", {mod: SIMPLE}, refusal(1, 0, "header name " + mod, mod), {})

for mod in ("FvdepExtra.X", "FvdepProofs.X", "Fvdep._A", "Other"):
    batch_case("header.library-name." + mod, "I2", {mod: "def Fvdep.x := 1\n"},
               refusal(1, 0, "header name " + mod, mod), {}, role="library")

batch_case("header.library-to-preview", "R/I1", {
    "Fvdep.X": "import FvdepPreview\ndef Fvdep.x := 1\n", "FvdepPreview": "def FvdepPreview.x := 1\n",
}, refusal(1, 0, "header import FvdepPreview", "Fvdep.X"), {}, role="library")
batch_case("header.library-to-phase2", "I1", {"Fvdep.X": "import FvdepProofs\ndef Fvdep.x := 1\n"},
           refusal(1, 0, "header import FvdepProofs", "Fvdep.X"), {}, role="library")
batch_case("header.library-init-submodule", "I1", {"Fvdep.X": "import Init.Core\ndef Fvdep.x := 1\n"},
           refusal(1, 0, "header import Init.Core", "Fvdep.X"), {}, role="library")
batch_case("header.consumer-batch", "I1/P3", {"Z": "import A.B\ndef z := a\n", "A.B": SIMPLE}, "accepted",
           dict.fromkeys(("A.B", "Z"), INIT))
batch_case("header.consumer-library", "I1/P5a", {"Impl": "import Fvdep\ndef z := Fvdep.Trial.sample\n"},
           "accepted", {"Impl": INIT}, library=LIBRARY_HEADERS)
batch_case("header.library-preview", "I1/P3", {
    "FvdepPreview.B": "import FvdepPreview.A\ndef FvdepPreview.b := FvdepPreview.a\n",
    "FvdepPreview.A": "import Fvdep.A\ndef FvdepPreview.a := Fvdep.a\n",
    "Fvdep.A": "import Std.Time\ndef Fvdep.a := 1\n",
}, "accepted", dict.fromkeys(("Fvdep.A", "FvdepPreview.A", "FvdepPreview.B"), TIME), role="library")
batch_case("header.library-to-batch", "I1", {"Fvdep.A": "def Fvdep.a := 1\n",
           "Fvdep.B": "import Fvdep.A\ndef Fvdep.b := Fvdep.a\n"},
           "accepted", dict.fromkeys(("Fvdep.A", "Fvdep.B"), INIT), role="library")

for id_, text, line, col, why in (
    ("namespace", "namespace Fvdep\n", 1, 0, "ownership Fvdep"),
    ("def", "def Std.foo := 1\n", 1, 4, "ownership Std.foo"),
    ("any-fvdep-prefix", "namespace FvdepCustom.X\n", 1, 0, "ownership FvdepCustom.X"),
    ("decl-before-leaf", "def Lean._x := 1\n", 1, 4, "ownership Lean._x"),
    ("scope-before-ownership", "namespace Lean._x\n", 1, 0, "scope namespace Lean"),
):
    finding("ownership." + id_, "R/I2/C1", text, line, col, why)

batch_case("ownership.library-foreign", "R/I2", {"Fvdep.X": "def Foo.bar := 1\n"},
           refusal(1, 4, "ownership Foo.bar", "Fvdep.X"), {"Fvdep.X": INIT}, role="library")
batch_case("ownership.preview-foreign", "I2", {"FvdepPreview.X": "namespace Fvdep\n"},
           refusal(1, 0, "ownership Fvdep", "FvdepPreview.X"), {"FvdepPreview.X": INIT}, role="library")
accepted("ownership.nested-reserved-root", "I2/C1", "namespace Trial\ndef Fvdep.f := 1\nend Trial\n")

for id_, text, line, col, why in (
    ("ns-exact", "namespace List\n", 1, 0, "scope namespace List"),
    ("ns-prefix", "namespace List.Foo\n", 1, 0, "scope namespace List"),
    ("ns-lean-prefix", "namespace Lean.Order\n", 1, 0, "scope namespace Lean"),
    ("ns-nested", "namespace String\nnamespace Internal\n", 2, 0, "scope namespace String.Internal"),
    ("ns-root", "namespace _root_.Array\n", 1, 0, "scope namespace _root_.Array"),
    ("open-array", "open Array\n", 1, 5, "scope open Array"),
    ("open-suffix", "open Do\n", 1, 5, "scope open Do"),
    ("open-qualified", "open Std.Do\n", 1, 5, "scope open Std.Do"),
    ("open-root", "open _root_.Array\n", 1, 5, "scope open _root_.Array"),
    ("open-order", "open Nat Array List\n", 1, 9, "scope open Array"),
    ("section-keeps-ns", "namespace String\nsection First.Second\nnamespace Internal\n",
     3, 0, "scope namespace String.Internal"),
    ("pop-qualified-ns", "namespace Trial.Nested\nend Trial.Nested\nnamespace List\n", 3, 0, "scope namespace List"),
    ("pop-section-then-ns", "namespace Trial\nsection First.Second\nend First.Second\nend Trial\nnamespace List\n",
     5, 0, "scope namespace List"),
    ("mutual-keeps-ns", "namespace String\nmutual\n  inductive T where\n    | c : T\nend\nnamespace Internal\n",
     6, 0, "scope namespace String.Internal"),
):
    finding("scope." + id_, "R/P4/C1", text, line, col, why)

for id_, text in (
    ("dotted-declaration", "def List.foo := 1\n"),
    ("dotted-ns", "namespace A.List\nend A.List\n"),
    ("nested-ns", "namespace A\nnamespace List\nend List\nend A\n"),
    ("popped", "namespace String\nend String\nnamespace Internal\nend Internal\n"),
    ("open-nat", "open Nat\n"),
    ("open-only", "open Array (push)\n"),
):
    accepted("scope.accept." + id_, "R/P4/C1", text)

for id_, text, line, col, why in (
    ("compiler", "def x._unsafe_rec := 1\n", 1, 4, "_unsafe_rec"),
    ("compiler-in-ns", "namespace Foo\ndef _unsafe_rec := 1\n", 2, 4, "_unsafe_rec"),
    ("root", "def _root_.Fvdep.x := 1\n", 1, 4, "_root_"),
    ("hygiene", "def a := «_@»\n", 1, 9, "_@"),
    ("binder", "def f (_x : Nat) := 1\n", 1, 7, "_x"),
    ("field", "structure S where\n  _a : Nat\n", 2, 2, "_a"),
    ("cases-on", "def T.casesOn := 1\n", 1, 4, "casesOn"),
    ("inductive-ctor", "inductive T where\n  | rec\n", 2, 4, "rec"),
    ("extends-projection", "structure Parent where\n  a : Nat\nstructure Child extends rec : Parent\n", 3, 24, "rec"),
    ("main", "def main := 1\n", 1, 4, "main"),
    ("detail-cap-ascii", "def _" + "a" * 1999 + " := 1\n", 1, 4, "_" + "a" * 1020 + "..."),
    ("detail-cap-unicode", "def «_a" + "é" * 999 + "» := 1\n", 1, 4, "_a" + "é" * 509 + "..."),
    ("generated-field", "structure S where\n  proof_0 : Nat\n", 2, 2, "proof_0"),
    ("generated-explicit-field", "structure S where\n  (eq_1 : Nat)\n", 2, 3, "eq_1"),
    ("generated-implicit-field", "structure S where\n  {match_2 : Nat}\n", 2, 3, "match_2"),
    ("generated-instance-field", "structure S where\n  [recOn : Inhabited Nat]\n", 2, 3, "recOn"),
    ("generated-structure-ctor", "structure S where\n  noConfusion ::\n  a : Nat\n", 2, 2, "noConfusion"),
    ("generated-where-helper", "def f := h where\n  fun_cases := 1\n", 2, 2, "fun_cases"),
):
    finding("reserved." + id_, "R/I3/T", text, line, col, "reserved " + why)

for id_, text in (
    ("main-nested", "namespace Foo\ndef main := 1\nend Foo\n"),
    ("main-qualified", "def Foo.main := 1\n"),
    ("rec-use", "def a := @Nat.rec\n"),
    ("uses", "def a := T.casesOn\ndef b := S.mk\n"),
    ("quoted-dot", "def «x._name» := 1\n"),
    ("generated-use", "def f (rec : Nat) := rec\ndef x := T.proof_1\n"),
    ("not-numeric-suffix", "def Foo.eq_alt := 1\ndef Foo.match_a := 2\ndef Foo.proof_x := 3\n"),
    ("universe-parameter", "def Probe.{rec} := Type rec\n"),
    ("enclosing-generated-name", "namespace rec\ndef f := 1\nend rec\n"),
):
    accepted("reserved.accept." + id_, "R/I3", text)


SLOTS = (
    "def {c} := 1\n", "def Q.{c}.r := 1\n", "def f ({c} : Nat) := 1\n", "def f := {c}\n",
    "namespace Trial.{c}\n", "open Trial.{c}\n", "structure S where\n  {c} : Nat\n",
    "inductive T where\n  | {c}\n", "def f := ``Trial.{c}\n",
)


def underscored_sample(i: int) -> tuple[str, str, int, int]:
    rng = random.Random(SEED + i)
    plain = "_" + "".join(rng.choices("abcdefghijklmnopqrstuvwxyz0123456789_", k=rng.randrange(2, 20)))
    component = plain if i % 2 == 0 else plain + ".with.dot"
    token = component if i % 2 == 0 else "«" + component + "»"
    template = SLOTS[i // 2 % len(SLOTS)]
    start = template.index("{c}")
    # Dotted source stays one identifier occurrence at the start of its first component.
    before = template[:start]
    line = before.count("\n") + 1
    col = len(before.rsplit("\n", 1)[-1]) - (2 if "Q." in before else 6 if "Trial." in before else 0)
    return template.format(c=token), component, line, col


def generated_reserved(i: int) -> None:
    @case(f"reserved.generated.{i:02}", "I3a/C1 property",
          "1; any _-led parsed component refused at the identifier start")
    def run(c: Context) -> None:
        text, component, line, col = underscored_sample(i)
        check(c, sources({"Impl": text}), refusal(line, col, "reserved " + component), grammar={"Impl": INIT})


for sample in range(2 * len(SLOTS)):
    generated_reserved(sample)


finding("parse.eof", "R/P5", "def a := (1\n", 2, 0, EOF)
finding("parse.exit-mid", "R/P5", "def a := 1\n#exit\ndef b := 2\n", 2, 0, "kind " + COMMAND + "exit")
finding("parse.exit-last", "R/P5", "def a := 1\n#exit\n", 2, 0, "kind " + COMMAND + "exit")
finding("parse.body-import", "R/P5", "def a := 1\nimport Std\n", 2, 0, "kind " + COMMAND + "import")
finding("parse.crlf", "R/P5/C1", "def a := 1\r\ndef b := sorry\r\n", 2, 9, SORRY)
finding("parse.lf-twin", "R/P5/C1", "def a := 1\ndef b := sorry\n", 2, 9, SORRY)
finding("parse.unicode-column", "R/P5/C1", "def «é» := sorry\n", 1, 11, SORRY)
accepted("parse.crlf-accepted", "R/C1", "def a := 1\r\ndef b := a\r\n")
accepted("parse.lf-accepted", "R/C1", "def a := 1\ndef b := a\n")

batch_case("grammar.init", "R/P3", {"A": DATE}, refusal(1, 35, "parse unexpected token '('; expected command", "A"),
           {"A": INIT})
batch_case("grammar.time", "R/P3", {"B": "import Std.Time\n" + DATE}, refusal(2, 31, "kind Std.Time.termDate(_)", "B"),
           {"B": TIME})
batch_case("grammar.sibling", "R/P3/C1", {"B": "import Std.Time\n" + DATE, "A": DATE},
           refusal(1, 35, "parse unexpected token '('; expected command", "A"), {"A": INIT, "B": TIME})
batch_case("grammar.with-space", "R/P3", {"B": "import Std.Time\n" + DATE_SPACE}, "accepted", {"B": TIME})
batch_case("grammar.batch-transitive", "P3/I1", {"A": "import Z\n" + DATE, "Z": "import Std.Time\n"},
           refusal(2, 31, "kind Std.Time.termDate(_)", "A"), dict.fromkeys(("A", "Z"), TIME))
batch_case("grammar.library-transitive", "P3/I1/P5a", {"Impl": "import Fvdep\n" + DATE},
           refusal(2, 31, "kind Std.Time.termDate(_)"), {"Impl": TIME},
           library=LIBRARY_HEADERS | {SPEC_MODULE: ("Std.Time",)})
batch_case("grammar.ordered-explicit", "P3/I1", {"Impl": "import Std.Time\nimport Std.Data.HashMap\n" + SIMPLE},
           "accepted", {"Impl": (*TIME, "Std.Data.HashMap")})
batch_case("grammar.reverse-explicit", "P3/I1", {"Impl": "import Std.Data.HashMap\nimport Std.Time\n" + SIMPLE},
           "accepted", {"Impl": (*INIT, "Std.Data.HashMap", "Std.Time")})
batch_case("grammar.std", "P3/I1", {"Impl": "import Std\n" + SIMPLE}, "accepted", {"Impl": STD})

batch_case("order.header-before-body", "B1/C1/I1", {"A": "#eval 1\n", "Z": "import Lean\n"},
           refusal(1, 0, "header import Lean", "Z"), {})
batch_case("order.header-module", "C1/I1", {"Z": "prelude\n", "A": "import Lean\n"},
           refusal(1, 0, "header import Lean", "A"), {})
batch_case("order.body-module", "C1", {"Z": "#eval 1\n", "A": "def a := sorry\n"},
           refusal(1, 9, SORRY, "A"), dict.fromkeys(("A", "Z"), INIT))
finding("order.import", "C1/I1", "import Lean\nimport Lake\n", 1, 0, "header import Lean", ())
finding("order.command", "C1/P5", "#eval 1\ndef a := (1\n", 1, 0, "kind " + COMMAND + "eval")
finding("order.parse-before-walk", "C1/P5", "def a := (sorry\n", 2, 0, EOF)
finding("order.ancestor-first", "C1/K0/I3", "#eval _x\n", 1, 0, "kind " + COMMAND + "eval")
finding("order.siblings-left-first", "C1/K0/I3", "def a := (_x, sorry)\n", 1, 10, "reserved _x")
at("order.choice-contents", "C1/K1", "def p : Prop := ∃ (n : Nat), sorry\n", "sorry", SORRY)


def early_snapshot(r: Result, name: str) -> None:
    r.code(2)
    out = r.output
    need(len(out) == 1 and out[0].startswith("infra io: ") and name in out[0],
         f"expected isolated S1 refusal naming {name}: {out!r}")
    r.no_build(launches=0)


@case("usage.module-max", "D1/U3 T3", "0; 256-byte module name accepted")
def module_max(c: Context) -> None:
    name = "A" * 120 + "." + "B" * 135
    check(c, sources({name: SIMPLE}), grammar={name: INIT})


def usage_case(id_: str, options: list[str], modules: list[str]) -> None:
    @case("usage." + id_, "D1/U3 T3", "2; profile check usage on stderr, no launch")
    def run(c: Context) -> None:
        src = c.trial(sources({"Impl": SIMPLE}))
        r = c.call(["profile", "check", *options, str(src), *modules], observe=True)
        r.usage("profile check", "--role")


for name, options, modules in (
    ("empty", ["--role", "consumer"], []),
    ("repeat", ["--role", "consumer"], ["Impl", "Impl"]),
    ("bad-name", ["--role", "consumer"], ["A..B"]),
    ("bad-component", ["--role", "consumer"], ["A.1B"]),
    ("module-over", ["--role", "consumer"], ["A" * 120 + "." + "B" * 136]),
    ("role-other", ["--role", "other"], ["Impl"]),
    ("role-missing", [], ["Impl"]),
    ("library-option", ["--role", "library", "--library", "unused"], ["Fvdep.X"]),
    ("two-seams", ["--role", "consumer", "--results", "unused", "--child", "unused"], ["Impl"]),
    ("bad-limit", ["--role", "consumer", "--limit", "other=1"], ["Impl"]),
    ("bad-limit-number", ["--role", "consumer", "--limit", "depth=1e2"], ["Impl"]),
    ("bad-limit-pair", ["--role", "consumer", "--limit", "depth"], ["Impl"]),
    *((f"zero-{k}", ["--role", "consumer", "--limit", f"{k}=0"], ["Impl"])
      for k in ("depth", "nodes", "batchNodes", "seconds", "frameBytes", "fileBytes")),
):
    usage_case(name, options, modules)


def snapshot_case(kind: str) -> None:
    @case("snapshot." + kind, "D1/P6/U5 S1", "2; S1 refusal alone, no launch")
    def run(c: Context) -> None:
        src = c.trial({})
        module = "Dir.Impl" if kind in {"link-dir", "not-dir"} else "Impl"
        path = src / module_path(module)
        if kind == "link":
            path.symlink_to(put(c.directory, "copy.lean", SIMPLE))
        if kind == "link-dir":
            put(c.directory, "real-dir/Impl.lean", SIMPLE)
            path.parent.symlink_to(c.directory / "real-dir", target_is_directory=True)
        if kind == "not-dir":
            path.parent.write_text(SIMPLE)
        if kind == "is-dir":
            path.mkdir()
        if kind == "fifo":
            os.mkfifo(path)
        if kind == "file-over":
            path.write_bytes(b" " * (SOURCE_FILE_BYTES + 1))
        early_snapshot(c.profile(src, [module], observe=True), module_path(module))


for failure in ("missing", "link", "link-dir", "not-dir", "is-dir", "fifo", "file-over"):
    snapshot_case(failure)


@case("snapshot.batch-over", "D1/P6/U5 S1", "2; 16 MiB + 1 refused without launch")
def batch_over(c: Context) -> None:
    batch = {f"Module{i:02}": b" " * SOURCE_FILE_BYTES
             for i in range(SOURCE_BATCH_BYTES // SOURCE_FILE_BYTES)} | {"Z": b" "}
    early_snapshot(c.profile(c.trial(batch), list(batch), observe=True), "Z.lean")


@case("corpus.library", "R/Q1/I1/I3", "0; all phase-1 library modules accepted under library/1")
def corpus_library(c: Context) -> None:
    paths = [ROOT / "Fvdep.lean", ROOT / "FvdepPreview.lean", *sorted((ROOT / "Fvdep").rglob("*.lean"))]
    batch = {".".join(p.relative_to(ROOT).with_suffix("").parts): p.read_bytes() for p in paths}
    check(c, batch, role="library")


@case("corpus.launch", "R/Q1/I1/I3", "0; all three launch example modules accepted under consumer/1")
def corpus_launch(c: Context) -> None:
    batch = {f"Launch.{m}": (ROOT / f"examples/launch/Launch/{m}.lean").read_bytes()
             for m in ("Base64", "Base64Abi", "Semver")}
    check(c, batch, library=ROOT)


accepted("corpus.model", "Q1/K3/K4/K6", "namespace Fixture\nstructure Input where\n  raw : Nat\n"
         "def model (xs : Input) : Option Nat := if xs.raw = 0 then none else some xs.raw\nend Fixture\n")
accepted("corpus.termination", "Q1/K5", "def distance (a b : Nat) : Nat :=\n"
         "  if a < b then distance (a + 1) b + 1 else 0\ntermination_by b - a\ndecreasing_by omega\n")
