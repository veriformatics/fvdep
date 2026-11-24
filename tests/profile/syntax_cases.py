"""R's concrete findings and controls; K complements over the pinned parser grammar."""
from __future__ import annotations

import random

from tests.profile.harness import INIT, SEED, STD, Context, case, check, refusal, sources

COMMAND = "Lean.Parser.Command."
TERM = "Lean.Parser.Term."
TACTIC = "Lean.Parser.Tactic."
TERMINATION = "Lean.Parser.Termination."
REC = "def f (n : Nat) : Nat := f n\n"
STRUCT = "structure S where\n  a : Nat\n"


def finding(id_: str, clause: str, source: str, line: int, col: int, cause: str,
            grammar: tuple[str, ...] = INIT) -> None:
    want = refusal(line, col, cause)

    @case(id_, clause, f"1; {want}")
    def _finding(c: Context) -> None:
        check(c, sources({"Impl": source}), want, grammar={"Impl": grammar})


def at(id_: str, clause: str, source: str, token: str, cause: str,
       grammar: tuple[str, ...] = INIT) -> None:
    start = source.index(token)
    line = source.count("\n", 0, start) + 1
    col = start - (source.rfind("\n", 0, start) + 1)
    finding(id_, clause, source, line, col, cause, grammar)


def accepted(id_: str, clause: str, source: str, grammar: tuple[str, ...] = INIT) -> None:
    @case(id_, clause, "0; accepted")
    def _accepted(c: Context) -> None:
        check(c, sources({"Impl": source}), grammar={"Impl": grammar})


for name, source, kind, line in (
    ("eval", "def a := 1\n#eval a\n", COMMAND + "eval", 2),
    ("run-cmd", "run_cmd pure ()\n", "Lean.runCmd", 1),
    ("macro", 'macro "m" : term => `(1)\n', COMMAND + "macro", 1),
    ("syntax", 'syntax "trialSyntax" : term\n', COMMAND + "syntax", 1),
    ("notation", 'notation "trialNotation" => (1 : Nat)\n', COMMAND + "notation", 1),
    ("macro-rules", "macro_rules | `(foo) => `(1)\n", COMMAND + "macro_rules", 1),
    ("elab", 'elab "trialElab" : term => pure (.lit (.natVal 1))\n', COMMAND + "elab", 1),
    ("initialize", "initialize a : Nat ← pure 1\n", COMMAND + "initialize", 1),
    ("example", "example : Nat := 1\n", COMMAND + "example", 1),
    ("check", "#check Nat\n", COMMAND + "check", 1),
    ("deriving", "deriving instance Repr for Nat\n", COMMAND + "deriving", 1),
    ("option", "set_option debug.skipKernelTC true\n", COMMAND + "set_option", 1),
    ("option-in", "set_option autoImplicit true in\ndef so := 1\n", COMMAND + "in", 1),
    ("open-in", "open Nat in\ndef oi := 1\n", COMMAND + "in", 1),
    ("theorem", "theorem t : True := trivial\n", COMMAND + "theorem", 1),
    ("opaque", "opaque O : Nat\n", COMMAND + "opaque", 1),
    ("axiom", "axiom X : False\n", COMMAND + "axiom", 1),
    ("attribute", "attribute [simp] Nat.add_comm\n", COMMAND + "attribute", 1),
    ("export", "export Nat (add)\n", COMMAND + "export", 1),
    ("include", "include x\n", COMMAND + "include", 1),
    ("omit", "omit x\n", COMMAND + "omit", 1),
):
    finding("command." + name, "R/K7", source, line, 0, "kind " + kind)

for word in ("noncomputable", "partial", "unsafe", "nonrec", "public", "meta"):
    finding(f"decl.modifier.{word}", "R/K4", f"{word} def f := 1\n", 1, 0, "kind " + COMMAND + word)

for attr in ("inline", "implemented_by alternative", 'extern "trial_symbol"', "export trialSymbol", "csimp", "simp"):
    finding(f"decl.attribute.{attr.split()[0]}", "R/K4", f"@[{attr}] def f := 1\n", 1, 0,
            "kind " + TERM + "attributes")

for word in ("scoped", "local"):
    finding(f"decl.instance.{word}", "R/K4", f"{word} instance : Inhabited Nat := ⟨0⟩\n", 1, 0,
            "kind " + TERM + word)

finding("decl.instance.named-priority", "R/K4", "instance (priority := low) : Inhabited Nat := ⟨0⟩\n",
        1, 9, "kind " + COMMAND + "namedPrio")
finding("decl.def-deriving", "R/K4", "def T := Nat\nderiving Repr\n", 2, 0,
        "atom " + COMMAND + "definition deriving")

for name, body, kind in (
    ("sorry", "sorry", TERM + "sorry"),
    ("unsafe", "unsafe x", TERM + "unsafe"),
    ("by", "by exact 1", TERM + "byTactic"),
    ("include-str", 'include_str "x"', "Lean.includeStr"),
    ("interpolation", 's!"x"', "termS!_"),
    ("interpolation-hole", 's!"{1}"', "termS!_"),
    ("dbg-trace", 'dbg_trace "x"; 1', TERM + "dbgTrace"),
    ("quotation", "`(1)", TERM + "quot"),
    ("by-elab", "by_elab exact 1", "Lean.byElab"),
):
    finding("term." + name, "R/K6", f"def a := {body}\n", 1, 9, "kind " + kind)

at("term.while", "R/K6", "def a := do while true do pure (); pure ()\n", "while", "kind " + TERM + "doWhile")
for name, body, col, kind in (
    ("positive", "let +nondep n := 1; n", 13, "letPosOpt"),
    ("eq", "let (eq := h) n := 1; n", 13, "letOptEq"),
    ("negative", "have -zeta n := 1; n", 14, "letNegOpt"),
):
    finding("term.let-config." + name, "R/K6", f"def x := {body}\n", 1, col, "kind " + TERM + kind)

for name, suffix, col, kind in (
    ("decide-native", "decreasing_by decide +native", 21, TACTIC + "configItem"),
    ("decide-kernel", "decreasing_by decide +kernel", 21, TACTIC + "configItem"),
    ("omega-config", "decreasing_by omega +splitDisjunctions", 20, TACTIC + "configItem"),
    ("partial-fixpoint", "partial_fixpoint", 0, TERMINATION + "partialFixpoint"),
    ("inductive-fixpoint", "inductive_fixpoint", 0, TERMINATION + "inductiveFixpoint"),
    ("by-query", "termination_by?", 0, TERMINATION + "terminationBy?"),
    ("simp-wf", "decreasing_by simp_wf; omega", 14, "tacticSimp_wf"),
):
    finding("termination." + name, "R/K5", REC + suffix + "\n", 2, col, "kind " + kind)

for attr in ("noncomputable", "@[expose]", "public"):
    token = attr if attr != "@[expose]" else "@["
    finding(f"decl.section.{token if token != '@[' else 'attribute'}", "R/K3", attr + " section\nend\n", 1, 0,
            "atom " + COMMAND + "sectionHeader " + token)

finding("decl.deriving.attribute", "R/K4", STRUCT + "  deriving @[expose] Repr\n", 3, 11,
        "atom " + COMMAND + "derivingClass @[")
finding("decl.deriving.name", "R/K4", STRUCT + "  deriving Repr, ToJson\n", 3, 17, "name deriving ToJson")
finding("decl.deriving.shape", "R/K4", STRUCT + "  deriving Repr (x := 1)\n", 3, 11,
        "shape " + COMMAND + "derivingClass")
finding("decl.class-inductive", "K4", "class inductive T where\n  | item : T\n", 1, 0,
        "kind " + COMMAND + "classInductive")
for kind in ("Scoped", "Hiding", "Renaming"):
    expr = {"Scoped": "scoped Array", "Hiding": "Nat hiding add", "Renaming": "Nat renaming add -> plus"}[kind]
    finding(f"command.open-{kind.lower()}", "K7/P4", f"open {expr}\n", 1, 5, "kind " + COMMAND + "open" + kind)

for name, source, clause in (
    ("private", "private def f := 1\n", "R/K4"),
    ("protected", "namespace Trial\nprotected def f := 1\nend Trial\n", "K4"),
    ("abbrev", "abbrev T := Nat\n", "K4"),
    ("instance", "instance : Inhabited Nat := ⟨0⟩\n", "K4"),
    ("class", "class Trial where\n  run : Nat\n", "K4"),
    ("def-equations", "def fold : Nat → Nat\n  | 0 => 0\n  | Nat.succ n => fold n\n", "K4"),
    ("inductive", "inductive T where\n  | item : T\n", "K4"),
    ("mutual", "mutual\n  inductive First where\n    | nil : First\n"
               "  inductive Second where\n    | one : First → Second\nend\n", "K4/C1"),
    ("deriving-two", STRUCT + "  deriving Repr, BEq\n", "R/K4"),
    ("extends", "structure Parent where\n  a : Nat\nstructure Child extends toParent : Parent\n", "R/I3b"),
    ("docs", '/-! Documentation: syntax "do not parse".\nUnicode: 🦆\n-/\n'
             '/-- Doc payload: `sorry` and `#eval`. -/\ndef documented := 1\n', "K2"),
    ("scope-kinds", "universe u\nsection\nvariable (α : Type u)\ndef f (x : α) := x\nend\n", "R/K3"),
    ("binders", "universe u v\ndef binder {α : Type u} ⦃β : Type v⦄ [Inhabited β] (x : α) := (x, default)\n"
                "def bounded := ∀ n > (0 : Nat), n ≠ 0\n", "K6"),
    ("sorts", "universe u v\ndef x := Sort (max (u + 1) (imax v 0))\ndef y := Prop\n", "K6"),
    ("choice", "def p : Prop := ∃ n : Nat, n = n\ndef s := {1}\ndef e := {}\n", "K1/K6"),
    ("wildcard", "def f := fun _ => 1\n", "R/I3a/K6"),
    ("escaped-ident", "def «x y» := 1\n", "R/I3/K0"),
    ("literals", 'def nat := 0xAF\ndef text := "quoted \\t data"\ndef glyph := \'λ\'\n'
                 "def sci := 1.25e3\ndef n := `Nat.succ\ndef nn := ``Nat.succ\n"
                 "def idx := (1, 2).2\n", "K6"),
    ("ascii-aliases", "def f : Nat -> Nat := λ n => if n <= 2 then n + 1 else n - 1\n"
                      "def g := fun n => n >= (1 : Nat)\n", "K0/K6"),
    ("let-have", "def f := let n := 1; have q := n; q\n", "K6"),
    ("notations", "def f (xs : Array Nat) (i : Nat) := xs[i]!\ndef g := [1] ++ [2] ++ 3 :: []\n"
                  "def h := #[1, 2]\ndef k := (1 : Nat) <<< 3\n", "R/K6"),
    ("do", "def f : Id Nat := do\n  let mut n := 0\n  for x in [1, 2] do\n    n := n + x\n  return n\n", "R/K6"),
    ("do-arrow", "def f : Option Nat := do\n  let n <- some 1\n  if n == 0 then return 2\n  return n\n", "K0/K6"),
    ("termination-omega", REC + "decreasing_by omega\n", "R/K5"),
    ("termination-decide", REC + "decreasing_by decide\n", "R/K5"),
    ("termination-wrappers", REC + "termination_by n\ndecreasing_by\n  · all_goals (omega)\n", "K5"),
):
    accepted("accept." + name, clause, source)

for handler in ("DecidableEq", "Repr", "BEq", "Hashable", "Ord", "Inhabited"):
    accepted("accept.deriving." + handler, "K4/Q1", STRUCT + f"  deriving {handler}\n")
    accepted("accept.deriving-recursive." + handler, "K4/Q1",
             f"inductive Tree where\n  | leaf\n  | next : Tree → Tree\n  deriving {handler}\n")


def term(rng: random.Random, depth: int) -> str:
    if depth == 0:
        return str(rng.randrange(100))
    left = term(rng, depth - 1)
    match rng.randrange(4):
        case 0:
            return f"({left})"
        case 1:
            return f"({left} {rng.choice(('+', '*', '%'))} {term(rng, depth - 1)})"
        case 2:
            return f"(let n := {left}; n)"
        case _:
            return f"(if {left} <= 12 then {term(rng, depth - 1)} else 9)"


@case("accept.generated", "K1/K3/K4/K6/C1", "0; generated admitted programs accepted as one batch")
def generated_admission(c: Context) -> None:
    rng = random.Random(SEED)
    batch = sources({f"Generated.M{i:02}": f"namespace Fixture.N{i}\n"
        + "".join(f"def f{j} : Nat := {term(rng, rng.randrange(1, 5))}\n" for j in range(3))
        + f"end Fixture.N{i}\n" for i in range(24)})
    check(c, batch, grammar=dict.fromkeys(batch, INIT), args_order=list(reversed(batch)))


# Additional forbidden syntax whose parser names are independently qualified with D4.
for name, source, token, kind, grammar in (
    ("panic", 'def a := panic! "x"\n', "panic!", TERM + "panic", INIT),
    ("assert", "def a := assert! true; 1\n", "assert!", TERM + "assert", INIT),
    ("unreachable", "def a := unreachable!\n", "unreachable!", TERM + "unreachable", INIT),
    ("angle", "def a := ‹Nat›\n", "‹", "term‹_›", INIT),
    ("subst", "def a (h : 1 = 1) := h ▸ 1\n", "h ▸", TERM + "subst", INIT),
    ("nomatch", "def a (n : Empty) := nomatch n\n", "nomatch", TERM + "nomatch", INIT),
    ("nofun", "def a : Empty → Nat := nofun\n", "nofun", TERM + "nofun", INIT),
    ("show", "def a := show Nat from 1\n", "show", TERM + "show", INIT),
    ("suffices", "def a := suffices h : True from 1; True.intro\n", "suffices", TERM + "suffices", INIT),
    ("calc", "def a := calc\n  0 = 0 := rfl\n", "calc", "Lean.calc", INIT),
    ("let-rec", "def a := let rec f (n : Nat) := n; f 0\n", "let rec", TERM + "letrec", INIT),
    ("open", "def a := open Nat in 1\n", "open", TERM + "open", INIT),
    ("set-option", "def a := set_option autoImplicit true in 1\n", "set_option", TERM + "set_option", INIT),
    ("sigma", "def a := Σ x : Nat, Nat\n", "Σ", "termΣ_,_", INIT),
    ("repeat", "def a := do\n  repeat\n    pure ()\n", "repeat", TERM + "doRepeat", INIT),
    ("repeat-until", "def a := do\n  repeat\n    pure ()\n  until true\n", "repeat", TERM + "doRepeatUntil", INIT),
    ("try", "def a := do\n  try pure () catch _ => pure ()\n", "try", TERM + "doTry", INIT),
    ("do-let-rec", "def a := do\n  let rec f (n : Nat) := n\n  pure (f 0)\n", "let rec", TERM + "doLetRec", INIT),
    ("do-trace", 'def a := do\n  dbg_trace "x"\n  pure ()\n', "dbg_trace", TERM + "doDbgTrace", INIT),
    ("do-assert", "def a := do\n  assert! true\n  pure ()\n", "assert!", TERM + "doAssert", INIT),
    ("range", "import Std\ndef a := 0...2\n", "0...", "Std.term_..._", STD),
    ("closed-range", "import Std\ndef a := 0...=2\n", "0...=", "Std.term_...=_", STD),
    ("legacy-range", "import Std\ndef a := [0:2]\n", "[0:", "Std.Legacy.Range.term[_:_]", STD),
):
    at("term.extra." + name, "K6/C1", source, token, "kind " + kind, grammar)
