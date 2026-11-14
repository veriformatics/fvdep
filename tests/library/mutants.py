#!/usr/bin/env python3
"""Hand mutants of the launch specs (credit for tester-5's A cases, green on both stubs): each
mutant = exact replacements, each applied once; the A cases run per mutant (`FVDEP_LIBRARY_CASE=A.`);
FAIL ids → `.gate/mutants/<key>.log` + `results.tsv`; files restored after each. Edits the tree in
place ⇒ run on a vflab workspace from the repo root, alone:
`tools/vflab-run bash -c 'python3 -I tests/library/mutants.py [KEY ...]'`."""
import os
import subprocess
import sys
from pathlib import Path

R = "Fvdep/Base64/Rfc4648/V1_0_0.lean"
E = "Fvdep/Base64/Encode/V1_0_0.lean"
EU = "Fvdep/Base64/EncodeUrl/V1_0_0.lean"
D = "Fvdep/Base64/Decode/V1_0_0.lean"
DU = "Fvdep/Base64/DecodeUrl/V1_0_0.lean"
P = "Fvdep/Semver/Parse/V1_0_0.lean"
C = "Fvdep/Semver/Compare/V1_0_0.lean"
WS = "fun c => !(c == ' ' || c == '\\t' || c == '\\n' || c == '\\r')"

MUTANTS = [
    ("MB1 filling bits unchecked", [(R, "if i1 % 16 = 0 then", "if true then"),
                                    (R, "if i2 % 4 = 0 then", "if true then")]),
    ("MB2 standard 62/63 swapped", [(R, '0123456789+/".toList', '0123456789/+".toList')]),
    ("MB3 url 62/63 swapped", [(R, '0123456789-_".toList', '0123456789_-".toList')]),
    ("MB4 encode padding dropped", [(R, "(n / 64 % 64),\n      '=']", "(n / 64 % 64)]"),
                                    (R, "(n / 4096 % 64), '=', '=']", "(n / 4096 % 64)]")]),
    ("MB5 full-group symbols 2/3 swapped",
     [(R, "      symbol alphabet (n / 4096 % 64) ::\n      symbol alphabet (n / 64 % 64) ::",
       "      symbol alphabet (n / 64 % 64) ::\n      symbol alphabet (n / 4096 % 64) ::")]),
    ("MB6 encoders append LF",
     [(E, ":= encodeWith standard", ":= fun b => encodeWith standard b ++ ['\\n']"),
      (EU, ":= encodeWith url", ":= fun b => encodeWith url b ++ ['\\n']")]),
    ("MB7 quad first byte +1", [(R, "some [(n / 65536).toUInt8,", "some [(n / 65536 + 1).toUInt8,")]),
    ("MB8 final 1-byte low bits", [(R, "(i0 * 4 + i1 / 16).toUInt8", "(i0 * 4 + i1 % 16).toUInt8")]),
    ("MB9 final 2-byte second byte", [(R, "(n / 4 % 256).toUInt8]", "(n % 256).toUInt8]")]),
    ("MB10 empty input refused", [(R, "Option (List UInt8)\n  | [] => some []", "Option (List UInt8)\n  | [] => none")]),
    ("MB11 foreign symbols read as 0", [(R, ":= alphabet.idxOf? c", ":= some ((alphabet.idxOf? c).getD 0)")]),
    ("MB12 partial tail ignored", [(R, "      some (q ++ t)\n  | _ => none", "      some (q ++ t)\n  | _ => some []")]),
    ("MB13 decoding stops at padding", [(R, "    if rest.isEmpty then final", "    if rest.isEmpty || c3 == '=' then final")]),
    ("MB14 whitespace read as 0",
     [(R, ":= alphabet.idxOf? c",
       ":= if c == ' ' || c == '\\t' || c == '\\n' || c == '\\r' then some 0 else alphabet.idxOf? c")]),
    ("MB15 decoders skip whitespace",
     [(D, ":= decodeWith standard", f":= fun s => decodeWith standard (s.filter {WS})"),
      (DU, ":= decodeWith url", f":= fun s => decodeWith url (s.filter {WS})")]),
    ("MS1 leading zeros accepted", [(P, "(cs.head? == some '0' && cs.length > 1)", "false")]),
    ("MS2 any identifier char", [(P, "def identChar (c : Char) : Bool := c.isDigit || c.isAlpha || c == '-'",
                                  "def identChar (_c : Char) : Bool := true")]),
    ("MS3 digits = chars from 0 up", [(P, "!cs.all Char.isDigit", "!cs.all (fun c => c.toNat ≥ 48)")]),
    ("MS4 whitespace trimmed",
     [(P, "def parse (s : List Char) : Option Version := do\n",
       "def parse (s₀ : List Char) : Option Version := do\n  let s := ((s₀.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse\n")]),
    ("MS5 empty identifiers accepted",
     [(P, "def preIdent (cs : List Char) : Option Ident :=\n  if cs.isEmpty || !cs.all identChar then none",
       "def preIdent (cs : List Char) : Option Ident :=\n  if cs.isEmpty then some (.alnum []) else if !cs.all identChar then none"),
      (P, "  if cs.isEmpty || !cs.all identChar then none else some cs", "  if !cs.all identChar then none else some cs")]),
    ("MS6 core components beyond three ignored",
     [(P, "let [ma, mi, pa] := splitOn '.' core | none", "let ma :: mi :: pa :: _ := splitOn '.' core | none")]),
    ("MS7 missing core components = 0",
     [(P, "let [ma, mi, pa] := splitOn '.' core | none",
       "let (ma, mi, pa) := match splitOn '.' core with\n    | [a] => (a, ['0'], ['0'])\n    | [a, b] => (a, b, ['0'])\n    | a :: b :: c :: _ => (a, b, c)\n    | [] => ([], [], [])")]),
    ("MS8 empty numeric = 0", [(P, "  if cs.isEmpty || !cs.all Char.isDigit", "  if cs.isEmpty then some 0 else if !cs.all Char.isDigit")]),
    ("MS9 empty input = 0.0.0",
     [(P, "def parse (s : List Char) : Option Version := do\n",
       "def parse (s : List Char) : Option Version := do\n  if s.isEmpty then return { major := 0, minor := 0, patch := 0, pre := [], build := [] }\n")]),
    ("MS10 leading sign dropped",
     [(P, "let (main, build?) := splitFirst '+' s", "let (main, build?) := splitFirst '+' (match s with | '+' :: t => t | '-' :: t => t | t => t)")]),
    ("MS11 numeric reads a digit prefix",
     [(P, "def numeric (cs : List Char) : Option Nat :=\n", "def numeric (cs₀ : List Char) : Option Nat :=\n  let cs := cs₀.takeWhile Char.isDigit\n")]),
    ("MS12 minor and patch swapped", [(P, "  some { major, minor, patch, pre, build }", "  some { major, minor := patch, patch := minor, pre, build }")]),
    ("MS13 numeric 0 refused", [(P, "(cs.head? == some '0' && cs.length > 1)", "(cs.head? == some '0')")]),
    ("MS14 identifier class by its first char", [(P, "  else if cs.all Char.isDigit then (numeric cs).map .num", "  else if cs.head?.any Char.isDigit then (numeric cs).map .num")]),
    ("MS15 numeric capped at 20 digits", [(P, "  else some (cs.foldl", "  else if cs.length > 20 then none else some (cs.foldl")]),
    ("MS16 build leading zeros refused",
     [(P, "  if cs.isEmpty || !cs.all identChar then none else some cs",
       "  if cs.isEmpty || !cs.all identChar || (cs.all Char.isDigit && cs.head? == some '0' && cs.length > 1) then none else some cs")]),
    ("MS17 build dropped", [(P, "  some { major, minor, patch, pre, build }",
                              "  some { major, minor, patch, pre, build := build.take 0 }")]),
    ("MS18 identifier char without -", [(P, "c.isDigit || c.isAlpha || c == '-'", "c.isDigit || c.isAlpha")]),
    ("MS19 pre-release reversed", [(P, "      (splitOn '.' p).mapM preIdent", "      ((splitOn '.' p).mapM preIdent).map List.reverse")]),
    ("MR1 decimal 0 = empty", [(P, "  if n < 10 then [digit n]", "  if n = 0 then [] else if n < 10 then [digit n]")]),
    ("MR2 render minor/patch swapped",
     [(P, "decimal v.major ++ '.' :: decimal v.minor ++ '.' :: decimal v.patch", "decimal v.major ++ '.' :: decimal v.patch ++ '.' :: decimal v.minor")]),
    ("MR3 render drops build", [(P, "else '+' :: joinDot v.build", "else []")]),
    ("MR4 join without dots", [(P, "  | w :: v :: ws => w ++ '.' :: joinDot (v :: ws)", "  | w :: v :: ws => w ++ joinDot (v :: ws)")]),
    ("MR5 pre-release marker ~", [(P, "else '-' :: joinDot (v.pre.map renderIdent)", "else '~' :: joinDot (v.pre.map renderIdent)")]),
    ("MC1 num above alnum", [(C, "  | .num _, .alnum _ => .lt\n  | .alnum _, .num _ => .gt", "  | .num _, .alnum _ => .gt\n  | .alnum _, .num _ => .lt")]),
    ("MC2 ident prefix after extension",
     [(C, "  | [], _ :: _ => .lt\n  | _ :: _, [] => .gt\n  | a :: as, b :: bs => (ident a b)", "  | [], _ :: _ => .gt\n  | _ :: _, [] => .lt\n  | a :: as, b :: bs => (ident a b)")]),
    ("MC3 reversed comparator",
     [(C, "  (nat a.major b.major).then <|\n    (nat a.minor b.minor).then <| (nat a.patch b.patch).then (pre a.pre b.pre)",
       "  (nat b.major a.major).then <|\n    (nat b.minor a.minor).then <| (nat b.patch a.patch).then (pre b.pre a.pre)")]),
    ("MC4 build compared",
     [(C, "(nat a.patch b.patch).then (pre a.pre b.pre)", "(nat a.patch b.patch).then ((pre a.pre b.pre).then (chars a.build.flatten b.build.flatten))")]),
    ("MC5 numbers compared as text", [(C, "  | .num a, .num b => nat a b", "  | .num a, .num b => chars (toString a).toList (toString b).toList")]),
    ("MC6 text compared case-insensitively", [(C, "(nat a.toNat b.toNat)", "(nat a.toLower.toNat b.toLower.toNat)")]),
    ("MC7 text by length first", [(C, "  | .alnum a, .alnum b => chars a b", "  | .alnum a, .alnum b => (nat a.length b.length).then (chars a b)")]),
    ("MC8 text prefix after extension",
     [(C, "  | [], _ :: _ => .lt\n  | _ :: _, [] => .gt\n  | a :: as, b :: bs => (nat a.toNat", "  | [], _ :: _ => .gt\n  | _ :: _, [] => .lt\n  | a :: as, b :: bs => (nat a.toNat")]),
    ("MC9 chars compared by low byte", [(C, "(nat a.toNat b.toNat)", "(nat (a.toNat % 256) (b.toNat % 256))")]),
    ("MC10 pre-release above release", [(C, "  | [], _ :: _ => .gt\n  | _ :: _, [] => .lt\n  | a :: as, b :: bs => idents", "  | [], _ :: _ => .lt\n  | _ :: _, [] => .gt\n  | a :: as, b :: bs => idents")]),
    ("MC11 pre-release before the core",
     [(C, "  (nat a.major b.major).then <|\n    (nat a.minor b.minor).then <| (nat a.patch b.patch).then (pre a.pre b.pre)",
       "  (pre a.pre b.pre).then <|\n    (nat a.major b.major).then <| (nat a.minor b.minor).then (nat a.patch b.patch)")]),
    ("MC12 minor ignored", [(C, "    (nat a.minor b.minor).then <| (nat a.patch b.patch)", "    (nat a.patch b.patch)")]),
    ("MC13 ties read as lt", [(C, "def nat (a b : Nat) : Ordering := if a < b then .lt else if a = b then .eq else .gt",
                                "def nat (a b : Nat) : Ordering := if a ≤ b then .lt else .gt")]),
    ("MC14 num vs text by text length",
     [(C, "  | .num _, .alnum _ => .lt\n  | .alnum _, .num _ => .gt",
       "  | .num n, .alnum s => if n < s.length then .lt else .gt\n  | .alnum s, .num n => if n < s.length then .gt else .lt")]),
    ("MC15 numbers beyond 2^53 - 1 compared as text",
     [(C, "def nat (a b : Nat) : Ordering := if a < b then .lt else if a = b then .eq else .gt",
       "def nat (a b : Nat) : Ordering :=\n  if a ≤ 9007199254740991 ∧ b ≤ 9007199254740991 then"
       " if a < b then .lt else if a = b then .eq else .gt\n"
       "  else Ord.compare (toString a) (toString b)")]),
]


def main() -> int:
    only = sys.argv[1:]
    out = Path(".gate/mutants")
    out.mkdir(parents=True, exist_ok=True)
    summary = []
    for label, edits in MUTANTS:
        key = label.split()[0]
        if only and key not in only:
            continue
        files = sorted({path for path, _, _ in edits})
        saved = {path: Path(path).read_text() for path in files}
        status = "ran"
        try:
            for path, old, new in edits:
                text = Path(path).read_text()
                if text.count(old) != 1:
                    status = f"noapply:{path}:{text.count(old)}"
                    break
                Path(path).write_text(text.replace(old, new))
            fails = []
            total = ""
            if status == "ran":
                proc = subprocess.run(["bash", "tests/library/run.sh"], capture_output=True, text=True,
                                      env={**os.environ, "FVDEP_LIBRARY_CASE": "A."})
                (out / f"{key}.log").write_text(proc.stdout + proc.stderr)
                for line in proc.stdout.splitlines():
                    if line.startswith("FAIL "):
                        fails.append(line.split()[1])
                    elif line.startswith("TOTAL "):
                        total = line
                if not total:
                    status = f"nototal:rc{proc.returncode}"
        finally:
            for path, text in saved.items():
                Path(path).write_text(text)
        row = f"{key}\t{label}\t{status}\t{total}\t{','.join(fails)}"
        summary.append(row)
        print(f"MUT {key} {status} {total} fails={len(fails)}", flush=True)
    (out / "results.tsv").write_text("\n".join(summary) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
