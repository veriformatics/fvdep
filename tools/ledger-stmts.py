#!/usr/bin/env python3
"""Print coverage-ledger statements (contract U2 L1 + L3) copied from theorem headers.

stdin (JSON): [{"namespace": "FvdepLedger.Rows.StatusClaims", "file": "tool/FvdepCore/Status.lean",
  "opens": "FvdepCore FvdepCore.Status", "items": [["<statement>", "<theorem>", "<doc>"], ...]}, ...]
stdout: per entry `namespace … end` with `def <statement> : Prop := ∀ <binders>, <type>`, the
theorem's own binder + type text: under the same opens it elaborates to the theorem's type (the
checker compares both terms; a difference = finding `statement`). A binder the rest of the statement
never names gets a `_` prefix (the unusedVariables linter rejects it inside a `def`).
"""

import json
import re
import sys
from pathlib import Path

OPEN = "([{⟨"
CLOSE = ")]}⟩"


def header(src: str, theorem: str) -> tuple[str, str]:
    """The binders + type of `theorem` (text between its name and `:=`, split at the top-level `:`)."""
    m = re.search(r"^(?:private )?theorem " + re.escape(theorem) + r"\b", src, re.M)
    if m is None:
        raise SystemExit(f"ledger-stmts: no theorem {theorem}")
    sig = src[m.end() : src.index(":=", m.end())]
    depth = 0
    for k, ch in enumerate(sig):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == ":" and depth == 0:
            return " ".join(sig[:k].split()), " ".join(sig[k + 1 :].split())
    raise SystemExit(f"ledger-stmts: {theorem} has no top-level ':'")


def groups(binders: str) -> list[str]:
    """Top-level bracket groups, in order."""
    out: list[str] = []
    depth = 0
    start = 0
    for k, ch in enumerate(binders):
        if ch in OPEN:
            if depth == 0:
                start = k
            depth += 1
        elif ch in CLOSE:
            depth -= 1
            if depth == 0:
                out.append(binders[start : k + 1])
    return out


def mark_unused(binders: str, typ: str) -> str:
    """Prefix `_` to each explicit binder name the later binders + the type never mention."""
    gs = groups(binders)
    out: list[str] = []
    for i, g in enumerate(gs):
        if g[0] in "({" and " : " in g:
            names, rest = g[1:-1].split(" : ", 1)
            later = " ".join(gs[i + 1 :]) + " " + rest + " " + typ
            names = " ".join(
                n if n.startswith("_") or re.search(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", later)
                else "_" + n
                for n in names.split()
            )
            g = g[0] + names + " : " + rest + g[-1]
        out.append(g)
    return " ".join(out)


def main() -> None:
    for entry in json.load(sys.stdin):
        src = Path(entry["file"]).read_text()
        print(f"namespace {entry['namespace']}\n\nopen {entry['opens']}\n")
        for statement, theorem, doc in entry["items"]:
            binders, typ = header(src, theorem)
            body = f"∀ {mark_unused(binders, typ)}, {typ}" if binders else typ
            print(f"/-- {doc} -/\ndef {statement} : Prop :=\n  {body}\n")
        print(f"end {entry['namespace']}\n")


if __name__ == "__main__":
    main()
