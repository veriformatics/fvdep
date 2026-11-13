#!/usr/bin/env python3
"""Every pinned dependency has a row in docs/dependencies.md (gate stage `deps`).

Pins: the Lean toolchain of every `lean-toolchain`, each tools/tools.lock tool, each workflow action
(`uses: owner/repo[/path]@…`), each git package of every tracked `lake-manifest.json` (by its
GitHub `owner/repo`). A row = the name in backticks somewhere in the table. Prints each missing
name. Usage: python3 -I tools/check-deps.py
"""

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLE = ROOT / "docs/dependencies.md"


def tracked(*patterns: str) -> list[Path]:
    out = subprocess.run(["git", "ls-files", "-co", "--exclude-standard", "--", *patterns],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return [ROOT / line for line in out.splitlines() if line]


def pins() -> set[str]:
    names: set[str] = set()
    for f in tracked("lean-toolchain", "*/lean-toolchain"):
        m = re.match(r"(leanprover/lean4):", f.read_text(encoding="utf-8").strip())
        if m:
            names.add(m.group(1))
    for line in (ROOT / "tools/tools.lock").read_text(encoding="utf-8").splitlines():
        cols = line.split()
        if len(cols) == 5 and not line.startswith("#"):
            names.add(cols[0])
    for f in tracked(".github/workflows/*.yml"):
        for m in re.finditer(r"^\s*(?:-\s*)?uses:\s*([^@\s]+)@", f.read_text(encoding="utf-8"), re.M):
            names.add(m.group(1))
    for f in tracked("lake-manifest.json", "*/lake-manifest.json"):
        if str(f.relative_to(ROOT)).startswith("tests/"):
            continue
        for p in json.loads(f.read_text(encoding="utf-8")).get("packages", []):
            if p.get("type") == "git":
                names.add(re.sub(r"\.git$", "", p["url"].removeprefix("https://github.com/")))
    return names


def main() -> int:
    if not TABLE.is_file():
        print(f"deps: {TABLE.relative_to(ROOT)} missing", file=sys.stderr)
        return 1
    table = TABLE.read_text(encoding="utf-8")
    missing = sorted(n for n in pins() if f"`{n}`" not in table)
    for n in missing:
        print(f"deps: {n} has no row in docs/dependencies.md", file=sys.stderr)
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
