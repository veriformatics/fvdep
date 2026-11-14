#!/usr/bin/env python3
"""Regenerate the inventory after an acceptance-suite change, never during a run."""
import csv
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
from harness import CASES  # noqa: E402 — isolated mode loads only this suite.


def main():
    for path in sorted(HERE.glob("test_*.py")):
        spec = importlib.util.spec_from_file_location(path.stem, path)
        assert spec is not None and spec.loader is not None
        spec.loader.exec_module(importlib.util.module_from_spec(spec))
    # A case keeps its merge status; a new case starts unmerged.
    path = HERE / "MANIFEST.tsv"
    status = {}
    if path.is_file():
        with path.open(newline="") as file:
            status = {row["id"]: row["status"] for row in csv.DictReader(file, delimiter="\t")}
    with path.open("w", newline="") as file:
        writer = csv.writer(file, delimiter="\t", lineterminator="\n")
        writer.writerow(["id", "unit", "source", "predicate", "kind", "status"])
        for test in sorted(CASES.values(), key=lambda c: (int(c.unit[1:]), c.id)):
            writer.writerow([test.id, test.unit, test.source, test.predicate, test.kind,
                             status.get(test.id, "unmerged")])
    print(f"MANIFEST: {len(CASES)} cases")


if __name__ == "__main__":
    main()
