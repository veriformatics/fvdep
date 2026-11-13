#!/usr/bin/env python3
"""Known vulnerabilities in the declared lockfile set (gate stage `vulns`).

tools/lockfiles.txt declares every lockfile of the tree: one path per line; `fixture <path>` = a
test input never installed (listed, not scanned); `none` alone = the set is empty on purpose. Every
listed file must exist and every lockfile in the graded file set must be listed, so a new lockfile
cannot escape the scan. osv-scanner then reads the scanned set; its rc 128 (no packages found) is
red, never success. Vendored C has no lockfile: each vendor/*/lock.json commit is queried at OSV by
commit (matched against OSV's git ranges); a listed advisory or a failed query is red. Usage:
python3 -I tools/check-vulns.py <osv-scanner binary>
"""

import json
import subprocess
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIST = "tools/lockfiles.txt"
OSV_QUERY = "https://api.osv.dev/v1/query"
NAMES = {"pnpm-lock.yaml", "package-lock.json", "yarn.lock", "bun.lock", "deno.lock", "Cargo.lock",
         "uv.lock", "poetry.lock", "pdm.lock", "Pipfile.lock", "go.sum", "Gemfile.lock",
         "composer.lock"}


def vendor_findings() -> list[str]:
    """OSV advisories listed for each vendored upstream commit (+ every failed query)."""
    out = subprocess.run(["git", "ls-files", "-co", "--exclude-standard", "--", "vendor/*/lock.json"],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    findings = []
    for rel in out.splitlines():
        try:
            commit = json.loads((ROOT / rel).read_text(encoding="utf-8"))["commit"]
            req = urllib.request.Request(OSV_QUERY, data=json.dumps({"commit": commit}).encode(),
                                         headers={"Content-Type": "application/json"})
            with urllib.request.urlopen(req, timeout=60) as r:
                ids = sorted(v["id"] for v in json.load(r).get("vulns", []))
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as e:
            findings.append(f"{rel}: OSV commit query failed: {e}")
            continue
        if ids:
            findings.append(f"{rel}: commit {commit}: OSV lists {', '.join(ids)}")
    return findings


def main(scanner: str) -> int:
    errors, scanned, fixtures, none = [], [], [], False
    for raw in (ROOT / LIST).read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line == "none":
            none = True
        elif line.startswith("fixture "):
            fixtures.append(line.removeprefix("fixture ").strip())
        else:
            scanned.append(line)
    listed = scanned + fixtures
    if none and listed:
        errors.append(f"{LIST}: `none` beside listed lockfiles")
    if not none and not listed:
        errors.append(f"{LIST}: empty; declare `none` if the tree has no lockfile")
    for path in listed:
        if not (ROOT / path).is_file():
            errors.append(f"{LIST}: {path} does not exist")
    files = subprocess.run(["git", "ls-files", "-co", "--exclude-standard", "-z"], cwd=ROOT,
                           capture_output=True, text=True, check=True).stdout.split("\0")
    for path in sorted(f for f in files if f and Path(f).name in NAMES):
        if path not in listed:
            errors.append(f"{path}: lockfile not listed in {LIST}")
    for e in errors:
        print(f"vulns: {e}", file=sys.stderr)
    if errors:
        return 1
    vendor = vendor_findings()
    for e in vendor:
        print(f"vulns: {e}", file=sys.stderr)
    if not scanned:
        print("vulns: no lockfile to scan (declared none or fixtures only)")
        return 1 if vendor else 0
    args = [scanner, "scan", "source"]
    for path in scanned:
        args += ["--lockfile", path]
    rc = subprocess.run(args, cwd=ROOT).returncode
    if rc == 128:
        print("vulns: osv-scanner found no packages in the declared lockfiles", file=sys.stderr)
        return 1
    return rc or (1 if vendor else 0)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: check-vulns.py <osv-scanner binary>", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
