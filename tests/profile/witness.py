#!/usr/bin/env python3
"""U6 Q1 + Q2 (contract `docs/contracts/U6-profile.md`): the witness corpus.

Every target of the v1 table (`fvdep-dev profile targets`: each rule, each (kind, atom) pair outside
the payload shapes, the scope shapes' rows, each anchor's slot (an optional one absent + present),
each deriving class) must be covered by a fixture under `tests/profile/witness/` that the checker
accepts + that compiles on the same bytes: one `fvdep-dev phase check ... --profile` over the whole
corpus (consumer role, the trial library), then `fvdep-dev profile witness` over the frozen project
files. Prints `uncovered<TAB><target>` lines. Q1's negative controls (`witness/controls/*.lean`,
first line `-- expect phase1: <text>`) run one by one: accepted by the profile, their phase 1 fails
naming `<text>` (a shadowed deriving class: Lean finds no handler). Exit 0 = every target covered +
every control as expected, 1 = the corpus refused, a failed build, an uncovered target or a control
off its expectation, 2 = harness failure.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tests.profile.harness import (  # noqa: E402 -- python -I imports the trusted checkout above
    DEV, HERE, HEX, PHASE_IMPL, ROOT, Context, Toolchain, env_base, module_path, need, sources,
)

FIXTURES = HERE / "witness"
CONTROLS = FIXTURES / "controls"
RUNS = HERE / ".runs"


def dev(args: list[str]) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run([DEV, *args], cwd=ROOT, env=env_base(), input=b"", capture_output=True,
                          timeout=900, check=False)


def control(parent: Path, toolchain: Toolchain, f: Path) -> str | None:
    """One control module alone: the profile accepts it, its phase 1 fails naming the expected text."""
    m = re.fullmatch(r"-- expect phase1: (.+)", f.read_text().splitlines()[0])
    need(m is not None, f"{f.name}: the first line must be `-- expect phase1: <text>`")
    assert m is not None
    ctx = Context(parent / f"control-{f.stem}", f"control {f.stem}", toolchain)
    project, _ = ctx.project(sources({"Impl": PHASE_IMPL, f"Witness.{f.stem}": f.read_bytes()}))
    r = ctx.phase(project, ctx.library())
    text = r.out.decode("utf-8", "backslashreplace") + r.err.decode("utf-8", "backslashreplace")
    lines = r.out.decode("utf-8", "backslashreplace").splitlines()
    failed = [line for line in lines if line.startswith("phase1 failed:")]
    if "accepted" not in lines:
        return f"{f.name}: the profile did not accept it (exit {r.rc})"
    if not failed:
        return f"{f.name}: phase 1 did not fail (exit {r.rc})"
    if m[1] not in text:
        return f"{f.name}: phase 1 failed without `{m[1]}`: {failed[0][:300]}"
    return None


def main() -> int:
    files = sorted(FIXTURES.glob("*.lean"))
    need(files, "no witness fixture under tests/profile/witness")
    batch = sources({"Impl": PHASE_IMPL} | {f"Witness.{f.stem}": f.read_bytes() for f in files})
    RUNS.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="witness-", dir=RUNS) as tmp:
        parent = Path(tmp)
        toolchain = Toolchain.seed(parent)
        ctx = Context(parent / "ctx", "witness", toolchain)
        project, _ = ctx.project(batch)
        r = ctx.phase(project, ctx.library())
        out = r.out.decode("utf-8", "backslashreplace").splitlines()
        built = any(re.fullmatch(f"phase1 built {HEX}", line) for line in out)
        if r.rc != 0 or "accepted" not in out or not built:
            for line in out:
                print("phase\t" + line)
            print(r.err.decode("utf-8", "backslashreplace")[-3000:], file=sys.stderr)
            print(f"FAIL the corpus is refused or does not compile (exit {r.rc})")
            return 1
        targets = dev(["profile", "targets"])
        need(targets.returncode == 0, f"profile targets failed: {targets.stderr[-500:]!r}")
        paths = [str(project / module_path(m)) for m in batch if m != "Impl"]
        wit = dev(["profile", "witness", *paths])
        need(wit.returncode == 0, f"profile witness failed: {wit.stderr[-500:]!r}")
        covered = {line.split("\t", 1)[1] for line in wit.stdout.decode().splitlines()}
        want = targets.stdout.decode().splitlines()
        missing = [t for t in want if t not in covered]
        for t in missing:
            print("uncovered\t" + t)
        controls = sorted(CONTROLS.glob("*.lean"))
        off = [why for why in (control(parent, toolchain, f) for f in controls) if why is not None]
        for why in off:
            print("control\t" + why)
        print(f"RESULT {len(want)} targets; {len(want) - len(missing)} covered; {len(missing)} uncovered; "
              f"{len(files)} fixtures; {len(controls) - len(off)}/{len(controls)} controls as expected")
        return 1 if missing or off else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except AssertionError as exc:
        print(f"HARNESS {exc}", file=sys.stderr)
        sys.exit(2)
