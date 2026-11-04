"""fvdep prototype CLI.

Catalog + audit read the Lean spec library; `check` runs a differential test of an
implementation against the oracle compiled from the spec (or audits a Lean refinement
theorem); `lock`/`outdated`/`diff`/`upgrade` follow spec updates; `scan` maps a project's
dependencies to specs; `request` = STUB for the commercial order flow.
"""

from __future__ import annotations

import argparse
import datetime as dt
import difflib
import hashlib
import json
import os
import random
import re
import shlex
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn

HOME = Path(os.environ.get("FVDEP_HOME", Path(__file__).resolve().parents[3]))
LIB = HOME / "library"
CATALOG = LIB / "catalog"
STATE = HOME / ".state"
ORACLE = LIB / ".lake/build/bin/fvdep-oracle"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# ── catalog ──────────────────────────────────────────────────────────────


@dataclass
class Spec:
    dep: str
    version: str
    meta: dict
    path: Path

    @property
    def id(self) -> str:
        return f"{self.dep}@{self.version}"

    @property
    def source(self) -> Path:
        return LIB / self.meta["source"]

    @property
    def ops(self) -> list[str]:
        return [o["name"] for o in self.meta["ops"]]

    @property
    def obligations(self) -> list[dict]:
        return self.meta["obligations"]

    def sha256(self) -> str:
        h = hashlib.sha256(self.path.read_bytes())
        h.update(self.source.read_bytes())
        return h.hexdigest()


def vkey(v: str) -> tuple[int, ...]:
    return tuple(int(x) for x in v.split("."))


def catalog() -> dict[str, list[Spec]]:
    out: dict[str, list[Spec]] = {}
    for f in sorted(CATALOG.glob("*/*.toml")):
        m = tomllib.loads(f.read_text())
        out.setdefault(m["dep"], []).append(Spec(m["dep"], m["version"], m, f))
    for v in out.values():
        v.sort(key=lambda s: vkey(s.version))
    return out


def resolve(ref: str) -> Spec:
    dep, _, ver = ref.partition("@")
    specs = catalog().get(dep)
    if not specs:
        die(f"no spec for `{dep}`. To ask for one, run: fvdep request <ecosystem>:{dep}")
    if not ver:
        return specs[-1]
    for s in specs:
        if s.version == ver:
            return s
    die(f"`{dep}` has no spec version {ver}. Versions: {', '.join(s.version for s in specs)}")


def die(msg: str, rc: int = 2) -> NoReturn:
    print(f"fvdep: {msg}", file=sys.stderr)
    sys.exit(rc)


# ── lean: build + axiom audit ────────────────────────────────────────────


def lake(args: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["lake", *args], cwd=cwd, capture_output=True, text=True)


def ensure_built() -> None:
    """Incremental `lake build` every call (no-op ≈ 0.2 s) ⇒ the oracle never lags a spec edit."""
    if not ORACLE.exists():
        print("Building the spec library and oracle (first run, about 2 minutes)…", file=sys.stderr)
    r = lake(["build"], LIB)
    if r.returncode:
        die(f"lake build failed:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")


AX_RE = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def print_axioms(project: Path, imports: list[str], names: list[str]) -> dict[str, set[str]]:
    """`#print axioms` per declaration, after a build of `project` (axioms are the evidence)."""
    r = lake(["build"], project)
    if r.returncode:
        die(f"lake build failed in {project}:\n{r.stdout[-2000:]}")
    probe = project / ".lake/fvdep-audit.lean"
    probe.write_text("".join(f"import {i}\n" for i in imports) + "".join(f"#print axioms {n}\n" for n in names))
    r = lake(["env", "lean", str(probe)], project)
    found = {m[1]: {a.strip() for a in (m[2] or "").split(",") if a.strip()} for m in AX_RE.finditer(r.stdout)}
    missing = [n for n in names if n not in found]
    if missing:
        die(f"audit could not read axioms for {missing}:\n{r.stdout[-1500:]}{r.stderr[-1500:]}")
    return found


def status(axioms: set[str]) -> str:
    if "sorryAx" in axioms:
        return "open"
    extra = axioms - STD_AXIOMS
    return "proven" if not extra else "trusts " + ", ".join(sorted(extra))


def audit() -> dict[str, str]:
    """Obligation → status, cached on the hash of every spec source + manifest."""
    specs = [s for v in catalog().values() for s in v]
    key = hashlib.sha256("".join(s.sha256() for s in specs).encode()).hexdigest()
    cache = STATE / "audit.json"
    if cache.exists():
        c = json.loads(cache.read_text())
        if c.get("key") == key:
            return c["status"]
    ensure_built()
    names = [o["theorem"] for s in specs for o in s.obligations]
    ax = print_axioms(LIB, ["Fvdep"], names)
    st = {n: status(ax[n]) for n in names}
    STATE.mkdir(exist_ok=True)
    cache.write_text(json.dumps({"key": key, "status": st}, indent=1))
    return st


# ── differential check ───────────────────────────────────────────────────

B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
RFC4648 = ["", "66", "666f", "666f6f", "666f6f62", "666f6f6261", "666f6f626172"]


def gen_base64(rng: random.Random, n: int, ops: list[str]) -> list[list[str]]:
    import base64 as b

    cases: list[list[str]] = []
    for h in RFC4648:
        cases += [["encode", h], ["decode", b.b64encode(bytes.fromhex(h)).decode()]]
    for _ in range(n):
        raw = rng.randbytes(rng.choice([0, 1, 2, 3, 4, 5, rng.randrange(6, 48)]))
        cases.append(["encode", raw.hex()])
        s = list(b.b64encode(raw).decode())
        kind = rng.randrange(6)
        if s and kind == 1:  # substitute any char, incl. non-alphabet + url-safe chars
            s[rng.randrange(len(s))] = rng.choice(B64 + "=-_ .\t\x7f é")
        elif s and kind == 2:  # perturb the last data char ⇒ non-canonical trailing bits
            i = max(k for k, c in enumerate(s) if c != "=") if any(c != "=" for c in s) else 0
            s[i] = B64[(B64.index(s[i]) ^ rng.randrange(1, 4)) % 64] if s[i] in B64 else s[i]
        elif s and kind == 3:
            del s[rng.randrange(len(s))]
        elif kind == 4:
            s = [c for c in s if c != "="]
        text = "".join(s).replace("\t", " ")
        cases.append(["decode", text])
        if "encode_url" in ops:
            cases.append(["encode_url", raw.hex()])
            url = b.urlsafe_b64encode(raw).decode()
            if url and kind == 1:
                url = url[:-1] + rng.choice("+/=-_A")
            cases.append(["decode_url", url])
    return cases


def gen_semver(rng: random.Random, n: int, ops: list[str]) -> list[list[str]]:
    def num() -> str:
        return str(rng.choice([0, 0, 1, 1, 2, 10, rng.randrange(100000)]))

    def ident() -> str:
        return rng.choice(["alpha", "beta", "rc", "x-y", "0", "1", "11", "2", "a1", "-", num()])

    def version() -> str:
        s = f"{num()}.{num()}.{num()}"
        if rng.random() < 0.6:
            s += "-" + ".".join(ident() for _ in range(rng.randrange(1, 4)))
        if rng.random() < 0.3:
            s += "+" + ".".join(rng.choice(["build", "001", "sha-5114f85", "x"]) for _ in range(rng.randrange(1, 3)))
        return s

    def mutate(s: str) -> str:
        m = rng.randrange(7)
        if m == 0:
            return "v" + s
        if m == 1:
            return s.replace(".", ".0", 1)  # leading zero
        if m == 2:
            return s + rng.choice(["-", "+", ".", "..", "-.a"])
        if m == 3:
            return s.split(".", 1)[1]
        if m == 4:
            return s + "-01"
        if m == 5:
            return " " + s
        return s.replace("-", "-ä", 1)

    fixed = ["1.0.0", "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta", "1.0.0-beta.2",
             "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0+build", "01.0.0", "1.0", "1.0.0-", "1.0.0-01"]
    cases = [["parse", f] for f in fixed]
    cases += [["compare", a, b] for a, b in zip(fixed[:8], fixed[1:9])]
    for _ in range(n):
        a = version()
        b = a.split("-")[0] + "-" + ".".join(ident() for _ in range(rng.randrange(1, 4))) if rng.random() < 0.5 else version()
        cases.append(["parse", a if rng.random() < 0.6 else mutate(a)])
        cases.append(["compare", a, b])
    return cases


GENERATORS = {"base64": gen_base64, "semver": gen_semver}


def run_adapter(cmd: list[str], cases: list[list[str]], cwd: Path) -> list[str]:
    stdin = "".join("\t".join(c) + "\n" for c in cases)
    try:
        r = subprocess.run(cmd, input=stdin, capture_output=True, text=True, cwd=cwd, timeout=120)
    except FileNotFoundError:
        die(f"cannot run implementation: {shlex.join(cmd)}")
    out = r.stdout.splitlines()
    if len(out) != len(cases):
        die(f"implementation replied {len(out)} lines for {len(cases)} requests (rc {r.returncode}).\n{r.stderr[-1500:]}")
    return out


@dataclass
class Result:
    spec: Spec
    trust: str  # "tested" | "proven" | "failed"
    cases: int
    seed: int | None
    mismatches: list[tuple[list[str], str, str]]
    unsupported: list[str]
    note: str = ""

    @property
    def passed(self) -> bool:
        return self.trust != "failed"


def differential(spec: Spec, cmd: list[str], n: int, seed: int, cwd: Path) -> Result:
    ensure_built()
    cases = GENERATORS[spec.dep](random.Random(seed), n, spec.ops)
    want = run_adapter([str(ORACLE), spec.id], cases, cwd)
    got = run_adapter(cmd, cases, cwd)
    unsupported = sorted({c[0] for c, g in zip(cases, got) if g == "unsupported"})
    bad = [(c, w, g) for c, w, g in zip(cases, want, got) if w != g and g != "unsupported"]
    bad.sort(key=lambda t: sum(map(len, t[0])))  # shortest counterexample first
    ok = not bad and not unsupported
    return Result(spec, "tested" if ok else "failed", len(cases), seed, bad, unsupported)


def lean_conformance(spec: Spec, project: Path, module: str, theorem: str) -> Result:
    ax = print_axioms(project, [module], [theorem])[theorem]
    st = status(ax)
    note = (f"`{theorem}` axioms: {', '.join(sorted(ax)) or 'none'}\n"
            "      PROTOTYPE SHORTCUT: the theorem's statement is not yet matched against the spec's "
            "conformance shape; only its axioms are audited.")
    return Result(spec, "proven" if st == "proven" else "failed", 0, None, [], [], note)


def report(r: Result) -> None:
    if r.trust == "proven":
        print(f"PASS  {r.spec.id}  trust=proven (Lean refinement theorem, kernel-checked)\n      {r.note}")
        return
    if r.passed:
        print(f"PASS  {r.spec.id}  trust=tested ({r.cases} cases, seed {r.seed}, all replies equal the oracle)")
        return
    why = [f"{len(r.mismatches)} of {r.cases} replies differ from the spec oracle"] if r.mismatches else []
    why += [f"missing operations: {', '.join(r.unsupported)}"] if r.unsupported else []
    print(f"FAIL  {r.spec.id}  {'; '.join(why) or 'see note'}")
    if r.note:
        print(f"      {r.note}")
    for c, w, g in r.mismatches[:5]:
        print(f"      {' '.join(map(repr, c))}\n        spec: {w}\n        impl: {g}")
    if len(r.mismatches) > 5:
        print(f"      … {len(r.mismatches) - 5} more")


def do_check(spec: Spec, impl: str | None, lean: str | None, n: int, seed: int, cwd: Path) -> Result:
    if lean:
        proj, _, decl = lean.partition(":")
        module, _, _thm = decl.rpartition(".")
        return lean_conformance(spec, (cwd / proj).resolve(), module.split(".")[0], decl)
    return differential(spec, shlex.split(impl), n, seed, cwd)


# ── commands ─────────────────────────────────────────────────────────────


def cmd_list(a) -> None:
    st = audit()
    print(f"{'dependency':<10} {'latest':<7} {'proven':>6} {'open':>4}  models")
    for dep, specs in catalog().items():
        s = specs[-1]
        sts = [st[o["theorem"]] for o in s.obligations]
        print(f"{dep:<10} {s.version:<7} {sts.count('proven'):>6} {sts.count('open'):>4}  {', '.join(s.meta['models'])}")
        print(f"{'':<10} {s.meta['title']}")


def cmd_show(a) -> None:
    s = resolve(a.spec)
    st = audit()
    m = s.meta
    others = [x.version for x in catalog()[s.dep]]
    print(f"{s.id}  {m['title']}\n")
    print(f"  standard   {m['standard']}")
    print(f"  models     {', '.join(m['models'])}")
    print(f"  versions   {', '.join(others)}")
    print(f"  source     {s.source.relative_to(HOME)}  (module {m['module']})")
    print(f"  sha256     {s.sha256()[:16]}…\n")
    print(f"  {m['summary']}\n\n  operations (adapter protocol, see PROTOCOL.md)")
    for o in m["ops"]:
        print(f"    {o['name']:<11} {', '.join(o['args']):<22} → {o['result']}")
    print("\n  obligations (status read from `#print axioms` on the kernel-checked library)")
    for o in s.obligations:
        print(f"    [{st[o['theorem']]:<6}] {o['says']}\n             {o['theorem']}")


def cmd_check(a) -> None:
    s = resolve(a.spec)
    if not (a.impl or a.lean):
        die("give an implementation: `-- <command>` or `--lean <project>:<Module.theorem>`")
    r = do_check(s, shlex.join(a.impl) if a.impl else None, a.lean, a.cases, a.seed, Path.cwd())
    report(r)
    sys.exit(0 if r.passed else 1)


def load_project(d: Path) -> dict:
    f = d / "fvdep.toml"
    if not f.exists():
        die(f"no fvdep.toml in {d}")
    return tomllib.loads(f.read_text())


def write_lock(d: Path, entries: dict) -> None:
    lines = ["# fvdep.lock — written by `fvdep lock`; spec pins + conformance evidence.\n"]
    for dep, e in sorted(entries.items()):
        lines.append(f"\n[{dep}]\n")
        for k, v in e.items():
            lines.append(f"{k} = {json.dumps(v)}\n")
    (d / "fvdep.lock").write_text("".join(lines))


def read_lock(d: Path) -> dict:
    f = d / "fvdep.lock"
    if not f.exists():
        die(f"no fvdep.lock in {d}. Run `fvdep lock` first.")
    return tomllib.loads(f.read_text())


def lock_entry(r: Result, impl: str) -> dict:
    return {"spec": r.spec.version, "spec_sha256": r.spec.sha256(), "impl": impl, "trust": r.trust,
            "cases": r.cases, "seed": r.seed or 0, "checked": dt.date.today().isoformat()}


def cmd_lock(a) -> None:
    d = Path(a.project).resolve()
    proj = load_project(d)
    entries, failed = {}, False
    for dep, cfg in proj["deps"].items():
        s = resolve(f"{dep}@{cfg['spec']}")
        r = do_check(s, cfg.get("impl"), cfg.get("lean"), a.cases, a.seed, d)
        report(r)
        if r.passed:
            entries[dep] = lock_entry(r, cfg.get("impl") or cfg.get("lean"))
        failed |= not r.passed
    write_lock(d, entries)
    print(f"\nwrote {d / 'fvdep.lock'} ({len(entries)} of {len(proj['deps'])} dependencies locked)")
    sys.exit(1 if failed else 0)


def classify(old: Spec, new: Spec) -> str:
    if vkey(new.version)[0] != vkey(old.version)[0]:
        return "major (breaking: re-implement)"
    # Compat obligations are found by naming convention (`std_unchanged*`); their status is audited.
    compat = [o["theorem"] for o in new.obligations if ".std_unchanged" in o["theorem"]]
    if not compat:
        return "minor (additive; compatibility not stated)"
    st = audit()
    proven = all(st[t] == "proven" for t in compat)
    return f"minor (additive; old surface unchanged: {'proven' if proven else 'NOT proven'})"


def cmd_outdated(a) -> None:
    d = Path(a.project).resolve()
    lk = read_lock(d)
    cat = catalog()
    print(f"{'dependency':<10} {'locked':<7} {'latest':<7} change")
    for dep, e in lk.items():
        latest = cat[dep][-1]
        cur = resolve(f"{dep}@{e['spec']}")
        drift = "" if cur.sha256() == e["spec_sha256"] else "  ⚠ locked spec text changed since lock"
        if latest.version == e["spec"]:
            print(f"{dep:<10} {e['spec']:<7} {latest.version:<7} up to date{drift}")
            continue
        print(f"{dep:<10} {e['spec']:<7} {latest.version:<7} {classify(cur, latest)}{drift}")
        print(f"{'':<10} see: fvdep diff {dep} {e['spec']} {latest.version}")


def cmd_diff(a) -> None:
    old, new = resolve(f"{a.dep}@{a.old}"), resolve(f"{a.dep}@{a.new}")
    st = audit()
    print(f"{a.dep} {old.version} → {new.version}: {classify(old, new)}\n")
    for label, xs, ys in [("operations", old.ops, new.ops)]:
        for x in ys:
            if x not in xs:
                print(f"  + {label[:-1]:<10} {x}")
        for x in xs:
            if x not in ys:
                print(f"  - {label[:-1]:<10} {x}")
    short = lambda t: t.rsplit(".", 1)[1]  # noqa: E731
    on = {short(o["theorem"]) for o in old.obligations}
    for o in new.obligations:
        if short(o["theorem"]) not in on:
            print(f"  + obligation [{st[o['theorem']]}] {o['says']}")
    if a.source:
        print()
        sys.stdout.writelines(difflib.unified_diff(
            old.source.read_text().splitlines(True), new.source.read_text().splitlines(True),
            str(old.source.relative_to(HOME)), str(new.source.relative_to(HOME))))


def cmd_upgrade(a) -> None:
    d = Path(a.project).resolve()
    proj, lk = load_project(d), read_lock(d)
    cfg = proj["deps"].get(a.dep) or die(f"`{a.dep}` is not in fvdep.toml")
    target = resolve(f"{a.dep}@{a.to}" if a.to else a.dep)
    print(f"Checking {a.dep} implementation against {target.id} (locked: {lk.get(a.dep, {}).get('spec', '-')})")
    r = do_check(target, cfg.get("impl"), cfg.get("lean"), a.cases, a.seed, d)
    report(r)
    if not r.passed:
        print(f"\nNot upgraded: the lock stays at {lk.get(a.dep, {}).get('spec', '-')}. Fix the implementation, then rerun.")
        sys.exit(1)
    lk[a.dep] = lock_entry(r, cfg.get("impl") or cfg.get("lean"))
    write_lock(d, lk)
    toml = (d / "fvdep.toml").read_text()
    toml = re.sub(rf'(\[deps\.{re.escape(a.dep)}\]\nspec = )"[^"]*"', rf'\1"{target.version}"', toml)
    (d / "fvdep.toml").write_text(toml)
    print(f"\nUpgraded {a.dep} to {target.version} in fvdep.toml + fvdep.lock")


def manifest_deps(root: Path) -> list[tuple[str, str, str]]:
    """(ecosystem:name, version, manifest file) from the manifests fvdep reads."""
    out = []
    pj = root / "package.json"
    if pj.exists():
        j = json.loads(pj.read_text())
        for sec in ("dependencies", "devDependencies"):
            out += [(f"npm:{k}", v, "package.json") for k, v in (j.get(sec) or {}).items()]
    lm = root / "lake-manifest.json"
    if lm.exists():
        out += [(f"lake:{p['name']}", p.get("rev", "")[:8], "lake-manifest.json") for p in json.loads(lm.read_text())["packages"]]
    ct = root / "Cargo.toml"
    if ct.exists():
        out += [(f"crates:{k}", str(v if isinstance(v, str) else v.get("version", "")), "Cargo.toml")
                for k, v in tomllib.loads(ct.read_text()).get("dependencies", {}).items()]
    pp = root / "pyproject.toml"
    if pp.exists():
        for spec in tomllib.loads(pp.read_text()).get("project", {}).get("dependencies", []):
            name = re.split(r"[<>=!~;\[ ]", spec, maxsplit=1)[0]
            out.append((f"pypi:{name}", spec[len(name):], "pyproject.toml"))
    return out


def cmd_scan(a) -> None:
    root = Path(a.path).resolve()
    deps = manifest_deps(root)
    if not deps:
        die(f"no package.json, lake-manifest.json, Cargo.toml or pyproject.toml in {root}")
    models = {m: s for v in catalog().values() for s in v for m in s.meta["models"]}
    covered = 0
    print(f"{root}: {len(deps)} dependencies\n")
    for name, ver, src in deps:
        s = models.get(name)
        covered += bool(s)
        mark = f"spec {s.id}" if s else "no spec yet"
        print(f"  {name:<34} {ver:<12} {mark}")
    print(f"\n{covered} of {len(deps)} covered by a spec.")
    if covered < len(deps):
        print("To ask for a spec (and optionally an implementation): fvdep request <ecosystem:name> [--lang <language>]")


def cmd_request(a) -> None:
    STATE.mkdir(exist_ok=True)
    rec = {"package": a.package, "lang": a.lang, "at": dt.datetime.now().isoformat(timespec="seconds")}
    with open(STATE / "requests.jsonl", "a") as f:
        f.write(json.dumps(rec) + "\n")
    print(f"STUB: no order service exists yet. The request was saved to {STATE / 'requests.jsonl'}.")
    print(f"  package: {a.package}   implementation language: {a.lang or 'spec only'}")


def main() -> None:
    p = argparse.ArgumentParser(prog="fvdep", description="Formally specified dependencies (prototype).")
    sub = p.add_subparsers(dest="cmd", required=True)

    def checkopts(x):
        x.add_argument("--cases", type=int, default=500, help="random cases per run (default 500)")
        x.add_argument("--seed", type=int, default=1, help="generator seed (default 1)")

    sub.add_parser("list", help="list specs in the library").set_defaults(f=cmd_list)
    x = sub.add_parser("show", help="show one spec: operations + obligations")
    x.add_argument("spec", help="<dep>[@<version>]")
    x.set_defaults(f=cmd_show)
    x = sub.add_parser("check", help="check an implementation against a spec",
                       usage="fvdep check <dep>@<version> [--lean DIR:Module.theorem] [-- <adapter command>]")
    x.add_argument("spec", help="<dep>@<version>")
    x.add_argument("--lean", help="Lean implementation: <lake project dir>:<Module.theorem>")
    checkopts(x)
    x.set_defaults(f=cmd_check)
    x = sub.add_parser("lock", help="check every dependency in fvdep.toml and write fvdep.lock")
    x.add_argument("--project", default=".")
    checkopts(x)
    x.set_defaults(f=cmd_lock)
    x = sub.add_parser("outdated", help="compare fvdep.lock with the library")
    x.add_argument("--project", default=".")
    x.set_defaults(f=cmd_outdated)
    x = sub.add_parser("diff", help="what changed between two spec versions")
    x.add_argument("dep")
    x.add_argument("old")
    x.add_argument("new")
    x.add_argument("--source", action="store_true", help="also print the Lean source diff")
    x.set_defaults(f=cmd_diff)
    x = sub.add_parser("upgrade", help="re-check a dependency against a newer spec, then update the lock")
    x.add_argument("dep")
    x.add_argument("--to", help="spec version (default: latest)")
    x.add_argument("--project", default=".")
    checkopts(x)
    x.set_defaults(f=cmd_upgrade)
    x = sub.add_parser("scan", help="map a project's dependencies to specs")
    x.add_argument("path", nargs="?", default=".")
    x.set_defaults(f=cmd_scan)
    x = sub.add_parser("request", help="ask for a new spec or implementation (stub)")
    x.add_argument("package", help="<ecosystem>:<name>, e.g. npm:ajv")
    x.add_argument("--lang", help="implementation language wanted")
    x.set_defaults(f=cmd_request)

    argv = sys.argv[1:]
    cut = argv.index("--") if "--" in argv else len(argv)
    a = p.parse_args(argv[:cut])
    a.impl = argv[cut + 1 :]  # `check <spec> -- <adapter command>`
    a.f(a)


if __name__ == "__main__":
    main()
