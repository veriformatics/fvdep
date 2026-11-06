"""fvdep prototype CLI.

Library = contract modules (one per operation, versioned alone) + package profiles (where a real
package deviates from a contract). Delivery = a machine-checked proof: `check --lean` writes the
conformance statement itself and audits the axioms of its proof; a differential run against the
oracle compiled from the spec = development evidence, never a delivery. `lock`/`outdated`/`diff`/
`upgrade` follow module updates; `scan` maps a project's packages to profiles; `request` = STUB.
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
from dataclasses import dataclass, field
from pathlib import Path
from typing import NoReturn

HOME = Path(os.environ.get("FVDEP_HOME", Path(__file__).resolve().parents[3]))
LIB = HOME / "library"
STATE = Path(os.environ.get("FVDEP_STATE", HOME / ".state"))
ORACLE = LIB / ".lake/build/bin/fvdep-oracle"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# ── library: contract modules + package profiles ────────────────────────


def vkey(v: str) -> tuple[int, ...]:
    return tuple(int(x) for x in v.split("."))


@dataclass
class Entry:
    """A catalog file: contract module version or package profile version."""

    name: str  # `base64.decode` | `npm:base64-js`
    version: str
    meta: dict
    path: Path

    @property
    def id(self) -> str:
        return f"{self.name}@{self.version}"

    @property
    def source(self) -> Path:
        return LIB / self.meta["source"]

    def sha256(self) -> str:
        h = hashlib.sha256(self.path.read_bytes())
        h.update(self.source.read_bytes())
        return h.hexdigest()


def load(glob: str, key: str) -> dict[str, list[Entry]]:
    out: dict[str, list[Entry]] = {}
    for f in sorted(LIB.glob(glob)):
        m = tomllib.loads(f.read_text())
        out.setdefault(m[key], []).append(Entry(m[key], m["version"], m, f))
    for v in out.values():
        v.sort(key=lambda e: vkey(e.version))
    return out


def modules() -> dict[str, list[Entry]]:
    return load("catalog/*/*.toml", "module")


def profiles() -> dict[str, list[Entry]]:
    return load("profiles/*/*/*.toml", "package")


def pick(table: dict[str, list[Entry]], ref: str, kind: str, hint: str) -> Entry:
    name, _, ver = ref.rpartition("@") if "@" in ref else (ref, "", "")
    entries = table.get(name)
    if not entries:
        die(f"no {kind} `{name}`. {hint}")
    if not ver:
        return entries[-1]
    for e in entries:
        if e.version == ver:
            return e
    die(f"`{name}` has no version {ver}. Versions: {', '.join(e.version for e in entries)}")


def module(ref: str) -> Entry:
    return pick(modules(), ref, "spec module", "Run `fvdep list` to see the modules. To ask for one, run: fvdep request <ecosystem>:<package>")


def profile(ref: str) -> Entry:
    return pick(profiles(), ref, "package profile", "Run `fvdep list` to see the profiles.")


def die(msg: str, rc: int = 2) -> NoReturn:
    print(f"fvdep: {msg}", file=sys.stderr)
    sys.exit(rc)


def theorems(e: Entry) -> list[str]:
    """Every theorem a catalog entry cites (obligations, compat, profile relations + witnesses)."""
    m = e.meta
    out = [o["theorem"] for o in m.get("obligations", [])]
    out += [m["compat"]["theorem"]] if "compat" in m else []
    for op in m.get("ops", []):
        out += [r["theorem"] for r in op["relations"]] + [d["theorem"] for d in op["deviations"]]
    return out


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


def lean_run(project: Path, name: str, text: str) -> subprocess.CompletedProcess:
    probe = project / ".lake" / name
    probe.parent.mkdir(exist_ok=True)
    probe.write_text(text)
    return lake(["env", "lean", str(probe)], project)


def axioms_of(out: str) -> dict[str, set[str]]:
    return {m[1]: {a.strip() for a in (m[2] or "").split(",") if a.strip()} for m in AX_RE.finditer(out)}


def status(axioms: set[str]) -> str:
    if "sorryAx" in axioms:
        return "open"
    extra = axioms - STD_AXIOMS
    return "proven" if not extra else "trusts " + ", ".join(sorted(extra))


def audit() -> dict[str, str]:
    """Theorem → status for every theorem the library cites, cached on the hash of every entry."""
    entries = [e for t in (modules(), profiles()) for v in t.values() for e in v]
    key = hashlib.sha256("".join(e.sha256() for e in entries).encode()).hexdigest()
    cache = STATE / "audit.json"
    if cache.exists():
        c = json.loads(cache.read_text())
        if c.get("key") == key:
            return c["status"]
    ensure_built()
    # `#print axioms` trusts the environment the elaborator built; a metaprogram can add a theorem
    # the kernel never checked (`debug.skipKernelTC`). leanchecker replays every declaration first.
    rc = lake(["env", "leanchecker", "Fvdep"], LIB)
    if rc.returncode:
        die(f"the library failed the kernel replay (leanchecker):\n{rc.stdout[-1500:]}{rc.stderr[-1500:]}")
    names = sorted({t for e in entries for t in theorems(e)})
    r = lean_run(LIB, "fvdep-audit.lean", "import Fvdep\n" + "".join(f"#print axioms {n}\n" for n in names))
    ax = axioms_of(r.stdout)
    missing = [n for n in names if n not in ax]
    if missing:
        die(f"audit could not read axioms for {missing}:\n{r.stdout[-1500:]}{r.stderr[-1500:]}")
    st = {n: status(ax[n]) for n in names}
    STATE.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps({"key": key, "status": st}, indent=1))
    return st


def tally(e: Entry, st: dict[str, str]) -> tuple[int, int]:
    sts = [st[o["theorem"]] for o in e.meta["obligations"]]
    return sts.count("proven"), len(sts) - sts.count("proven")


# ── differential runs (development evidence) ─────────────────────────────

B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
RFC4648 = ["", "66", "666f", "666f6f", "666f6f62", "666f6f6261", "666f6f626172"]


def gen_base64(rng: random.Random, n: int) -> list[list[str]]:
    import base64 as b

    cases: list[list[str]] = []
    for h in RFC4648:
        raw = bytes.fromhex(h)
        cases += [["encode", h], ["decode", b.b64encode(raw).decode()],
                  ["encode_url", h], ["decode_url", b.urlsafe_b64encode(raw).decode()]]
    for _ in range(n):
        raw = rng.randbytes(rng.choice([0, 1, 2, 3, 4, 5, rng.randrange(6, 48)]))
        cases += [["encode", raw.hex()], ["encode_url", raw.hex()]]
        s = list(b.b64encode(raw).decode())
        kind = rng.randrange(7)
        if s and kind == 1:  # substitute any char, incl. non-alphabet + url-safe chars
            s[rng.randrange(len(s))] = rng.choice(B64 + "=-_ .!\t\x7f é")
        elif s and kind == 2:  # perturb the last data char ⇒ non-canonical trailing bits
            i = max(k for k, c in enumerate(s) if c != "=") if any(c != "=" for c in s) else 0
            s[i] = B64[(B64.index(s[i]) ^ rng.randrange(1, 4)) % 64] if s[i] in B64 else s[i]
        elif s and kind == 3:
            del s[rng.randrange(len(s))]
        elif kind == 4:
            s = [c for c in s if c != "="]
        elif kind == 5:  # data or padding after a padded group
            s += list(rng.choice([b.b64encode(rng.randbytes(rng.randrange(1, 4))).decode(), "===="]))
        text = "".join(s).replace("\t", " ")
        cases.append(["decode", text])
        url = b.urlsafe_b64encode(raw).decode()
        if url and kind == 1:
            url = url[:-1] + rng.choice("+/=-_A")
        cases.append(["decode_url", url])
    return cases


def gen_semver(rng: random.Random, n: int) -> list[list[str]]:
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


def gen_cases(contracts: list[str], ops: list[str], n: int, seed: int) -> list[list[str]]:
    """Cases for `ops`, from the generator of each contract module's family (`base64.decode` → base64)."""
    out: list[list[str]] = []
    for fam in dict.fromkeys(c.split(".")[0] for c in contracts):
        out += [c for c in GENERATORS[fam](random.Random(seed), n) if c[0] in ops]
    return out


def run_adapter(cmd: list[str], cases: list[list[str]], cwd: Path) -> list[str]:
    stdin = "".join("\t".join(c) + "\n" for c in cases)
    try:
        r = subprocess.run(cmd, input=stdin, capture_output=True, text=True, cwd=cwd, timeout=300)
    except FileNotFoundError:
        die(f"cannot run implementation: {shlex.join(cmd)}")
    out = r.stdout.splitlines()
    if len(out) != len(cases):
        die(f"`{shlex.join(cmd)}` replied {len(out)} lines for {len(cases)} requests (rc {r.returncode}).\n{r.stderr[-1500:]}")
    return out


@dataclass
class Diff:
    cases: int
    seed: int
    mismatches: list[tuple[list[str], str, str]]
    unsupported: list[str]

    @property
    def ok(self) -> bool:
        return not self.mismatches and not self.unsupported


def differential(handler: str, contracts: list[str], ops: list[str], cmd: list[str], n: int, seed: int, cwd: Path) -> Diff:
    ensure_built()
    cases = gen_cases(contracts, ops, n, seed)
    want = run_adapter([str(ORACLE), handler], cases, cwd)
    got = run_adapter(cmd, cases, cwd)
    unsupported = sorted({c[0] for c, g in zip(cases, got) if g == "unsupported"})
    bad = list({tuple(c): (c, w, g) for c, w, g in zip(cases, want, got) if w != g and g != "unsupported"}.values())
    bad.sort(key=lambda t: sum(map(len, t[0])))  # shortest counterexample first
    return Diff(len(cases), seed, bad, unsupported)  # mismatches = distinct cases


def print_mismatches(d: Diff, left: str, right: str) -> None:
    for c, w, g in d.mismatches[:5]:
        print(f"      {' '.join(map(repr, c))}\n        {left}: {w}\n        {right}: {g}")
    if len(d.mismatches) > 5:
        print(f"      … {len(d.mismatches) - 5} more")


# ── conformance: proof (delivery) or differential (development evidence) ─


@dataclass
class Result:
    spec: Entry
    verdict: str  # PROVEN | NOT PROVEN | MATCHED | MISMATCH
    detail: str
    evidence: str  # proof | differential
    diff: Diff | None = None
    lines: list[str] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return self.verdict in ("PROVEN", "MATCHED")

    @property
    def delivered(self) -> bool:
        return self.verdict == "PROVEN"


# `leanexport` names = the challenge decls + the kernel builtins `lake comparator` exports with them.
EXPORT_BUILTINS = ("Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub "
                   "Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor "
                   "Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String "
                   "String.mk Char optParam autoParam semiOutParam outParam").split()


def challenge_text(spec: Entry) -> str:
    fn = spec.meta["fn"]
    return (f"import {spec.meta['lean']}\ndef fvdep_impl : type_of% @{fn} := sorry\n"
            f"theorem fvdep_conformance : fvdep_impl = @{fn} := sorry\n")


def trusted_challenge(spec: Entry) -> Path:
    """Challenge built + exported against fvdep's own library, outside the implementation's project."""
    d = STATE / "challenges" / spec.id
    out = d / f"{spec.sha256()[:16]}.ndjson"
    if out.exists():
        return out
    ensure_built()
    d.mkdir(parents=True, exist_ok=True)
    (d / "lakefile.toml").write_text(f'name = "fvdepchallenge"\n[[require]]\nname = "fvdep"\npath = "{LIB}"\n'
                                     '[[lean_lib]]\nname = "FvdepChallenge"\n')
    (d / "lean-toolchain").write_text((LIB / "lean-toolchain").read_text())
    (d / "FvdepChallenge.lean").write_text(challenge_text(spec))
    r = lake(["build", "FvdepChallenge"], d)
    if r.returncode:
        die(f"challenge build failed:\n{r.stdout[-2000:]}{r.stderr[-1000:]}")
    names = ["fvdep_conformance", "fvdep_impl", *EXPORT_BUILTINS]
    ex = subprocess.run(["lake", "env", "leanexport", "FvdepChallenge", "--", *names],
                        cwd=d, capture_output=True, text=True)
    if ex.returncode:
        die(f"leanexport failed:\n{ex.stderr[-1500:]}")
    out.write_text(ex.stdout)
    return out


def comparator(spec: Entry, project: Path, mod: str, impl: str, tactic: str) -> tuple[int, str]:
    """`lake comparator` (bwrap sandbox) judges an fvdep-written solution module in a copy of the
    project against the trusted challenge export. The sandbox hides $HOME ⇒ the copy vendors the
    library (`fvdep-library/`, prebuilt oleans reused: a tampered constant fails the comparison)."""
    challenge = trusted_challenge(spec)
    work = STATE / "comparator" / hashlib.sha256(f"{project}|{spec.id}|{impl}".encode()).hexdigest()[:16]
    subprocess.run(["rm", "-rf", str(work)], check=True)
    work.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["rsync", "-a", "--exclude", ".lake", "--exclude", "lake-manifest.json",
                    f"{project}/", f"{work}/"], check=True)
    subprocess.run(["rsync", "-a", "--exclude", ".lake/fvdep-*", f"{LIB}/", f"{work}/fvdep-library/"], check=True)
    lf = work / "lakefile.toml"
    if not lf.exists():
        die(f"{project}: the prototype Lean check needs a lakefile.toml")
    text, n = re.subn(r'(name = "fvdep"\npath = )"[^"]*"', r'\1"fvdep-library"', lf.read_text())
    if not n:
        die(f"{project}/lakefile.toml must require the fvdep library by path")
    lf.write_text(text + '\n[[lean_lib]]\nname = "FvdepChallenge"\n\n[[lean_lib]]\nname = "FvdepSolution"\n')
    fn = spec.meta["fn"]
    (work / "FvdepChallenge.lean").write_text(challenge_text(spec))
    (work / "FvdepSolution.lean").write_text(
        f"import {spec.meta['lean']}\nimport {mod}\ndef fvdep_impl : type_of% @{fn} := @{impl}\n"
        f"theorem fvdep_conformance : fvdep_impl = @{fn} := by\n  show (@{impl}) = (@{fn})\n  {tactic}\n")
    (work / "comparator.json").write_text(json.dumps({
        "challenge_module": "FvdepChallenge", "solution_module": "FvdepSolution",
        "theorem_names": ["fvdep_conformance"], "definition_names": ["fvdep_impl"],
        "permitted_axioms": sorted(STD_AXIOMS)}))
    u = lake(["update"], work)  # writes lake-manifest.json; lakefile.toml = declarative, no code runs
    if u.returncode:
        die(f"lake update failed in {work}:\n{u.stderr[-1500:]}")
    r = lake(["comparator", "--challenge-from-export", str(challenge)], work)
    if r.returncode == 2:
        die(f"lake comparator could not start:\n{r.stdout[-1500:]}{r.stderr[-1500:]}")
    lines = (r.stdout + r.stderr).splitlines()
    why = [ln for ln in lines if "rejected" in ln or "does not match" in ln or "not found" in ln or "axiom" in ln]
    return r.returncode, (why or [ln for ln in lines if ln.startswith("error")] or lines[-1:] or ["no output"])[0]


def lean_conformance(spec: Entry, project: Path, mod: str, impl: str, proof: str) -> Result:
    """fvdep writes the statement `impl = <spec fn>`; the named proof has to close it. A local probe
    gives readable errors; `lake comparator` against a trusted challenge decides."""
    r = lake(["build"], project)
    if r.returncode:
        die(f"lake build failed in {project}:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    fn = spec.meta["fn"]
    compat = spec.meta.get("compat", {}).get("theorem")
    close = f"first | exact {proof} | (funext; exact {proof} ..)"
    tactic = f"first | ({close})" + (f" | (rw [{compat}]; {close})" if compat else "")
    stmt = f"(@{impl}) = (@{fn})"
    text = (f"import {spec.meta['lean']}\nimport {mod}\n"
            f"theorem fvdep_conformance : {stmt} := by\n  {tactic}\n"
            "#print axioms fvdep_conformance\n")
    out = lean_run(project, "fvdep-conformance.lean", text)
    ax = axioms_of(out.stdout).get("fvdep_conformance")
    if out.returncode or ax is None:
        err = next((ln for ln in out.stdout.splitlines() if "error" in ln), out.stdout.strip()[:300])
        return Result(spec, "NOT PROVEN", f"`{proof}` does not prove {impl} = {fn}", "proof",
                      lines=[f"statement written by fvdep: {stmt}", f"Lean: {err.split(': ', 2)[-1]}"])
    s = status(ax)
    if s != "proven":
        return Result(spec, "NOT PROVEN", f"the proof of {impl} = {fn} is {s}", "proof",
                      lines=[f"axioms: {', '.join(sorted(ax))}"])
    rc, msg = comparator(spec, project, mod, impl, tactic)
    if rc:
        return Result(spec, "NOT PROVEN", "lake comparator rejected the proof against the trusted spec",
                      "proof", lines=[f"comparator: {msg}"])
    return Result(spec, "PROVEN", f"{impl} = {fn} (kernel-checked)", "proof",
                  lines=["statement written by fvdep; judged by lake comparator against the trusted library",
                         f"axioms: {', '.join(sorted(ax)) or 'none'}"])


def run_check(spec: Entry, cfg: dict, n: int, seed: int, cwd: Path) -> Result:
    if "lean" in cfg:
        lc = cfg["lean"]
        return lean_conformance(spec, (cwd / lc["project"]).resolve(), lc["module"], lc["impl"], lc["proof"])
    d = differential(spec.id, [spec.name], [spec.meta["op"]], shlex.split(cfg["impl"]), n, seed, cwd)
    if d.ok:
        return Result(spec, "MATCHED", f"{d.cases} cases agree with the spec oracle (seed {d.seed})", "differential", d)
    why = [f"{len(d.mismatches)} of {d.cases} replies differ from the spec oracle"] if d.mismatches else []
    why += [f"operation not implemented: {', '.join(d.unsupported)}"] if d.unsupported else []
    return Result(spec, "MISMATCH", "; ".join(why), "differential", d)


def report(r: Result) -> None:
    proven, open_ = tally(r.spec, audit())
    print(f"{r.verdict:<10} {r.spec.id}  {r.detail}")
    for ln in r.lines:
        print(f"           {ln}")
    if r.diff and r.diff.mismatches:
        print_mismatches(r.diff, "spec", "impl")
    if r.delivered:
        print("           delivered: yes (machine-checked proof against the spec)")
    elif r.passed:
        print("           delivered: no (development evidence only; delivery needs a proof)")
    print(f"           spec obligations: {proven} proven, {open_} open")


def impl_ref(cfg: dict) -> str:
    if "lean" in cfg:
        lc = cfg["lean"]
        return f"lean {lc['project']}:{lc['module']} {lc['impl']} by {lc['proof']}"
    return cfg["impl"]


# ── commands ─────────────────────────────────────────────────────────────


def cmd_list(a) -> None:
    st = audit()
    print(f"{'module':<18} {'latest':<7} {'proven':>6} {'open':>4}  title")
    for name, entries in modules().items():
        e = entries[-1]
        p, o = tally(e, st)
        print(f"{name:<18} {e.version:<7} {p:>6} {o:>4}  {e.meta['title']}")
    print(f"\n{'package profile':<26} {'deviations':<11} {'list':<9} modules")
    for name, entries in profiles().items():
        e = entries[-1]
        devs = sum(len(op["deviations"]) for op in e.meta["ops"])
        done = "complete" if all(complete(op, st) for op in e.meta["ops"]) else "partial"
        print(f"{e.id:<26} {devs:<11} {done:<9} {', '.join(op['contract'] for op in e.meta['ops'])}")


def complete(op: dict, st: dict[str, str]) -> bool:
    """A proven relation marked `complete` = the deviation list of this op is exhaustive."""
    return any(r.get("complete") and st[r["theorem"]] == "proven" for r in op["relations"])


def cmd_show(a) -> None:
    e = module(a.module)
    st = audit()
    m = e.meta
    print(f"{e.id}  {m['title']}\n")
    print(f"  standard   {m['standard']}")
    print(f"  versions   {', '.join(x.version for x in modules()[e.name])}")
    print(f"  uses       {', '.join(m['uses']) or '-'}")
    print(f"  source     {e.source.relative_to(HOME)}")
    print(f"  implement  {m['fn']}")
    print(f"  sha256     {e.sha256()[:16]}…\n")
    print(f"  {m['summary']}\n")
    print(f"  adapter operation (see PROTOCOL.md): {m['op']} {', '.join(m['args'])} → {m['result']}")
    if "compat" in m:
        c = m["compat"]
        print(f"\n  compatibility with {c['from']}\n    [{st[c['theorem']]:<6}] {c['says']}\n             {c['theorem']}")
    print("\n  obligations (status = `#print axioms` after a leanchecker kernel replay of the library)")
    for o in m["obligations"]:
        print(f"    [{st[o['theorem']]:<6}] {o['says']}\n             {o['theorem']}")


def setup_package(e: Entry) -> None:
    if "setup" in e.meta:
        r = subprocess.run(shlex.split(e.meta["setup"]), cwd=HOME, capture_output=True, text=True)
        if r.returncode:
            die(f"setup failed: {e.meta['setup']}\n{r.stderr[-1500:]}")


def cmd_profile(a) -> None:
    e = profile(a.package)
    st = audit()
    m = e.meta
    print(f"{e.id}  {m['title']}\n")
    print(f"  measured   {m['measured']}")
    print(f"  model      {e.source.relative_to(HOME)}")
    print(f"  adapter    {m['adapter']}")
    for op in m["ops"]:
        print(f"\n  {op['op']}  {op['api']}  vs contract {op['contract']}")
        for r in op["relations"]:
            print(f"    [{st[r['theorem']]:<6}] {r['says']}")
        if not complete(op, st):
            print("    completeness: not proven, so deviations beyond the list below may exist")
        if not op["deviations"]:
            print("    deviations: none")
        for d in op["deviations"]:
            print(f"    deviation [{st[d['theorem']]:<6}] {d['name']}  e.g. {d['witness']!r}\n      {d['says']}")
    if not a.check:
        print(f"\n  The theorems are about the model. To compare the model with the real package, run:\n"
              f"  fvdep profile {e.id} --check")
        return
    setup_package(e)
    ops = [op["op"] for op in m["ops"]]
    d = differential(e.id, [op["contract"] for op in m["ops"]], ops, shlex.split(m["adapter"]), a.cases, a.seed, HOME)
    print()
    if d.ok:
        print(f"MODEL MATCHES  {e.id}: the real package and its model agree on {d.cases} cases (seed {d.seed}).")
        print("  This is evidence that the model is faithful, not a proof about the package.")
        return
    print(f"MODEL DIFFERS  {e.id}: {len(d.mismatches)} of {d.cases} cases differ"
          + (f"; package lacks {', '.join(d.unsupported)}" if d.unsupported else ""))
    print_mismatches(d, "model", "package")
    sys.exit(1)


def check_cfg(a) -> dict:
    if a.lean:
        proj, _, mod = a.lean.partition(":")
        if not (mod and a.impl_fn and a.proof):
            die("a Lean check needs --lean <project dir>:<Module> --impl <function> --proof <theorem>")
        return {"lean": {"project": proj, "module": mod, "impl": a.impl_fn, "proof": a.proof}}
    if a.impl:
        return {"impl": shlex.join(a.impl)}
    die("give an implementation: `-- <adapter command>` or `--lean <dir>:<Module> --impl <fn> --proof <theorem>`")


def cmd_check(a) -> None:
    r = run_check(module(a.module), check_cfg(a), a.cases, a.seed, Path.cwd())
    report(r)
    sys.exit(0 if r.passed else 1)


def load_project(d: Path) -> dict:
    f = d / "fvdep.toml"
    if not f.exists():
        die(f"no fvdep.toml in {d}")
    return tomllib.loads(f.read_text())


def write_lock(d: Path, entries: dict) -> None:
    lines = ["# fvdep.lock — written by `fvdep lock`; module pins + conformance evidence.\n"]
    for name, e in sorted(entries.items()):
        lines.append(f'\n["{name}"]\n')
        for k, v in e.items():
            lines.append(f"{k} = {json.dumps(v)}\n")
    (d / "fvdep.lock").write_text("".join(lines))


def read_lock(d: Path) -> dict:
    f = d / "fvdep.lock"
    if not f.exists():
        die(f"no fvdep.lock in {d}. Run `fvdep lock` first.")
    return tomllib.loads(f.read_text())


def lock_entry(r: Result, cfg: dict) -> dict:
    e = {"spec": r.spec.version, "spec_sha256": r.spec.sha256(), "impl": impl_ref(cfg),
         "evidence": r.evidence, "delivered": r.delivered, "checked": dt.date.today().isoformat()}
    if r.diff:
        e |= {"cases": r.diff.cases, "seed": r.diff.seed}
    return e


def cmd_lock(a) -> None:
    d = Path(a.project).resolve()
    mods = load_project(d)["modules"]
    entries, failed = {}, False
    for name, cfg in mods.items():
        r = run_check(module(f"{name}@{cfg['spec']}"), cfg, a.cases, a.seed, d)
        report(r)
        if r.passed:
            entries[name] = lock_entry(r, cfg)
        failed |= not r.passed
    write_lock(d, entries)
    delivered = sum(e["delivered"] for e in entries.values())
    print(f"\nwrote {d / 'fvdep.lock'}: {len(entries)} of {len(mods)} modules locked, "
          f"{delivered} delivered (proven), {len(entries) - delivered} with development evidence only")
    if a.require_proof and delivered < len(mods):
        print("--require-proof: every module needs a proof. Not delivered: "
              + ", ".join(n for n in mods if not entries.get(n, {}).get("delivered")))
        sys.exit(1)
    sys.exit(1 if failed else 0)


def classify(old: Entry, new: Entry, evidence: str | None = None) -> str:
    if vkey(new.version)[0] != vkey(old.version)[0]:
        return "major: behaviour may change; re-implement and re-prove"
    c = new.meta.get("compat")
    if not c or c["from"] != old.version:
        return "minor: compatibility with your version is not stated"
    if audit()[c["theorem"]] != "proven":
        return "same behaviour claimed but NOT proven"
    then = {"proof": "your proof carries over", "differential": "rerun the differential check"}.get(
        evidence, f"proofs against {old.version} carry over")
    return f"same behaviour (proven); {then}"


def cmd_outdated(a) -> None:
    d = Path(a.project).resolve()
    lk = read_lock(d)
    mods = modules()
    print(f"{'module':<18} {'locked':<7} {'latest':<7} change")
    for name, e in lk.items():
        latest = mods[name][-1]
        cur = module(f"{name}@{e['spec']}")
        drift = "" if cur.sha256() == e["spec_sha256"] else "  ⚠ locked spec text changed since lock"
        if latest.version == e["spec"]:
            print(f"{name:<18} {e['spec']:<7} {latest.version:<7} up to date{drift}")
            continue
        print(f"{name:<18} {e['spec']:<7} {latest.version:<7} {classify(cur, latest, e['evidence'])}{drift}")
        print(f"{'':<18} see: fvdep diff {name} {e['spec']} {latest.version}")


def cmd_diff(a) -> None:
    old, new = module(f"{a.module}@{a.old}"), module(f"{a.module}@{a.new}")
    st = audit()
    print(f"{a.module} {old.version} → {new.version}: {classify(old, new)}\n")
    for u in new.meta["uses"]:
        if u not in old.meta["uses"]:
            print(f"  + uses       {u}")
    for u in old.meta["uses"]:
        if u not in new.meta["uses"]:
            print(f"  - uses       {u}")
    short = lambda t: t.rsplit(".", 1)[1]  # noqa: E731
    on = {short(o["theorem"]) for o in old.meta["obligations"]}
    nn = {short(o["theorem"]) for o in new.meta["obligations"]}
    for o in new.meta["obligations"]:
        if short(o["theorem"]) not in on:
            print(f"  + obligation [{st[o['theorem']]}] {o['says']}")
    for o in old.meta["obligations"]:
        if short(o["theorem"]) not in nn:
            print(f"  - obligation {o['says']}")
    if a.source:
        print()
        sys.stdout.writelines(difflib.unified_diff(
            old.source.read_text().splitlines(True), new.source.read_text().splitlines(True),
            str(old.source.relative_to(HOME)), str(new.source.relative_to(HOME))))


def cmd_upgrade(a) -> None:
    d = Path(a.project).resolve()
    mods, lk = load_project(d)["modules"], read_lock(d)
    cfg = mods.get(a.module) or die(f"`{a.module}` is not in fvdep.toml")
    target = module(f"{a.module}@{a.to}" if a.to else a.module)
    locked = lk.get(a.module, {}).get("spec", "-")
    print(f"Checking the {a.module} implementation against {target.id} (locked: {locked})")
    r = run_check(target, cfg, a.cases, a.seed, d)
    report(r)
    if not r.passed:
        print(f"\nNot upgraded: the lock stays at {locked}. Fix the implementation, then run the upgrade again.")
        sys.exit(1)
    lk[a.module] = lock_entry(r, cfg)
    write_lock(d, lk)
    toml = (d / "fvdep.toml").read_text()
    toml = re.sub(rf'(\[modules\."{re.escape(a.module)}"\]\nspec = )"[^"]*"', rf'\1"{target.version}"', toml)
    (d / "fvdep.toml").write_text(toml)
    print(f"\nUpgraded {a.module} to {target.version} in fvdep.toml and fvdep.lock")


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
    profs = profiles()
    st = audit()
    found = 0
    print(f"{root}: {len(deps)} dependencies\n")
    for name, ver, _src in deps:
        entries = profs.get(name)
        if not entries:
            print(f"  {name:<24} {ver:<10} no profile yet: how it differs from a contract is unknown")
            continue
        found += 1
        e = next((x for x in entries if x.version == ver.lstrip("^~=")), entries[-1])
        same = "" if e.version == ver.lstrip("^~=") else f" (measured on {e.version}, yours is {ver})"
        print(f"  {name:<24} {ver:<10} profile {e.id}{same}")
        for op in e.meta["ops"]:
            n = len(op["deviations"])
            what = f"{n} deviations" if n else "no deviations"
            what += "" if complete(op, st) else " listed; list not proven complete"
            names = f": {', '.join(d['name'] for d in op['deviations'])}" if n else ""
            print(f"  {'':<35} {op['contract']:<22} {what}{names}")
    print(f"\n{found} of {len(deps)} have a package profile. For details, run: fvdep profile <package>")
    print("A profile describes the package. To use a contract instead, implement its modules and prove them.")
    if found < len(deps):
        print("To ask for a profile, a spec or an implementation: fvdep request <ecosystem:name> [--lang <language>]")


def cmd_request(a) -> None:
    STATE.mkdir(parents=True, exist_ok=True)
    rec = {"package": a.package, "lang": a.lang, "at": dt.datetime.now().isoformat(timespec="seconds")}
    with open(STATE / "requests.jsonl", "a") as f:
        f.write(json.dumps(rec) + "\n")
    print(f"STUB: no order service exists yet. The request was saved to {STATE / 'requests.jsonl'}.")
    print(f"  package: {a.package}   implementation language: {a.lang or 'spec only'}")


def main() -> None:
    p = argparse.ArgumentParser(prog="fvdep", description="Formally specified dependencies (prototype).")
    sub = p.add_subparsers(dest="cmd", required=True)

    def checkopts(x):
        x.add_argument("--cases", type=int, default=500, help="random cases per differential run (default 500)")
        x.add_argument("--seed", type=int, default=1, help="generator seed (default 1)")

    sub.add_parser("list", help="list spec modules and package profiles").set_defaults(f=cmd_list)
    x = sub.add_parser("show", help="show one spec module: operation + obligations")
    x.add_argument("module", help="<module>[@<version>], e.g. base64.decode")
    x.set_defaults(f=cmd_show)
    x = sub.add_parser("profile", help="show how a real package deviates from the contract")
    x.add_argument("package", help="<ecosystem>:<name>[@<version>], e.g. npm:base64-js")
    x.add_argument("--check", action="store_true", help="compare the profile's model with the real package")
    checkopts(x)
    x.set_defaults(f=cmd_profile)
    x = sub.add_parser("check", help="check an implementation against a spec module",
                       usage="fvdep check <module>@<version> (--lean DIR:Module --impl FN --proof THM | -- <adapter command>)")
    x.add_argument("module", help="<module>@<version>")
    x.add_argument("--lean", help="Lean implementation: <lake project dir>:<Module>")
    x.add_argument("--impl", dest="impl_fn", help="Lean function that implements the module")
    x.add_argument("--proof", help="Lean theorem that proves the function equal to the spec")
    checkopts(x)
    x.set_defaults(f=cmd_check)
    x = sub.add_parser("lock", help="check every module in fvdep.toml and write fvdep.lock")
    x.add_argument("--project", default=".")
    x.add_argument("--require-proof", action="store_true", help="fail unless every module is delivered (proven)")
    checkopts(x)
    x.set_defaults(f=cmd_lock)
    x = sub.add_parser("outdated", help="compare fvdep.lock with the library")
    x.add_argument("--project", default=".")
    x.set_defaults(f=cmd_outdated)
    x = sub.add_parser("diff", help="what changed between two versions of a module")
    x.add_argument("module")
    x.add_argument("old")
    x.add_argument("new")
    x.add_argument("--source", action="store_true", help="also print the Lean source diff")
    x.set_defaults(f=cmd_diff)
    x = sub.add_parser("upgrade", help="check a module's implementation against a newer version, then update the lock")
    x.add_argument("module")
    x.add_argument("--to", help="module version (default: latest)")
    x.add_argument("--project", default=".")
    checkopts(x)
    x.set_defaults(f=cmd_upgrade)
    x = sub.add_parser("scan", help="map a project's packages to package profiles")
    x.add_argument("path", nargs="?", default=".")
    x.set_defaults(f=cmd_scan)
    x = sub.add_parser("request", help="ask for a new profile, spec or implementation (stub)")
    x.add_argument("package", help="<ecosystem>:<name>, e.g. npm:ajv")
    x.add_argument("--lang", help="implementation language wanted")
    x.set_defaults(f=cmd_request)

    argv = sys.argv[1:]
    cut = argv.index("--") if "--" in argv else len(argv)
    a = p.parse_args(argv[:cut])
    a.impl = argv[cut + 1 :]  # `check <module> -- <adapter command>`
    a.f(a)


if __name__ == "__main__":
    main()
