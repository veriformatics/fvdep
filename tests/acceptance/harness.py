"""Black-box helpers; expectations come from the public contracts alone."""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = Path(__file__).resolve().parent / "fixtures"
SEED = 0xF4DE_2026
CASES: dict[str, "Case"] = {}


@dataclass(frozen=True)
class Case:
    id: str
    unit: str
    source: str
    predicate: str
    kind: str
    run: Callable[["Context"], None]


def case(id: str, unit: str, source: str, predicate: str, kind: str = "example"):
    def register(fn):
        assert id not in CASES, f"duplicate test id: {id}"
        assert kind in {"example", "property"}
        CASES[id] = Case(id, unit, source, predicate, kind, fn)
        return fn
    return register


@dataclass(frozen=True)
class Result:
    returncode: int
    stdout: str
    stderr: str

    @property
    def text(self) -> str:
        return self.stdout + "\n" + self.stderr

    def code(self, expected: int) -> "Result":
        assert self.returncode == expected, (
            f"exit {self.returncode}, expected {expected}\nstdout:\n{self.stdout}"
            f"\nstderr:\n{self.stderr}"
        )
        return self

    def contains(self, text: str) -> "Result":
        assert text in self.text, f"missing {text!r}\n{self.text}"
        return self

    def document(self) -> dict:
        def unique(pairs):
            out = {}
            for key, value in pairs:
                assert key not in out, f"duplicate JSON key: {key}"
                out[key] = value
            assert list(out) == sorted(out), f"JSON object keys not sorted: {list(out)}"
            return out
        try:
            value = json.loads(self.stdout, object_pairs_hook=unique)
        except ValueError as exc:
            raise AssertionError(f"stdout is not one JSON document: {self.stdout!r}") from exc
        assert isinstance(value, dict), f"JSON envelope must be an object: {value!r}"
        assert set(value) == {"schema", "command", "exit", "error", "result", "trusted", "status"}
        assert type(value["schema"]) is int and value["schema"] == 1
        assert type(value["exit"]) is int and value["exit"] == self.returncode
        assert isinstance(value["command"], str)
        assert isinstance(value["trusted"], list)
        assert all(isinstance(x, str) for x in value["trusted"])
        assert set(value["status"]) == {"commit", "fetched", "fetch_error"}
        assert all(x is None or isinstance(x, str) for x in value["status"].values())
        if self.returncode != 2:
            assert value["error"] is None, value["error"]
        else:
            assert set(value["error"]) == {"code", "detail"}
            assert isinstance(value["error"]["detail"], str)
        return value


def digest(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def saved(project: Path) -> dict[str, str | None]:
    return {name: digest(project / name) for name in ("fvdep.toml", "fvdep.lock")}


def unchanged(project: Path, before: dict[str, str | None]) -> None:
    assert saved(project) == before, f"project persistence changed: {before} -> {saved(project)}"


def raw_run(argv, *, cwd: Path, env: dict | None = None, data: str | None = None,
            timeout: float = 240) -> Result:
    try:
        proc = subprocess.run([str(x) for x in argv], cwd=cwd, env=env, input=data,
                              text=True, capture_output=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as exc:
        raise AssertionError(f"command exceeded test deadline {timeout}s: {argv!r}") from exc
    return Result(proc.returncode, proc.stdout, proc.stderr)


class Context:
    def __init__(self):
        self.binary = self._binary("FVDEP_BIN", ROOT / "tool/.lake/build/bin/fvdep")
        self.temp = tempfile.TemporaryDirectory(prefix="fvdep-acceptance-")
        self.base = Path(self.temp.name)
        self.env = dict(os.environ)
        self.env["FVDEP_CACHE"] = str(self.base / "cache")
        self.env["FVDEP_GROWTH_STATE"] = str(self.base / "growth")
        self._library: Path | None = None
        self._pin: str | None = None
        self._serial = 0

    @staticmethod
    def _binary(key: str, default: Path) -> Path:
        value = Path(os.environ.get(key, str(default))).expanduser().absolute()
        label = "fvdep" if key == "FVDEP_BIN" else "fvdep-grow"
        assert value.is_file() and os.access(value, os.X_OK), f"{label} binary not found: {value}"
        return value

    def close(self):
        self.temp.cleanup()

    def call(self, *args: str, cwd: Path | None = None, data: str | None = None,
             env: dict | None = None, timeout: float = 240) -> Result:
        return raw_run([self.binary, *args], cwd=cwd or self.base,
                       env=self.env | (env or {}), data=data, timeout=timeout)

    def grow(self, *args: str, env: dict | None = None) -> Result:
        binary = self._binary("FVDEP_GROW_BIN", ROOT / "tool/.lake/build/bin/fvdep-grow")
        return raw_run([binary, *args], cwd=self.base, env=self.env | (env or {}))

    def git(self, directory: Path, *args: str) -> str:
        return raw_run(["git", "-C", directory, *args], cwd=self.base,
                       env=self.env | {"GIT_AUTHOR_NAME": "fvdep acceptance",
                                       "GIT_AUTHOR_EMAIL": "acceptance@example.invalid",
                                       "GIT_COMMITTER_NAME": "fvdep acceptance",
                                       "GIT_COMMITTER_EMAIL": "acceptance@example.invalid"}).code(0).stdout.strip()

    def commit(self, directory: Path, message: str = "acceptance fixture") -> str:
        self.git(directory, "add", "--all")
        self.git(directory, "-c", "core.hooksPath=/dev/null", "commit", "--quiet", "--allow-empty", "-m", message)
        return self.git(directory, "rev-parse", "HEAD")

    def library(self) -> tuple[Path, str]:
        if self._library is not None:
            assert self._pin is not None
            return self._library, self._pin
        target = self.base / "library"
        source = os.environ.get("FVDEP_LIBRARY_URL")
        if source:
            raw_run(["git", "clone", "--quiet", "--no-hardlinks", "--", source, target],
                    cwd=self.base, env=self.env).code(0)
            self.git(target, "checkout", "--quiet", "-B", "main", "origin/main")
        else:
            target.mkdir()
            # Snapshot the working copy, not a consumer's vendored library. File contents
            # are only copied here; no implementation supplies an expected test value.
            names = raw_run(["git", "-C", ROOT, "ls-files", "-z", "--cached", "--others",
                             "--exclude-standard"], cwd=self.base).code(0).stdout.split("\0")
            for name in names:
                if not name or name.split("/", 1)[0] in {".scratch", ".git", "prototype", "tests", "tool"}:
                    continue
                src = ROOT / name
                if not src.exists() and not src.is_symlink():
                    continue
                dst = target / name
                dst.parent.mkdir(parents=True, exist_ok=True)
                if src.is_symlink():
                    dst.symlink_to(os.readlink(src))
                elif src.is_file():
                    shutil.copy2(src, dst)
            self.git(target, "init", "--quiet", "--initial-branch=main")
            self.commit(target)
        self._library = target
        self._pin = self.git(target, "rev-parse", "HEAD")
        self.env["FVDEP_LIBRARY_URL"] = str(target)
        return target, self._pin

    def manifest(self, entries: dict[str, dict], *, policy: str | None = "required",
                 directory: Path | None = None, pin: str | None = None) -> Path:
        _, default_pin = self.library()
        if directory is None:
            self._serial += 1
            directory = self.base / f"project-{self._serial}"
        directory.mkdir(parents=True, exist_ok=True)
        lines = ["schema = 1", "", "[library]", f'commit = "{pin or default_pin}"']
        if policy is not None:
            lines.extend(["", "[policy]", f'proof = "{policy}"'])
        for module, values in entries.items():
            lines.extend(["", f"[modules.{json.dumps(module)}]"])
            lines.extend(f"{key} = {json.dumps(value, ensure_ascii=False)}" for key, value in values.items())
        (directory / "fvdep.toml").write_text("\n".join(lines) + "\n")
        return directory

    def project(self, fixture: str = "honest-fn", *, policy: str = "required") -> Path:
        _, pin = self.library()
        self._serial += 1
        target = self.base / f"project-{self._serial}"
        shutil.copytree(FIXTURES / "consumers" / fixture, target)
        for template in target.rglob("*.lean.in"):
            template.rename(template.with_suffix(""))
        manifest = target / "fvdep.toml"
        text = manifest.read_text().replace("@LIBRARY_COMMIT@", pin).replace("@POLICY@", policy)
        manifest.write_text(text)
        for path in target.rglob("*.lean"):
            source = path.read_text()
            if "@OUTSIDE@" in source:
                path.write_text(source.replace("@OUTSIDE@", str(self.base / "outside-canary")))
        return target

    def differential(self, mode: str = "match", *, policy: str | None = "development") -> Path:
        project = self.manifest({"base64.encode": differential_entry(mode)}, policy=policy)
        shutil.copy2(FIXTURES / "adapter.py", project / "adapter.py")
        return project

    def oracle(self, target: str, requests: list[dict | str]) -> list[dict]:
        self.library()
        lines = [x if isinstance(x, str) else json.dumps(x, ensure_ascii=True) for x in requests]
        result = self.call("oracle", target, data="\n".join(lines) + "\n").code(0)
        replies = result.stdout.splitlines()
        assert len(replies) == len(lines), f"oracle sent {len(replies)} replies for {len(lines)} requests"
        out = []
        for reply in replies:
            value = json.loads(reply)
            assert isinstance(value, dict) and len(value) == 1, f"bad protocol reply: {value!r}"
            assert set(value) <= {"ok", "err", "unsupported", "invalid"}, value
            out.append(value)
        return out


def proof_entry(impl: str = "Impl.encode", proof: str = "Proof.encode_eq",
                *, version: str = "1.0.0", shape: str = "fn",
                impl_modules: list[str] | None = None, proof_modules: list[str] | None = None) -> dict:
    return {"version": version, "shape": shape, "impl_modules": impl_modules or ["Impl"],
            "proof_modules": proof_modules or ["Proof"], "impl": impl, "proof": proof}


def differential_entry(mode: str = "match") -> dict:
    return {"version": "1.0.0", "evidence": "differential",
            "adapter": ["python3", "-I", "adapter.py", mode]}


def checked_modules(result: Result, expected_exit: int | None = None) -> list[dict]:
    if expected_exit is not None:
        result.code(expected_exit)
    document = result.document()
    assert set(document["result"]) == {"modules", "wrote", "library"}
    if any(module["verdict"] == "proven" for module in document["result"]["modules"]):
        assert document["trusted"], "a proof claim omitted its trusted base"
    for module in document["result"]["modules"]:
        assert set(module) == {"module", "version", "impl", "evidence", "verdict", "policy_met",
                               "retracted", "reasons", "lock", "receipt"}, module
        assert module["verdict"] in {"proven", "not_proven", "matched", "mismatch"}
        assert isinstance(module["policy_met"], bool)
        assert all(set(r) == {"code", "detail"} for r in module["reasons"])
    return document["result"]["modules"]


def one_module(result: Result, expected_exit: int | None = None) -> dict:
    modules = checked_modules(result, expected_exit)
    assert len(modules) == 1, modules
    return modules[0]


def receipts(value):
    found = []
    if isinstance(value, dict):
        if {"digests", "request", "verification_profile", "checked"} <= set(value):
            found.append(value)
        else:
            for child in value.values():
                found.extend(receipts(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(receipts(child))
    return found


def rewrite_lock(project: Path, edit) -> None:
    path = project / "fvdep.lock"
    value = json.loads(path.read_text())
    edit(value)
    path.write_text(json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n")


def receipt_valid(receipt: dict, *, evidence: str) -> None:
    assert set(receipt) == {"checked", "digests", "evidence", "library", "policy", "request", "verification_profile"}
    assert receipt["evidence"] == evidence
    assert re.fullmatch(r"[0-9a-f]{40}", receipt["library"])
    assert receipt["policy"] in {"required", "development"}
    assert isinstance(receipt["checked"], str) and receipt["checked"]
    assert isinstance(receipt["verification_profile"], str) and receipt["verification_profile"]
    assert set(receipt["request"]) == {"adapter", "impl", "module", "proof", "shape", "version"}
    digests = receipt["digests"]
    assert set(digests) == {"adapter", "impl_sources", "phase1_export", "proof_sources", "solution_export", "spec_closure"}
    present = {"spec_closure", "adapter"} if evidence == "differential" else set(digests) - {"adapter"}
    for key, value in digests.items():
        assert (isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value)) if key in present else value is None, (key, value)
    assert "delivered" not in receipt
