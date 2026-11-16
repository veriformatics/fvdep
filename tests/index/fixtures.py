"""Source-generated U4 fixture libraries + Git histories. No tool implementation imports."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
from typing import Any

S = "Fvdep.Base64.Encode.V1_0_0"
E = "Fvdep.Registry.Base64.Encode.V1_0_0"
P = "FvdepProofs.Registry.Base64.Encode.V1_0_0"
R = "Fvdep.Registry.Types.V1"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
LAUNCH = ["base64.decode", "base64.decode_url", "base64.encode", "base64.encode_url",
          "semver.compare", "semver.parse"]
OBLIGATIONS = {
    "base64.encode": ["bits", "length"], "base64.encode_url": ["bits", "length"],
    "base64.decode": ["inverse", "canonical"], "base64.decode_url": ["inverse", "canonical"],
    "semver.parse": ["onlyValid", "canonical", "complete"],
    "semver.compare": ["swap", "trans", "eqIff", "precedence"],
}


def canonical(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).replace(
        "\x7f", "\\u007f").encode("utf-8")


def write(root: Path, module: str, source: str) -> Path:
    path = root / (module.replace(".", "/") + ".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    return path


def quoted(text: str) -> str:
    # Control characters stay explicit in fixture source.
    chunks = []
    for char in text:
        if char in ('"', "\\"):
            chunks.append("\\" + char)
        elif char == "\n":
            chunks.append("\\n")
        elif char == "\r":
            chunks.append("\\r")
        elif char == "\t":
            chunks.append("\\t")
        elif ord(char) < 32 or ord(char) == 127:
            chunks.append("\\u" + format(ord(char), "04x"))
        else:
            chunks.append(char)
    return '"' + "".join(chunks) + '"'


class Library:
    def __init__(self, root: Path, repo: Path, launch: bool = False):
        self.root = root
        self.repo = repo
        root.mkdir(parents=True)
        if launch:
            for item in ("Fvdep", "FvdepPreview", "FvdepProofs"):
                if (repo / item).is_dir():
                    shutil.copytree(repo / item, root / item)
            for item in ("Fvdep.lean", "FvdepPreview.lean", "FvdepProofs.lean", "lakefile.lean",
                         "lean-toolchain"):
                shutil.copy2(repo / item, root / item)
        else:
            (root / "lean-toolchain").write_text(TOOLCHAIN + "\n")
            (root / "lakefile.lean").write_text((repo / "lakefile.lean").read_text())
            for module in (R, "Fvdep.Registry.ProfileTypes.V1", "Fvdep.Abi.V1_0_0"):
                relative = module.replace(".", "/") + ".lean"
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(repo / relative, path)
            self.spec()
            self.entry()
            self.proofs()
            self.registry([E])
            self.notices([])
            self.removed([])
            (root / "Fvdep.lean").write_text(
                "import Fvdep.Registry\nimport Fvdep.Registry.Notices\nimport Fvdep.Registry.Removed\n")
            (root / "FvdepProofs.lean").write_text(f"import {P}\n")
            (root / "FvdepPreview.lean").write_text("/-! Empty fixture preview library. -/\n")

    def spec(self, source: str | None = None, module: str = S) -> None:
        if source is None:
            source = f'''namespace {module}
def encode (_ : List UInt8) : List Char := []
def bits : Prop := True
def length : Prop := True
end {module}
'''
        write(self.root, module, source)

    def entry(self, *, module: str = E, spec: str = S + ".encode", id: str = "base64.encode",
              version: str = "1.0.0", obligations: list[str] | None = None,
              abi: str | None = None, compat: str | None = None,
              imports: list[str] | None = None) -> None:
        if obligations is None:
            obligations = [S + ".bits", S + ".length"]
        refs = ", ".join("``" + item for item in obligations)
        imported = imports if imports is not None else [spec.rsplit(".", 1)[0], R]
        if abi is not None and abi.startswith("Fvdep.Abi."):
            imported = [*imported, abi.rsplit(".", 1)[0]]
        text = "".join(f"import {name}\n" for name in dict.fromkeys(imported))
        text += f'''namespace {module}
def entry : {R}.Module := {{
  id := {quoted(id)}
  version := {quoted(version)}
  spec := ``{spec}
  obligations := [{refs}]
  abi := {('some ``' + abi) if abi else 'none'}
  compat := {('some ' + quoted(compat)) if compat is not None else 'none'}
}}
end {module}
'''
        write(self.root, module, text)

    def proofs(self, *, source: str | None = None, module: str = P,
               entry: str = E, spec: str = S) -> None:
        if source is None:
            source = f'''import {entry}
namespace {module}
theorem bits : {spec}.bits := True.intro
theorem length : {spec}.length := True.intro
def proofs : {R}.Proofs := {{
  obligations := [(``{spec}.bits, ``{module}.bits), (``{spec}.length, ``{module}.length)]
  compat := none
}}
end {module}
'''
        write(self.root, module, source)

    def registry(self, entries: list[str], *, expression: str | None = None,
                 profiles: str = "[]", prefix: str = "") -> None:
        imports = "".join(f"import {name}\n" for name in dict.fromkeys(entries))
        imports += f"import {R}\nimport Fvdep.Registry.ProfileTypes.V1\n"
        value = expression if expression is not None else "[" + ", ".join(
            name + ".entry" for name in entries) + "]"
        write(self.root, "Fvdep.Registry", imports + f'''namespace Fvdep.Registry
{prefix}
def modules : List {R}.Module := {value}
def profiles : List Fvdep.Registry.ProfileTypes.V1.Profile := {profiles}
end Fvdep.Registry
''')

    def notices(self, items: list[dict[str, Any]], expression: str | None = None) -> None:
        values = []
        for item in items:
            replacement = item.get("replacement")
            values.append("{ id := " + quoted(item["id"]) + ", version := " + quoted(
                item["version"]) + ", reason := " + quoted(item["reason"]) +
                ", replacement := " + ("none" if replacement is None else
                                        "some " + quoted(replacement)) + " }")
        value = expression if expression is not None else "[" + ", ".join(values) + "]"
        write(self.root, "Fvdep.Registry.Notices", f'''import {R}
namespace Fvdep.Registry
def notices : List {R}.Notice := {value}
end Fvdep.Registry
''')

    def removed(self, items: list[dict[str, Any]], expression: str | None = None) -> None:
        values = []
        for item in items:
            fields = [key + " := " + quoted(item[key]) for key in
                      ("id", "version", "digest", "toolchain", "lastCommit")]
            values.append("{ " + ", ".join(fields) + ", kind := ." + item.get(
                "kind", "operation") + " }")
        value = expression if expression is not None else "[" + ", ".join(values) + "]"
        write(self.root, "Fvdep.Registry.Removed", f'''import {R}
namespace Fvdep.Registry
def removed : List {R}.Removed := {value}
end Fvdep.Registry
''')

    def add_version(self, version: str, *, compat: str | None = None,
                    valid_proof: bool = True, spec_type: str = "List UInt8 → List Char") -> str:
        suffix = "V" + version.replace(".", "_")
        spec = "Fvdep.Base64.Encode." + suffix
        entry = "Fvdep.Registry.Base64.Encode." + suffix
        proof = "FvdepProofs.Registry.Base64.Encode." + suffix
        body = S + ".encode" if spec_type == "List UInt8 → List Char" else "fun _ => 0"
        self.spec(f'''import {S}
namespace {spec}
def encode : {spec_type} := {body}
def bits : Prop := True
def length : Prop := True
end {spec}
''', spec)
        self.entry(module=entry, spec=spec + ".encode", version=version,
                   obligations=[spec + ".bits", spec + ".length"], compat=compat)
        theorem = ""
        if compat is not None:
            statement = f"@{spec}.encode = @{S}.encode" if valid_proof else "True"
            term = "rfl" if valid_proof else "True.intro"
            theorem = f"theorem compatible : {statement} := {term}\n"
        self.proofs(source=f'''import {entry}
namespace {proof}
theorem bits : {spec}.bits := True.intro
theorem length : {spec}.length := True.intro
{theorem}def proofs : {R}.Proofs := {{
  obligations := [(``{spec}.bits, ``{proof}.bits), (``{spec}.length, ``{proof}.length)]
  compat := {('some ``' + proof + '.compatible') if compat is not None else 'none'}
}}
end {proof}
''', module=proof)
        with (self.root / "FvdepProofs.lean").open("a") as stream:
            stream.write(f"import {proof}\n")
        return entry


def git(root: Path, *args: str) -> str:
    env = {**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_SYSTEM": "/dev/null"}
    proc = subprocess.run(["git", "-C", str(root), *args], env=env, capture_output=True,
                          timeout=30, check=False)
    if proc.returncode:
        raise RuntimeError(f"fixture git {' '.join(args)}: {proc.stderr.decode(errors='replace')}")
    return proc.stdout.decode().strip()


def init_git(root: Path) -> None:
    git(root, "init", "-q", "-b", "main")
    git(root, "config", "user.name", "fvdep index fixtures")
    git(root, "config", "user.email", "fixture@example.invalid")
    git(root, "config", "commit.gpgsign", "false")


def commit(root: Path, value: dict[str, Any] | None, subject: str = "fixture") -> str:
    if value is not None:
        (root / "index.json").write_bytes(canonical(value) + b"\n")
    git(root, "add", "-A")
    git(root, "commit", "-q", "--allow-empty", "-m", subject)
    return git(root, "rev-parse", "HEAD")


def index(*, operations: list[dict[str, Any]] | None = None,
          notices: list[dict[str, Any]] | None = None,
          removed: list[dict[str, Any]] | None = None,
          toolchain: str = TOOLCHAIN) -> dict[str, Any]:
    return {"schema": 1, "toolchain": toolchain, "operations": [] if operations is None else operations,
            "notices": [] if notices is None else notices, "removed": [] if removed is None else removed}


def operation(id: str = "base64.encode", version: str = "1.0.0", digest: str = "1" * 64,
              obligations: list[dict[str, Any]] | None = None, compat: Any = None) -> dict[str, Any]:
    return {"id": id, "version": version, "digest": digest, "compat": compat,
            "obligations": ([{"name": "bits", "status": "proven", "axioms": []}]
                            if obligations is None else obligations)}


def notice(id: str = "base64.encode", version: str = "1.0.0",
           reason: str = "fixture retraction", replacement: str | None = None) -> dict[str, Any]:
    return {"id": id, "version": version, "reason": reason, "replacement": replacement}


def removed_record(id: str = "base64.encode", version: str = "1.0.0",
                   last: str = "2" * 40, digest: str = "1" * 64) -> dict[str, Any]:
    return {"id": id, "version": version, "kind": "operation", "digest": digest,
            "toolchain": TOOLCHAIN, "last_commit": last}
