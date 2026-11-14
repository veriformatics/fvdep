"""Local git-library extensions using the public Registry declarations.

Only fixture construction inspects declaration headers. Expected values never
come from a library body, registry status flag, or product implementation.
"""
import json
import re
from pathlib import Path

BASE = "Fvdep.Base64.Encode.V1_0_0"


def write_module(root: Path, module: str, source: str) -> None:
    path = root / (module.replace(".", "/") + ".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)


def add_version(ctx, version: str, *, compat: bool = False, changed: bool = False,
                bad_compat: bool = False) -> str:
    root, _ = ctx.library()
    suffix = "V" + version.replace(".", "_")
    spec = f"Fvdep.Base64.Encode.{suffix}"
    entry = f"Fvdep.Registry.Base64.Encode.{suffix}"
    proofs = f"FvdepProofs.Registry.Base64.Encode.{suffix}"
    body = f"fun xs => ({BASE}.encode xs).reverse" if changed else f"{BASE}.encode"
    write_module(root, spec, f"import {BASE}\nnamespace {spec}\ndef encode : List UInt8 → List Char :=\n  {body}\ndef total : Prop := True\nend {spec}\n")
    write_module(root, entry, f'''import {spec}
import Fvdep.Abi.V1_0_0
import Fvdep.Registry.Types.V1
namespace {entry}
def entry : Fvdep.Registry.Types.V1.Module := {{
  id := "base64.encode", version := "{version}", spec := ``{spec}.encode,
  obligations := [``{spec}.total],
  abi := some ``Fvdep.Abi.V1_0_0.encoder,
  compat := {('some "1.0.0"' if compat else 'none')} }}
end {entry}
''')
    compat_theorem = ""
    if compat:
        statement = "True" if bad_compat else f"@{spec}.encode = @{BASE}.encode"
        compat_theorem = f"theorem compatible : {statement} := {'True.intro' if bad_compat else 'rfl'}\n"
    compat_value = f"some ``{proofs}.compatible" if compat else "none"
    write_module(root, proofs, f'''import {entry}
namespace {proofs}
theorem total_proof : {spec}.total := True.intro
{compat_theorem}def proofs : Fvdep.Registry.Types.V1.Proofs := {{
  obligations := [(``{spec}.total, ``{proofs}.total_proof)],
  compat := {compat_value} }}
end {proofs}
''')
    registry = root / "Fvdep/Registry.lean"
    source = registry.read_text()
    # The documented root exports modules then profiles. Preserve every original
    # entry and its namespace; add one public declaration beside those exports.
    base_name = "acceptanceBaseModules" + version.replace(".", "_")
    source, count = re.subn(r"\bdef\s+modules\b", f"def {base_name}", source, count=1)
    assert count == 1, "fixture Registry needs the contract's `def modules` declaration"
    match = re.search(r"(?m)^(?:\s*)def\s+profiles\b", source)
    assert match is not None, "fixture Registry needs `def profiles` after `def modules`"
    insertion = f"\ndef modules : List Fvdep.Registry.Types.V1.Module :=\n  {base_name} ++ [{entry}.entry]\n\n"
    source = source[:match.start()] + insertion + source[match.start():]
    registry.write_text(f"import {entry}\n" + source)
    for root_file, module in (("Fvdep.lean", entry), ("FvdepProofs.lean", proofs)):
        file = root / root_file
        if file.exists():
            file.write_text(f"import {module}\n" + file.read_text())
    ctx.call("index", cwd=root).code(0)
    return ctx.commit(root, f"add base64.encode {version}")


def add_notice(ctx, *, version: str = "1.0.0", replacement: str | None = "1.1.0",
               reason: str = "acceptance retraction") -> str:
    root, _ = ctx.library()
    path = root / "Fvdep/Registry/Notices.lean"
    source = path.read_text()
    match = re.search(r"\bdef\s+notices\s*:[\s\S]*?:=\s*", source)
    assert match is not None, "fixture Notices needs the contract's `def notices` declaration"
    begin = source.find("[", match.end())
    assert begin >= 0, "fixture Notices needs the documented list literal"
    depth, quoted, escaped, end = 0, False, False, None
    for index in range(begin, len(source)):
        char = source[index]
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                end = index
                break
    assert end is not None
    previous = source[begin + 1:end].strip()
    repl = "none" if replacement is None else f"some {json.dumps(replacement)}"
    notice = f'{{ id := "base64.encode", version := {json.dumps(version)}, reason := {json.dumps(reason)}, replacement := {repl} }}'
    contents = (previous + ",\n  " if previous else "") + notice
    path.write_text(source[:begin] + "[" + contents + "]" + source[end + 1:])
    ctx.call("index", cwd=root).code(0)
    return ctx.commit(root, "append retraction notice")


def index_entries(value):
    found = []
    if isinstance(value, dict):
        if {"id", "version", "digest"} <= set(value):
            found.append(value)
        else:
            for child in value.values():
                found.extend(index_entries(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(index_entries(child))
    return found


def operation_digest(root: Path, id: str = "base64.encode", version: str = "1.0.0") -> str:
    values = index_entries(json.loads((root / "index.json").read_text()))
    matches = [entry["digest"] for entry in values if entry["id"] == id and entry["version"] == version]
    assert len(matches) == 1, (id, version, matches)
    assert re.fullmatch(r"[0-9a-f]{64}", matches[0]), matches
    return matches[0]
