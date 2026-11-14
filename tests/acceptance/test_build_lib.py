"""C delivery records and receipts; binary symbol/ownership API awaits U9."""
import hashlib
import json
import re
import shutil
from pathlib import Path

from harness import case, receipts, rewrite_lock, saved, unchanged


def built_record(project, out):
    record = json.loads((out / "fvdep-build.json").read_text())
    assert set(record) == {"built", "header", "library", "module", "receipt", "schema", "shape", "shim", "verification_profile", "version"}
    assert record["schema"] == 1 and record["module"] == "base64.encode" and record["version"] == "1.0.0"
    assert record["shape"] == "encoder" and record["shim"] and record["built"]
    by_hash = {}
    for path in out.rglob("*"):
        if path.is_file() and path.name != "fvdep-build.json":
            by_hash[hashlib.sha256(path.read_bytes()).hexdigest()] = path
    for field in ("library", "header"):
        assert re.fullmatch(r"[0-9a-f]{64}", record[field]) and record[field] in by_hash, (field, record)
    proof_receipt = next(receipt for receipt in receipts(json.loads((project / "fvdep.lock").read_text()))
                         if receipt["request"]["module"] == "base64.encode")
    canonical = json.dumps(proof_receipt, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()
    assert record["receipt"] == hashlib.sha256(canonical).hexdigest()
    assert record["verification_profile"] == proof_receipt["verification_profile"]
    return record


@case("build-lib.artifacts-and-receipt", "U9", "Decisions C-library delivery; interface §§3/6; library C ABI shapes", "build-lib emits hashed artifacts and a record extending the delivered ABI receipt without changing project files")
def artifacts(ctx):
    project = ctx.project("honest-abi")
    ctx.call("lock", cwd=project).code(0)
    before = saved(project)
    out = ctx.base / "c-library"
    result = ctx.call("build-lib", "base64.encode", "--out", str(out), cwd=project).code(0)
    assert "Built " in result.stdout and "for base64.encode@1.0.0 (encoder)" in result.stdout
    assert "C-ABI delivery also trusts: " in result.stdout and "your binding glue" in result.stdout
    built_record(project, out)
    unchanged(project, before)


@case("build-lib.default-output", "U9", "interface §3 build-lib", "The default C output directory is fvdep-build and project persistence is read-only")
def default_output(ctx):
    project = ctx.project("honest-abi")
    ctx.call("lock", cwd=project).code(0)
    before = saved(project)
    ctx.call("build-lib", "base64.encode", cwd=project).code(0)
    built_record(project, project / "fvdep-build")
    unchanged(project, before)


for fixture, lock, policy, name in [
    ("honest-abi", False, "required", "no-lock"),
    ("honest-fn", True, "required", "wrong-shape"),
    ("differential", True, "development", "test-evidence"),
]:
    @case(f"build-lib.refuse.{name}", "U9", "Decisions C-library delivery; interface §3", f"build-lib refuses {name} rather than treating it as C delivery")
    def refuse(ctx, fixture=fixture, lock=lock, policy=policy):
        project = ctx.differential() if fixture == "differential" else ctx.project(fixture, policy=policy)
        if lock:
            ctx.call("lock", cwd=project).code(0)
        before = saved(project)
        out = ctx.base / "refused-output"
        ctx.call("build-lib", "base64.encode", "--out", str(out), cwd=project).code(1)
        assert not (out / "fvdep-build.json").exists()
        unchanged(project, before)


@case("build-lib.cache-miss-reconstruction", "U9", "Decisions C-library delivery; interface §3 build-lib", "Losing cached phase-1 outputs triggers an isolated rebuild with the same receipt digest")
def reconstruct(ctx):
    project = ctx.project("honest-abi")
    ctx.call("lock", cwd=project).code(0)
    before = saved(project)
    cache = Path(ctx.env["FVDEP_CACHE"])
    assert cache.is_relative_to(ctx.base) and cache != ctx.base
    shutil.rmtree(cache)
    out = ctx.base / "reconstructed-output"
    ctx.call("build-lib", "base64.encode", "--out", str(out), cwd=project).code(0)
    built_record(project, out)
    unchanged(project, before)


@case("build-lib.cache-miss-digest-mismatch", "U9", "interface §3 build-lib; Decisions C-library delivery", "A reconstructed export that disagrees with the receipt is not shipped")
def reconstruct_mismatch(ctx):
    project = ctx.project("honest-abi")
    ctx.call("lock", cwd=project).code(0)

    def edit(value):
        for receipt in receipts(value):
            if receipt["request"]["module"] == "base64.encode":
                digest = receipt["digests"]["phase1_export"]
                receipt["digests"]["phase1_export"] = ("0" if digest[0] != "0" else "1") + digest[1:]
    rewrite_lock(project, edit)
    before = saved(project)
    cache = Path(ctx.env["FVDEP_CACHE"])
    assert cache.is_relative_to(ctx.base) and cache != ctx.base
    shutil.rmtree(cache)
    out = ctx.base / "refused-reconstruction"
    status = ctx.call("status", "--json", cwd=project)
    status.document()
    assert status.returncode in {0, 1, 2}
    result = ctx.call("build-lib", "base64.encode", "--out", str(out), cwd=project)
    assert result.returncode in {1, 2}, result.text
    # The contract permits refusing an invalid receipt before reconstruction.
    # If it still meets DELIVERED's precondition, the export mismatch has the
    # specified negative verdict and message instead of a C delivery.
    if status.returncode == 0:
        result.code(1).contains("the implementation changed")
    assert not (out / "fvdep-build.json").exists()
    unchanged(project, before)
