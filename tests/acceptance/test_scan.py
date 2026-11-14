"""Scan tests pin lock facts, not uncontracted package configuration defaults."""
import json
import random
import shutil

from harness import FIXTURES, SEED, case


def scan_fixture(ctx, name):
    ctx.library()
    target = ctx.base / ("scan-" + name)
    shutil.copytree(FIXTURES / "scan" / name, target)
    return target


def dependencies(ctx, directory):
    result = ctx.call("scan", str(directory), "--json").code(0).document()
    deps = result["result"]["dependencies"]
    for dependency in deps:
        assert set(dependency) == {"ecosystem", "package", "resolved", "range", "scope", "coverage", "operations", "suggestions", "assumes", "lockfile"}
        assert dependency["scope"] in {"direct", "indirect"}
        assert dependency["coverage"] in {"covered", "conditional", "preview", "not_covered", "unresolved"}
        if dependency["coverage"] == "conditional":
            assert dependency["assumes"], dependency
        if dependency["coverage"] == "covered":
            assert dependency["assumes"] == [], dependency
        if dependency["operations"] is not None:
            assert 0 <= dependency["operations"]["proven"] <= dependency["operations"]["total"]
    return deps


for name, direct, direct_version, indirect, indirect_version in [
    ("pnpm", "base64-js", "1.5.1", "semver", "7.7.3"),
    ("npm", "base64-js", "1.5.1", "semver", "7.7.3"),
    ("cargo", "base64", "0.22.1", "semver", "1.0.27"),
    ("uv", "direct-leaf", "1.2.3", "indirect-leaf", "2.3.4"),
    ("lake", "direct-lib", "a" * 40, "indirect-lib", "b" * 40),
]:
    @case(f"scan.resolved-scope.{name}", "U12", "Decisions Scan; interface §§3/6", f"{name} distinguishes exact direct and indirect versions without resolving a range")
    def resolved_scope(ctx, name=name, direct=direct, direct_version=direct_version,
                       indirect=indirect, indirect_version=indirect_version):
        target = scan_fixture(ctx, name)
        before = {str(p.relative_to(target)): p.read_bytes() for p in target.rglob("*") if p.is_file()}
        deps = dependencies(ctx, target)
        direct_rows = [d for d in deps if d["package"] == direct]
        indirect_rows = [d for d in deps if d["package"] == indirect]
        assert len(direct_rows) == len(indirect_rows) == 1, deps
        assert direct_rows[0]["scope"] == "direct" and direct_rows[0]["resolved"] == direct_version
        assert indirect_rows[0]["scope"] == "indirect" and indirect_rows[0]["resolved"] == indirect_version
        after = {str(p.relative_to(target)): p.read_bytes() for p in target.rglob("*") if p.is_file()}
        assert before == after, "scan wrote to its input directory"


@case("scan.other-version-is-suggestion", "U12", "Decisions Scan; interface §3", "A different package version can only suggest a profile and never counts as covered")
def other_version(ctx):
    target = scan_fixture(ctx, "npm-other-version")
    rows = [d for d in dependencies(ctx, target) if d["package"] == "base64-js"]
    assert len(rows) == 1 and rows[0]["resolved"] == "1.5.0"
    assert rows[0]["coverage"] == "not_covered", rows
    assert any(suggestion.startswith("npm:base64-js@1.5.1") for suggestion in rows[0]["suggestions"]), rows


@case("scan.unresolved-range", "U12", "Decisions Scan; interface §§3/6", "An unresolved range is printed as unresolved, never as an exact covered version")
def unresolved(ctx):
    target = scan_fixture(ctx, "npm-unresolved")
    rows = [d for d in dependencies(ctx, target) if d["package"] == "not-resolved"]
    assert len(rows) == 1
    assert rows[0]["resolved"] is None and rows[0]["range"] == "^1.2.0"
    assert rows[0]["coverage"] == "unresolved" and rows[0]["operations"] is None
    text = ctx.call("scan", str(target)).code(0).stdout
    assert "npm:not-resolved ^1.2.0  unresolved" in text


for name, filename in [("unsupported", "package-lock.json"), ("malformed", "pnpm-lock.yaml")]:
    @case(f"scan.refuse.{name}", "U12", "interface §3 scan; Decisions Self-verification scope", f"{name} lock input is refused with exit 2 naming its file")
    def refuse(ctx, name=name, filename=filename):
        target = scan_fixture(ctx, name)
        result = ctx.call("scan", str(target), "--json").code(2)
        result.document()
        assert filename in result.text, result.text


@case("scan.no-lockfile", "U12", "interface §3 scan", "An empty scan directory is exit 2 rather than an empty coverage success")
def no_lock(ctx):
    ctx.library()
    directory = ctx.base / "no-lockfiles"
    directory.mkdir()
    ctx.call("scan", str(directory), "--json").code(2).document()


@case("scan.exact-version-property", "U12", "Decisions Scan", "Coverage never transfers from the profiled version to generated different versions", "property")
def exact_property(ctx):
    target = scan_fixture(ctx, "npm")
    path = target / "package-lock.json"
    value = json.loads(path.read_text())
    rng = random.Random(SEED ^ 7)
    versions = {"1.5.0", "1.5.2", "2.0.0", "0.0.0"}
    versions.update(f"{rng.randrange(2, 50)}.{rng.randrange(30)}.{rng.randrange(30)}" for _ in range(8))
    for version in sorted(versions):
        value["packages"]["node_modules/base64-js"]["version"] = version
        path.write_text(json.dumps(value) + "\n")
        rows = [d for d in dependencies(ctx, target) if d["package"] == "base64-js"]
        assert len(rows) == 1 and rows[0]["resolved"] == version
        assert rows[0]["coverage"] == "not_covered", rows


@case("scan.configuration-not-assumed", "U12", "Decisions Scan; library Profiles", "A crate lock lacking base64 engine configuration cannot claim unconditional coverage")
def configuration(ctx):
    target = scan_fixture(ctx, "cargo")
    row = next(d for d in dependencies(ctx, target) if d["package"] == "base64")
    # The launch profile is for STANDARD, but Cargo.lock does not record an engine.
    assert row["coverage"] in {"conditional", "preview", "not_covered"}, row
    if row["coverage"] == "conditional":
        assert row["assumes"] and "assumes:" in ctx.call("scan", str(target)).code(0).stdout
