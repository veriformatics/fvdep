"""Library reports, generated index identity, and admission boundaries."""
import json
import re

from harness import case, saved, unchanged
from library_fixtures import add_version, operation_digest

LAUNCH = {"base64.encode", "base64.decode", "base64.encode_url", "base64.decode_url", "semver.parse", "semver.compare"}


@case("library.launch-list", "U8", "Decisions Launch set; Library API v1; interface §§3/6", "The launch set has six operation versions and every obligation is proven")
def launch_list(ctx):
    ctx.library()
    value = ctx.call("list", "--json").code(0).document()
    operations = value["result"]["operations"]
    assert {operation["id"] for operation in operations} >= LAUNCH
    for operation in operations:
        if operation["id"] in LAUNCH:
            assert operation["version"] == "1.0.0", operation
            counts = operation["obligations"]
            assert counts["proven"] == counts["total"] and counts["total"] >= 0, operation
    result = ctx.call("list").code(0)
    for id in LAUNCH:
        assert re.search(rf"(?m)^{re.escape(id)}@1\.0\.0  \d+/\d+ obligations proven$", result.stdout), result.stdout


@case("library.preview-separate", "U10", "Decisions Preview area; Profile shape; library Profiles; interface §6", "Preview operations stay outside the published list and have explicit per-operation status")
def preview_separate(ctx):
    ctx.library()
    plain = ctx.call("list", "--json").code(0).document()["result"]["profiles"]
    extended = ctx.call("list", "--previews", "--json").code(0).document()["result"]["profiles"]
    assert all(profile["area"] == "published" for profile in plain)
    assert all(profile["area"] in {"published", "preview"} for profile in extended)
    seen = set()
    for profile in extended:
        for operation in profile["operations"]:
            assert operation["status"] == profile["area"], (profile, operation)
            key = (profile["id"], operation["name"])
            assert key not in seen, f"operation appears in both latest areas: {key}"
            seen.add(key)
    published = {(p["id"], p["version"]) for p in plain}
    assert published == {(p["id"], p["version"]) for p in extended if p["area"] == "published"}


@case("library.launch-profile-identities", "U10", "Decisions Launch set; library Profiles", "All four package identities remain visible in published or preview areas")
def launch_profiles(ctx):
    ctx.library()
    profiles = ctx.call("list", "--previews", "--json").code(0).document()["result"]["profiles"]
    ids = {profile["id"].split("#", 1)[0] for profile in profiles}
    assert {"cpython:base64@3.14", "npm:base64-js@1.5.1", "crates:base64@0.22.1", "npm:semver@7.7.3"} <= ids
    for profile in profiles:
        assert re.fullmatch(r"[^:]+:.+@[^#]+(?:#[a-z0-9-]+)?", profile["id"]), profile
        assert re.fullmatch(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)", profile["version"])


@case("library.show-operation", "U8", "interface §3; library Operations", "show exposes the operation version, statement, and obligation status")
def show_operation(ctx):
    ctx.library()
    result = ctx.call("show", "base64.encode@1.0.0").code(0)
    for text in ("1.0.0", "encode", "UInt8", "Char"):
        assert text in result.stdout, result.stdout
    assert "obligation" in result.stdout.lower(), result.stdout


@case("library.brief", "U8", "interface §3; Decisions Conformance method", "brief supplies the statement, profile rules, proof freedom, manifest entry, and check command")
def brief(ctx):
    ctx.library()
    result = ctx.call("brief", "base64.encode@1.0.0").code(0)
    for text in ("base64.encode", "1.0.0", "impl_modules", "proof_modules", "fvdep check"):
        assert text in result.stdout, result.stdout
    assert "proof" in result.stdout.lower() and "profile" in result.stdout.lower()


for command, args in [("show", ["missing.operation"]), ("brief", ["missing.operation"]),
                      ("diff", ["base64.encode", "1.0.0", "99.0.0"]),
                      ("profile", ["npm:missing-package@0.0.0", "--check"])]:
    @case(f"library.unrecognized.{command}", "U8", "interface §§2–3", f"{command} refuses a target absent from the selected snapshot")
    def unknown(ctx, command=command, args=args):
        ctx.library()
        ctx.call(command, *args).code(2)


@case("library.index-pure", "U4", "Decisions Library layout + identity; library Registry; interface §3", "Index generation is byte-idempotent and --check is read-only", "property")
def index_pure(ctx):
    root, _ = ctx.library()
    first = ctx.call("index", cwd=root).code(0)
    assert re.fullmatch(r"Wrote index\.json \(\d+ entries\)\n", first.stdout), first.stdout
    path = root / "index.json"
    expected = path.read_bytes()
    data = json.loads(expected)
    assert data["schema"] == 1
    ctx.call("index", cwd=root).code(0)
    assert path.read_bytes() == expected
    result = ctx.call("index", "--check", cwd=root).code(0)
    assert result.stdout == "index.json is current\n"
    assert path.read_bytes() == expected


@case("library.index-drift", "U4", "interface §3 index", "index --check reports byte drift without rewriting the committed index")
def index_drift(ctx):
    root, _ = ctx.library()
    ctx.call("index", cwd=root).code(0)
    path = root / "index.json"
    changed = path.read_bytes() + b" "
    path.write_bytes(changed)
    result = ctx.call("index", "--check", cwd=root).code(1)
    assert result.stdout == "index.json differs from the library\n"
    assert path.read_bytes() == changed


@case("library.identity-proof-exclusion", "U4", "Decisions Library layout + identity; library Registry (identity)", "Changing proof bytes alone leaves the entry identity unchanged", "property")
def proof_exclusion(ctx):
    root, _ = ctx.library()
    ctx.call("index", cwd=root).code(0)
    before = operation_digest(root)
    path = root / "FvdepProofs/Registry/Base64/Encode/V1_0_0.lean"
    assert path.is_file(), "the contract's phase-2 proof registry is missing"
    path.write_text(path.read_text() + "\n-- proof-only identity perturbation\n")
    ctx.call("index", cwd=root).code(0)
    assert operation_digest(root) == before


@case("library.identity-source-sensitive", "U4", "Decisions Library layout + identity; library Registry (identity)", "Changing any sampled source-closure byte changes the entry digest", "property")
def source_sensitive(ctx):
    root, _ = ctx.library()
    ctx.call("index", cwd=root).code(0)
    before = operation_digest(root)
    path = root / "Fvdep/Base64/Encode/V1_0_0.lean"
    path.write_text(path.read_text() + "\n-- source identity perturbation\n")
    ctx.call("index", cwd=root).code(0)
    assert operation_digest(root) != before


@case("library.identity-unrelated-entry", "U4", "library Registry (identity); Decisions Spec modularity", "Adding a separately versioned entry leaves the original identity unchanged", "property")
def unrelated_entry(ctx):
    root, _ = ctx.library()
    ctx.call("index", cwd=root).code(0)
    before = operation_digest(root)
    add_version(ctx, "1.0.1")
    assert operation_digest(root) == before


@case("library.latest-numeric-version", "U8", "library Naming; interface §3 list", "Operation entry versions sort numerically rather than as strings")
def latest_numeric(ctx):
    ctx.library()
    add_version(ctx, "1.0.2")
    add_version(ctx, "1.0.10")
    operations = ctx.call("list", "--json").code(0).document()["result"]["operations"]
    matches = [item for item in operations if item["id"] == "base64.encode"]
    assert len(matches) == 1 and matches[0]["version"] == "1.0.10", matches


@case("library.admit-read-only", "U7", "Decisions Automation; library Registry; interface §3 admit", "Admission of an already valid library reports results without changing its working tree")
def admit_read_only(ctx):
    root, _ = ctx.library()
    before = ctx.git(root, "status", "--porcelain", "--untracked-files=all")
    result = ctx.call("admit", str(root)).code(0)
    assert "ADMITTED " in result.stdout, result.stdout
    assert ctx.git(root, "status", "--porcelain", "--untracked-files=all") == before


@case("library.admit-mutated-published", "U7", "Decisions Retraction; Library layout + identity; library Registry", "Admission refuses a byte edit to a published source closure")
def admit_mutated(ctx):
    root, pin = ctx.library()
    path = root / "Fvdep/Base64/Encode/V1_0_0.lean"
    path.write_text(path.read_text() + "\n-- a new byte changes this published identity\n")
    before = path.read_bytes()
    result = ctx.call("admit", str(root), "--base", pin).code(1)
    assert "REFUSED " in result.stdout, result.stdout
    assert path.read_bytes() == before


@case("library.admit-wrong-compat", "U7", "Decisions Module updates; library Registry (proof registry)", "A tagged theorem of True cannot certify the new=old compatibility statement")
def admit_wrong_compat(ctx):
    root, pin = ctx.library()
    add_version(ctx, "1.1.0", compat=True, bad_compat=True)
    result = ctx.call("admit", str(root), "--base", pin).code(1)
    assert "REFUSED " in result.stdout


@case("library.project-snapshot", "U8", "interface §1; Decisions Spec modularity", "Library reports inside a project use its pinned source snapshot, not the feed head")
def project_snapshot(ctx):
    project = ctx.project()
    add_version(ctx, "1.1.0", compat=True)
    before = saved(project)
    inside = ctx.call("list", "--json", cwd=project).code(0).document()["result"]["operations"]
    outside = ctx.call("list", "--json").code(0).document()["result"]["operations"]
    assert next(op for op in inside if op["id"] == "base64.encode")["version"] == "1.0.0"
    assert next(op for op in outside if op["id"] == "base64.encode")["version"] == "1.1.0"
    unchanged(project, before)
