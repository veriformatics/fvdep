"""Schema refusals are infrastructure outcomes, before any persistence commit."""
import json
import random
import shutil

from harness import FIXTURES, SEED, case, differential_entry, proof_entry, saved, unchanged


BAD_MANIFESTS = [
    ("schema-version", "schema = 1", "schema = 2", "schema"),
    ("schema-type", "schema = 1", 'schema = "1"', "schema"),
    ("duplicate-key", "schema = 1", "schema = 1\nschema = 1", "schema"),
    ("extra-root", "schema = 1", 'schema = 1\nunexpected = "x"', "unexpected"),
    ("extra-library", '[library]', '[library]\nunexpected = "x"', "unexpected"),
    ("uppercase-commit", None, None, "commit"),
    ("short-commit", None, None, "commit"),
    ("missing-library", None, None, "library"),
    ("policy-value", 'proof = "required"', 'proof = "optional"', "proof"),
    ("policy-type", 'proof = "required"', "proof = true", "proof"),
    ("module-version", 'version = "1.0.0"', 'version = "01.0.0"', "version"),
    ("module-prerelease", 'version = "1.0.0"', 'version = "1.0.0-rc.1"', "version"),
    ("module-build", 'version = "1.0.0"', 'version = "1.0.0+build"', "version"),
    ("shape", 'shape = "fn"', 'shape = "native"', "shape"),
    ("empty-impl-modules", 'impl_modules = ["Impl"]', "impl_modules = []", "impl_modules"),
    ("empty-proof-modules", 'proof_modules = ["Proof"]', "proof_modules = []", "proof_modules"),
    ("repeat-impl-module", 'impl_modules = ["Impl"]', 'impl_modules = ["Impl", "Impl"]', "impl_modules"),
    ("overlap-modules", 'proof_modules = ["Proof"]', 'proof_modules = ["Impl"]', "Impl"),
    ("extra-module-key", 'shape = "fn"', 'shape = "fn"\nunexpected = 1', "unexpected"),
    ("missing-proof", 'proof = "Proof.encode_eq"\n', "", "proof"),
    ("wrong-module-list-type", 'impl_modules = ["Impl"]', 'impl_modules = "Impl"', "impl_modules"),
]


for name, old, new, field in BAD_MANIFESTS:
    @case(f"schema.manifest.{name}", "U8", "Decisions Data formats; interface §7", f"Manifest defect {name} is named, refused with exit 2, and read-only")
    def bad_manifest(ctx, name=name, old=old, new=new, field=field):
        project = ctx.project()
        path = project / "fvdep.toml"
        text = path.read_text()
        if name == "uppercase-commit":
            _, pin = ctx.library()
            # A guaranteed letter avoids a vanishingly rare all-numeric SHA.
            text = text.replace(pin, "A" + pin[1:])
        elif name == "short-commit":
            _, pin = ctx.library()
            text = text.replace(pin, pin[:12])
        elif name == "missing-library":
            _, pin = ctx.library()
            text = text.replace(f'[library]\ncommit = "{pin}"\n', "")
        else:
            assert old in text, (name, text)
            text = text.replace(old, new)
        path.write_text(text)
        before = saved(project)
        result = ctx.call("lock", "--json", cwd=project).code(2)
        value = result.document()
        assert value["error"]["code"] == "schema", value
        assert field in value["error"]["detail"], value
        unchanged(project, before)


for name, entry in [
    ("empty-argv", {"version": "1.0.0", "evidence": "differential", "adapter": []}),
    ("argv-type", {"version": "1.0.0", "evidence": "differential", "adapter": "adapter.py"}),
    ("missing-argv", {"version": "1.0.0", "evidence": "differential"}),
    ("forbidden-proof-field", differential_entry() | {"proof": "Proof.encode_eq"}),
    ("forbidden-shape", differential_entry() | {"shape": "fn"}),
    ("proof-forbidden-evidence", proof_entry() | {"evidence": "proof"}),
]:
    @case(f"schema.evidence.{name}", "U8", "interface §7", f"Evidence entry {name} cannot cross the proof/differential schema boundary")
    def evidence_schema(ctx, entry=entry):
        project = ctx.manifest({"base64.encode": entry})
        before = saved(project)
        value = ctx.call("lock", "--json", cwd=project).code(2).document()
        assert value["error"]["code"] == "schema", value
        unchanged(project, before)


for name in ("schema-version", "unknown-field", "duplicate-key"):
    @case(f"schema.lock.{name}", "U8", "Decisions Data formats; interface §6", f"Lock defect {name} is refused with exit 2 without overwriting its bytes")
    def bad_lock(ctx, name=name):
        project = ctx.differential()
        ctx.call("lock", cwd=project).code(0)
        path = project / "fvdep.lock"
        value = json.loads(path.read_text())
        if name == "schema-version":
            value["schema"] = 99
            text = json.dumps(value)
        elif name == "unknown-field":
            value["unexpected"] = True
            text = json.dumps(value)
        else:
            text = '{"schema":1,' + json.dumps(value).lstrip()[1:]
        path.write_text(text)
        before = saved(project)
        document = ctx.call("status", "--json", cwd=project).code(2).document()
        assert document["error"]["code"] == "schema", document
        unchanged(project, before)


@case("schema.manifest-printer-round-trip", "U8", "Decisions Data formats; interface §§3/7", "Canonical init manifests round-trip through the public TOML reader for both policies", "property")
def printer_round_trip(ctx):
    rng = random.Random(SEED ^ 6)
    for development in rng.sample([False, True], k=2):
        ctx.library()
        directory = ctx.base / ("dev-init" if development else "proof-init")
        directory.mkdir()
        ctx.call("init", *( ["--development"] if development else []), cwd=directory).code(0)
        before = saved(directory)
        # No modules means policy is vacuously met; the printer's output must parse.
        document = ctx.call("check", "--json", cwd=directory).code(0).document()
        assert document["result"]["modules"] == []
        unchanged(directory, before)


@case("schema.unrecognized-operation", "U8", "interface §§2/7", "A nonexistent manifest operation is refused instead of checking a same-shaped operation")
def unknown_operation(ctx):
    project = ctx.manifest({"missing.operation": differential_entry()}, policy="development")
    shutil.copy2(FIXTURES / "adapter.py", project / "adapter.py")
    before = saved(project)
    ctx.call("check", "--json", cwd=project).code(2).contains("missing.operation")
    unchanged(project, before)
