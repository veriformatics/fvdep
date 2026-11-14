"""Project policy, receipts, refusal atomicity, and read-only report commands."""
import itertools
import json
import os
import random
import shutil
import tomllib

from harness import FIXTURES, SEED, case, checked_modules, differential_entry, one_module, receipt_valid, receipts, rewrite_lock, saved, unchanged


@case("workflow.init-required", "U8", "interface §§3/5/7", "init creates a schema-1 empty manifest pinned to the library head with proof required")
def init_required(ctx):
    _, pin = ctx.library()
    result = ctx.call("init").code(0)
    assert result.stdout == "Created fvdep.toml (proof required)\n"
    value = tomllib.loads((ctx.base / "fvdep.toml").read_text())
    assert value["schema"] == 1 and value["library"]["commit"] == pin
    assert value["policy"]["proof"] == "required" and not value.get("modules")
    assert not (ctx.base / "fvdep.lock").exists()


@case("workflow.init-development", "U8", "interface §§3/5", "init --development saves test-evidence policy and never calls it delivered")
def init_development(ctx):
    ctx.library()
    result = ctx.call("init", "--development").code(0)
    assert result.stdout == "Created fvdep.toml (development: test evidence accepted, never delivered)\n"
    assert tomllib.loads((ctx.base / "fvdep.toml").read_text())["policy"]["proof"] == "development"


@case("workflow.init-existing", "U8", "interface §§2–3", "init never overwrites an existing manifest")
def init_existing(ctx):
    project = ctx.differential()
    before = saved(project)
    ctx.call("init", cwd=project).code(2)
    unchanged(project, before)


for policy, expected in [("development", 0), ("required", 1), (None, 1)]:
    name = policy or "absent-default"

    @case(f"policy.differential.{name}", "U8", "Decisions Guarantee; Proof policy; interface §5", f"Matching test evidence under {name} is never delivered and obeys saved policy")
    def policy_match(ctx, policy=policy, expected=expected):
        project = ctx.differential(policy=policy)
        before = saved(project)
        result = ctx.call("check", "--json", cwd=project)
        module = one_module(result, expected)
        assert module["verdict"] == "matched" and module["evidence"] == "differential"
        assert module["policy_met"] is (expected == 0)
        receipt_valid(module["receipt"], evidence="differential")
        if expected:
            assert any(r["code"] == "policy_proof_required" for r in module["reasons"])
        unchanged(project, before)
        text = ctx.call("check", cwd=project).code(expected).stdout
        first = text.splitlines()[0]
        assert first.startswith("MATCHED base64.encode@1.0.0 ") and first.endswith("(test evidence, not delivered)"), text


for mode, expected, verdict, code in [
    ("mismatch", 1, "mismatch", "mismatch"), ("wrong-error", 1, "mismatch", "mismatch"),
    ("unsupported", 2, None, "adapter"), ("invalid", 2, None, "adapter"),
    ("crash", 2, None, "adapter"), ("not-json", 2, None, "adapter"),
    ("missing", 2, None, "adapter"), ("extra", 2, None, "adapter"),
]:
    @case(f"adapter.reject.{mode}", "U8", "interface §§2/8", f"Adapter mode {mode} produces exit {expected} without updating either project file")
    def bad_adapter(ctx, mode=mode, expected=expected, verdict=verdict, code=code):
        project = ctx.differential(mode)
        before = saved(project)
        result = ctx.call("lock", "--json", cwd=project).code(expected)
        document = result.document()
        if expected == 2:
            assert document["error"]["code"] == code, document
            assert "adapter" in document["error"]["detail"].lower(), document
        else:
            module = one_module(result)
            assert module["verdict"] == verdict
            assert any(r["code"] == code for r in module["reasons"])
        unchanged(project, before)


@case("adapter.partial-unsupported", "U8", "interface §8", "Unsupported requests are skipped when other requests match")
def partial_unsupported(ctx):
    project = ctx.differential("some-unsupported")
    module = one_module(ctx.call("check", "--json", cwd=project), 0)
    assert module["verdict"] == "matched"


@case("adapter.rejection-text-ignored", "U8", "interface §8", "Decode rejection text is never compared with the oracle's rejection text")
def rejection_text(ctx):
    project = ctx.manifest({"base64.decode": differential_entry()}, policy="development")
    shutil.copy2(FIXTURES / "adapter.py", project / "adapter.py")
    module = one_module(ctx.call("check", "--json", cwd=project), 0)
    assert module["verdict"] == "matched"


@case("policy.exit-precedence", "U8", "interface §2; Decisions Public interface", "Module mixes return max(2,1,0) independently of manifest order", "property")
def exit_precedence(ctx):
    rng = random.Random(SEED ^ 5)
    ids = ["base64.encode", "base64.encode_url", "base64.decode"]
    for outcomes in itertools.product([0, 1, 2], repeat=3):
        order = list(zip(ids, outcomes, strict=True))
        rng.shuffle(order)
        entries = {id: differential_entry({0: "match", 1: "mismatch", 2: "crash"}[code]) for id, code in order}
        project = ctx.manifest(entries, policy="development")
        shutil.copy2(FIXTURES / "adapter.py", project / "adapter.py")
        before = saved(project)
        result = ctx.call("check", "--json", cwd=project).code(max(outcomes))
        result.document()
        unchanged(project, before)


@case("workflow.refusal-byte-identity", "U8", "Decisions Proof policy; Data formats; interface §2", "Every sampled pre-commit refusal preserves manifest and existing-or-absent lock byte for byte", "property")
def refusal_bytes(ctx):
    for command, has_lock, mode in itertools.product(["check", "lock"], [False, True], ["match", "mismatch", "crash"]):
        project = ctx.differential()
        if has_lock:
            ctx.call("lock", cwd=project).code(0)
        manifest = project / "fvdep.toml"
        text = manifest.read_text().replace('proof = "development"', 'proof = "required"')
        text = text.replace('"adapter.py", "match"', f'"adapter.py", "{mode}"')
        manifest.write_text(text)
        before = saved(project)
        ctx.call(command, "--json", cwd=project).code(2 if mode == "crash" else 1).document()
        unchanged(project, before)


@case("workflow.no-lock-status", "U8", "interface §§3–4", "A fresh valid proof is not delivered without a lock receipt")
def no_lock_status(ctx):
    project = ctx.project()
    before = saved(project)
    one_module(ctx.call("check", "--json", cwd=project), 0)
    result = ctx.call("status", "--json", cwd=project).code(1).document()
    module = result["result"]["modules"][0]
    assert module["delivered"] is False and module["reason"] is not None
    ctx.call("status", cwd=project).code(1).contains("no lock entry")
    unchanged(project, before)


@case("workflow.proof-lock-delivery", "U8", "Decisions Proof policy; Data formats; interface §§3–4/6", "Only a current proof receipt yields DELIVERED and lock stores no delivered bit")
def proof_lock_delivery(ctx):
    project = ctx.project()
    manifest_before = saved(project)["fvdep.toml"]
    module = one_module(ctx.call("lock", "--json", cwd=project), 0)
    receipt_valid(module["receipt"], evidence="proof")
    assert saved(project)["fvdep.toml"] == manifest_before
    lock = json.loads((project / "fvdep.lock").read_text())
    assert lock["schema"] == 1
    found = receipts(lock)
    assert len(found) == 1 and found[0] == module["receipt"]

    def no_delivered(value):
        if isinstance(value, dict):
            assert "delivered" not in value, value
            for child in value.values():
                no_delivered(child)
        elif isinstance(value, list):
            for child in value:
                no_delivered(child)
    no_delivered(lock)
    before = saved(project)
    text = ctx.call("status", cwd=project).code(0).stdout
    assert "DELIVERED base64.encode@1.0.0 Impl.encode" in text
    result = ctx.call("status", "--json", cwd=project).code(0).document()
    assert result["result"]["modules"][0]["delivered"] is True
    current = one_module(ctx.call("check", "--json", cwd=project), 0)
    assert current["lock"] == "current"
    unchanged(project, before)


@case("workflow.development-lock-not-delivered", "U8", "Decisions Guarantee; interface §5", "Development receipts meet policy but status still says NOT DELIVERED")
def development_lock(ctx):
    project = ctx.differential()
    module = one_module(ctx.call("lock", "--json", cwd=project), 0)
    receipt_valid(module["receipt"], evidence="differential")
    text = ctx.call("status", cwd=project).code(0).stdout
    assert "NOT DELIVERED base64.encode@1.0.0: test evidence only" in text
    value = ctx.call("status", "--json", cwd=project).code(0).document()
    assert value["result"]["modules"][0]["delivered"] is False


for changed in ("implementation", "proof", "adapter", "verification-profile"):
    @case(f"workflow.stale.{changed}", "U8", "Decisions Proof policy; Lifecycle + profile evolution; interface §3", f"A changed {changed} makes a saved receipt stale without rebuilding")
    def stale(ctx, changed=changed):
        project = ctx.differential() if changed == "adapter" else ctx.project()
        ctx.call("lock", cwd=project).code(0)
        if changed == "implementation":
            path = project / "Impl.lean"
            path.write_text(path.read_text() + "\n-- source closure changed\n")
        elif changed == "proof":
            path = project / "Proof.lean"
            path.write_text(path.read_text() + "\n-- proof closure changed\n")
        elif changed == "adapter":
            path = project / "adapter.py"
            path.write_text(path.read_text() + "\n# adapter bytes changed\n")
        else:
            rewrite_lock(project, lambda value: receipts(value)[0].update(verification_profile="acceptance-previous-profile"))
        before = saved(project)
        value = ctx.call("status", "--json", cwd=project).code(1).document()
        assert value["result"]["modules"][0]["delivered"] is False
        assert value["result"]["modules"][0]["reason"] is not None
        unchanged(project, before)
        if changed == "verification-profile":
            implementation = project / "Impl.lean"
            implementation.write_text(implementation.read_text() + "\n-- source stale too\n")
            lines = ctx.call("status", cwd=project).code(1).stdout.splitlines()
            assert "NOT DELIVERED base64.encode@1.0.0: the proof was checked under an older verification profile" in lines, lines
            unchanged(project, before)
        # A fresh successful recheck is a successful check even with a stale lock.
        fresh = one_module(ctx.call("check", "--json", cwd=project), 0)
        assert fresh["lock"] == "out_of_date"
        unchanged(project, before)


@case("workflow.status-no-rebuild", "U8", "interface §3 status", "status can report current delivery without running Lean or Lake")
def no_rebuild(ctx):
    project = ctx.project()
    ctx.call("lock", cwd=project).code(0)
    fake = ctx.base / "fake-tools"
    fake.mkdir()
    marker = ctx.base / "unexpected-build"
    for name in ("lean", "lake"):
        path = fake / name
        path.write_text(f'#!/bin/sh\nprintf called >> "{marker}"\nexit 71\n')
        path.chmod(0o755)
    before = saved(project)
    ctx.call("status", "--json", cwd=project, env={"PATH": str(fake) + os.pathsep + os.environ["PATH"]}).code(0).document()
    assert not marker.exists(), "status invoked the build toolchain"
    unchanged(project, before)


@case("workflow.check-subset", "U8", "interface §3 check", "A subset check reports only requested manifest modules and writes no files")
def check_subset(ctx):
    project = ctx.project("honest-launch")
    before = saved(project)
    modules = checked_modules(ctx.call("check", "base64.decode", "semver.parse", "--json", cwd=project), 0)
    assert {m["module"] for m in modules} == {"base64.decode", "semver.parse"}
    unchanged(project, before)


@case("workflow.check-absent-module", "U8", "interface §2", "Checking a module absent from the manifest is exit 2 and read-only")
def absent_module(ctx):
    project = ctx.differential()
    before = saved(project)
    ctx.call("check", "base64.decode", "--json", cwd=project).code(2).document()
    unchanged(project, before)


@case("workflow.lock-json-round-trip", "U8", "Decisions Data formats; interface §6", "A schema lock survives a JSON decode/encode cycle and the product rereads the same receipts", "property")
def lock_json_round_trip(ctx):
    project = ctx.project("honest-launch")
    ctx.call("lock", "--json", cwd=project).code(0).document()
    original = json.loads((project / "fvdep.lock").read_text())
    expected = receipts(original)
    assert len(expected) == 6
    for item in expected:
        receipt_valid(item, evidence="proof")
    encoded = json.dumps(original, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"
    (project / "fvdep.lock").write_text(encoded)
    before = saved(project)
    value = ctx.call("status", "--json", cwd=project).code(0).document()
    assert len(value["result"]["modules"]) == 6
    assert all(m["delivered"] for m in value["result"]["modules"])
    assert receipts(json.loads((project / "fvdep.lock").read_text())) == expected
    unchanged(project, before)


@case("workflow.commit-io-old-or-new", "U8", "interface §2; Decisions Data formats", "A denied lock commit exits 2 with commit_io and leaves complete old bytes")
def commit_io(ctx):
    assert os.geteuid() != 0, "run this filesystem-permission test as an unprivileged user"
    project = ctx.project()
    ctx.call("lock", cwd=project).code(0)
    before = saved(project)
    mode = project.stat().st_mode & 0o777
    project.chmod(0o555)
    try:
        result = ctx.call("lock", "--json", cwd=project).code(2)
        document = result.document()
        # Exclusive writer-lock creation may fail before commit on some IO mappings;
        # either is infrastructure, and neither may corrupt persisted bytes.
        assert document["error"]["code"] in {"io", "commit_io"}, document
        if document["error"]["code"] == "commit_io":
            assert "Could not finish writing fvdep.lock:" in result.stderr
            assert 'Run "fvdep status" to see the state.' in result.stderr
        unchanged(project, before)
    finally:
        project.chmod(mode)
