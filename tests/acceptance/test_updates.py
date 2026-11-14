"""Source snapshot and lifecycle snapshot are separate identities."""
import re
from pathlib import Path

from harness import case, checked_modules, saved, unchanged
from library_fixtures import add_notice, add_version


for name, version, compat, expected in [
    ("proven-major", "2.0.0", True, "same_behaviour"),
    ("unstated-minor", "1.1.0", False, "not_stated"),
    ("unstated-major", "2.0.0", False, "major"),
]:
    @case(f"updates.outdated.{name}", "U11", "Decisions Module updates; interface §§3/6", f"{name} compatibility follows the proven relation rather than version labels")
    def outdated(ctx, version=version, compat=compat, expected=expected):
        project = ctx.project()
        head = add_version(ctx, version, compat=compat)
        before = saved(project)
        document = ctx.call("outdated", "--json", cwd=project).code(0).document()
        module = document["result"]["modules"][0]
        assert module == {"module": "base64.encode", "pinned": "1.0.0", "latest": version,
                          "compat": expected, "retracted": None}, module
        assert document["status"]["commit"] == head and document["status"]["fetched"]
        text = ctx.call("outdated", cwd=project).code(0).stdout
        phrase = {"same_behaviour": "same behaviour (proven)", "not_stated": "compatibility not stated", "major": "major version: prove again"}[expected]
        assert f"base64.encode  1.0.0 → {version}  {phrase}" in text
        assert re.search(r"Status as of .+ \([0-9a-f]{40}\)\n$", text)
        unchanged(project, before)


@case("updates.fetch-before-first-success", "U11", "interface §3 fetch; Decisions Updates", "An unreachable feed reports failure and never instead of claiming up to date")
def fetch_never(ctx):
    result = ctx.call("fetch", env={"FVDEP_LIBRARY_URL": str(ctx.base / "unreachable")}).code(2)
    assert result.stdout == ""
    assert result.stderr.startswith("Fetch failed: ") and "Last successful fetch: never." in result.stderr
    assert "up to date" not in result.text.lower()


@case("updates.fetch-failed-keeps-last-time", "U11", "interface §§3/6; Decisions Lifecycle + profile evolution", "A failed fetch retains the last successful status snapshot and reports exit 2")
def fetch_keeps_last(ctx):
    root, _ = ctx.library()
    project = ctx.project()
    add_version(ctx, "1.1.0", compat=True)
    first = ctx.call("outdated", "--json", cwd=project).code(0).document()
    root.rename(root.with_name("hidden-library"))
    before = saved(project)
    result = ctx.call("outdated", "--json", cwd=project).code(2)
    second = result.document()
    assert second["error"]["code"] == "fetch_failed", second
    assert second["status"]["fetched"] == first["status"]["fetched"]
    assert second["status"]["commit"] == first["status"]["commit"]
    assert second["status"]["fetch_error"]
    assert second["result"]["modules"] == first["result"]["modules"]
    assert "Fetch failed:" in result.stderr and first["status"]["fetched"] in result.stderr
    unchanged(project, before)


@case("updates.upgrade-compat-pin-move", "U11", "Decisions Module updates; Public interface; interface §§3/6", "Proven compatibility transports the proof, moves the pin, and commits lock before manifest")
def upgrade_compat(ctx):
    project = ctx.project("honest-launch")
    ctx.call("lock", cwd=project).code(0)
    _, old_pin = ctx.library()
    head = add_version(ctx, "1.1.0", compat=True)
    document = ctx.call("upgrade", "base64.encode", "--json", cwd=project).code(0).document()
    assert document["result"]["library"] == {"from": old_pin, "to": head}
    assert [Path(path).name for path in document["result"]["wrote"]] == ["fvdep.lock", "fvdep.toml"]
    modules = document["result"]["modules"]
    assert len(modules) == 6 and all(m["verdict"] == "proven" for m in modules)
    assert next(m for m in modules if m["module"] == "base64.encode")["version"] == "1.1.0"
    status = ctx.call("status", "--json", cwd=project).code(0).document()
    assert all(m["delivered"] for m in status["result"]["modules"])


@case("updates.upgrade-refusal-byte-identity", "U11", "Decisions Proof policy; Data formats; interface §§2–3", "An incompatible target cannot change the manifest or lock")
def upgrade_refusal(ctx):
    project = ctx.project()
    ctx.call("lock", cwd=project).code(0)
    add_version(ctx, "2.0.0", changed=True)
    before = saved(project)
    ctx.call("upgrade", "base64.encode", "--to", "2.0.0", "--json", cwd=project).code(1).document()
    unchanged(project, before)


@case("updates.pin-move-rechecks-all", "U11", "Decisions Public interface; interface §3 upgrade", "A moved pin rechecks nontarget modules before committing anything")
def recheck_all(ctx):
    project = ctx.project("honest-launch")
    ctx.call("lock", cwd=project).code(0)
    add_version(ctx, "1.1.0", compat=True)
    proof = project / "Proof.lean"
    text = proof.read_text()
    old = "theorem compare_eq : @Impl.compare = @Fvdep.Semver.Compare.V1_0_0.compare := rfl"
    assert old in text
    proof.write_text(text.replace(old, "theorem compare_eq : True := True.intro"))
    before = saved(project)
    result = ctx.call("upgrade", "base64.encode", "--json", cwd=project).code(1)
    modules = checked_modules(result)
    failed = [m for m in modules if m["module"] == "semver.compare"]
    assert len(failed) == 1 and failed[0]["verdict"] == "not_proven", modules
    unchanged(project, before)


for replacement in ("1.1.0", None):
    suffix = "replacement" if replacement else "no-replacement"

    @case(f"updates.retraction.{suffix}", "U11", "Decisions Retraction; Lifecycle + profile evolution; interface §§3–6", f"A retraction with {suffix} preserves proof validity but removes delivery")
    def retraction(ctx, replacement=replacement):
        project = ctx.project()
        ctx.call("lock", cwd=project).code(0)
        if replacement:
            add_version(ctx, replacement, compat=True)
        add_notice(ctx, replacement=replacement)
        before = saved(project)
        ctx.call("fetch", cwd=project).code(0)
        status = ctx.call("status", "--json", cwd=project).code(1).document()
        assert status["result"]["modules"][0]["delivered"] is False
        assert status["result"]["modules"][0]["reason"]["code"] == "retracted"
        modules = checked_modules(ctx.call("check", "--json", cwd=project), 1)
        assert modules[0]["verdict"] == "proven" and modules[0]["policy_met"] is False
        assert modules[0]["retracted"] == {"reason": "acceptance retraction", "replacement": replacement}
        text = ctx.call("check", cwd=project).code(1).stdout
        assert text.startswith("PROVEN base64.encode@1.0.0 Impl.encode\n")
        ending = f"replacement {replacement}" if replacement else "no replacement"
        assert f"  not delivered: retracted (acceptance retraction); {ending}" in text
        unchanged(project, before)


@case("updates.development-retracted-proof", "U11", "interface §5", "Development policy accepts a retracted proof but still never delivers it")
def dev_retraction(ctx):
    project = ctx.project(policy="development")
    ctx.call("lock", cwd=project).code(0)
    add_notice(ctx, replacement=None)
    ctx.call("fetch", cwd=project).code(0)
    module = checked_modules(ctx.call("check", "--json", cwd=project), 0)[0]
    assert module["verdict"] == "proven" and module["policy_met"] is True and module["retracted"] is not None
    document = ctx.call("status", "--json", cwd=project).code(0).document()
    assert document["result"]["modules"][0]["delivered"] is False


@case("updates.status-test-evidence-before-retraction", "U11", "interface §3 status (LEAD-DIRECTIVES D4c)", "Test-only evidence is the single status reason before a simultaneous retraction")
def test_evidence_before_retraction(ctx):
    project = ctx.differential()
    ctx.call("lock", cwd=project).code(0)
    add_notice(ctx, replacement=None)
    ctx.call("fetch", cwd=project).code(0)
    before = saved(project)
    document = ctx.call("status", "--json", cwd=project).code(0).document()
    module = document["result"]["modules"][0]
    assert module["delivered"] is False and module["reason"]["code"] != "retracted", module
    lines = ctx.call("status", cwd=project).code(0).stdout.splitlines()
    status_lines = [line for line in lines if line.startswith("NOT DELIVERED base64.encode@1.0.0:")]
    assert status_lines == ["NOT DELIVERED base64.encode@1.0.0: test evidence only"], lines
    unchanged(project, before)


@case("updates.status-global-disagreement-first", "U11", "interface §§2–3 status (LEAD-DIRECTIVES D4c)", "An interrupted lock-before-manifest upgrade makes every module not delivered until repaired")
def global_disagreement_first(ctx):
    project = ctx.project("honest-launch")
    ctx.call("lock", cwd=project).code(0)
    old_manifest = (project / "fvdep.toml").read_bytes()
    add_version(ctx, "1.1.0", compat=True)
    ctx.call("upgrade", "base64.encode", "--json", cwd=project).code(0).document()
    # Both files are genuine outputs; restore the old manifest to model the
    # allowed interruption between the two atomic replacements.
    (project / "fvdep.toml").write_bytes(old_manifest)
    before = saved(project)
    document = ctx.call("status", "--json", cwd=project).code(1).document()
    modules = document["result"]["modules"]
    assert len(modules) == 6 and all(not module["delivered"] for module in modules)
    lines = ctx.call("status", cwd=project).code(1).stdout.splitlines()
    status_lines = [line for line in lines if line.startswith("NOT DELIVERED ")]
    assert len(status_lines) == 6 and all(": fvdep.lock and fvdep.toml disagree (" in line for line in status_lines), lines
    fresh = checked_modules(ctx.call("check", "--json", cwd=project), 0)
    assert len(fresh) == 6 and all(module["verdict"] == "proven" for module in fresh)
    unchanged(project, before)
    ctx.call("lock", cwd=project).code(0)
    repaired = ctx.call("status", "--json", cwd=project).code(0).document()
    assert all(module["delivered"] for module in repaired["result"]["modules"])


@case("updates.observed-retraction-persists", "U11", "Decisions Lifecycle + profile evolution", "A feed rollback cannot erase an already observed retraction")
def persistent_notice(ctx):
    root, original = ctx.library()
    project = ctx.project()
    ctx.call("lock", cwd=project).code(0)
    add_notice(ctx, replacement=None)
    ctx.call("fetch", cwd=project).code(0)
    ctx.git(root, "reset", "--hard", original)
    result = ctx.call("fetch", cwd=project)
    assert result.returncode in {0, 2}, result.text
    document = ctx.call("status", "--json", cwd=project).code(1).document()
    assert document["result"]["modules"][0]["reason"]["code"] == "retracted", document


@case("updates.default-skips-retracted-latest", "U11", "interface §3 upgrade", "The default upgrade target is the latest nonretracted version at the feed head")
def skip_retracted(ctx):
    project = ctx.project()
    add_version(ctx, "1.1.0", compat=True)
    add_version(ctx, "1.2.0", compat=True)
    add_notice(ctx, version="1.2.0", replacement="1.1.0")
    modules = checked_modules(ctx.call("upgrade", "base64.encode", "--json", cwd=project), 0)
    assert modules[0]["version"] == "1.1.0", modules


@case("updates.missing-lifecycle-schema", "U11", "Decisions Lifecycle + profile evolution (lifecycle-v<N>)", "A missing lifecycle-v1 feed is a fetch failure, not an empty status")
def missing_lifecycle(ctx):
    root, _ = ctx.library()
    ctx.call("fetch").code(0)
    path = root / "lifecycle-v1.json"
    assert path.is_file(), "schema-1 lifecycle feed missing from library"
    path.unlink()
    ctx.commit(root, "plant missing old-client lifecycle feed")
    result = ctx.call("fetch").code(2)
    assert "Fetch failed:" in result.stderr


@case("updates.diff-compat", "U11", "interface §3; Decisions Module updates", "diff reports the proven compatibility relation without changing the consumer")
def diff_compat(ctx):
    ctx.library()
    add_version(ctx, "1.1.0", compat=True)
    result = ctx.call("diff", "base64.encode", "1.0.0", "1.1.0").code(0)
    assert "same behaviour" in result.stdout.lower(), result.stdout


@case("updates.toolchain-refusal", "U8", "interface §1; Decisions Lifecycle + profile evolution", "A library on another Lean toolchain is refused before a project write")
def toolchain_refusal(ctx):
    root, _ = ctx.library()
    (root / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
    ctx.commit(root, "plant unsupported toolchain")
    result = ctx.call("init").code(2)
    assert re.search(r"Library commit [0-9a-f]{40} uses Lean .+; this fvdep checks Lean .+\. Install the matching fvdep or change the library pin\.\n", result.stderr), result.stderr
    assert not (ctx.base / "fvdep.toml").exists()
