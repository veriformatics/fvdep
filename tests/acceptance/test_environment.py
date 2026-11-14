"""Cache/source selection without reading consumer-vendored implementation code."""
import json
from pathlib import Path

from harness import case, raw_run, saved, unchanged


@case("environment.cache-precedence", "U8", "interface §1", "FVDEP_CACHE overrides XDG_CACHE_HOME and confines fvdep state to the test cache")
def cache_precedence(ctx):
    ctx.library()
    xdg = ctx.base / "xdg"
    ctx.call("list", "--json", env={"XDG_CACHE_HOME": str(xdg)}).code(0).document()
    assert Path(ctx.env["FVDEP_CACHE"]).is_dir()
    assert not (xdg / "fvdep").exists()


@case("environment.cache-xdg-default", "U8", "interface §1", "Without FVDEP_CACHE the state directory is XDG_CACHE_HOME/fvdep")
def cache_xdg(ctx):
    ctx.library()
    env = ctx.env.copy()
    env.pop("FVDEP_CACHE")
    env["XDG_CACHE_HOME"] = str(ctx.base / "xdg")
    raw_run([ctx.binary, "list", "--json"], cwd=ctx.base, env=env).code(0).document()
    assert (ctx.base / "xdg/fvdep").is_dir()
    assert not (ctx.base / "cache").exists()


@case("environment.library-offline-fallback", "U8", "interface §1 (library-reading commands)", "An offline library report uses its previously fetched head")
def library_offline(ctx):
    root, _ = ctx.library()
    first = ctx.call("list", "--json").code(0).document()["result"]
    root.rename(root.with_name("offline-library"))
    second = ctx.call("list", "--json").code(0).document()["result"]
    assert second == first


@case("environment.library-offline-no-head", "U8", "interface §1 (library-reading commands)", "An unreachable library without a cached head is a fetch failure")
def library_no_head(ctx):
    result = ctx.call("list", "--json", env={"FVDEP_LIBRARY_URL": str(ctx.base / "absent-library")}).code(2)
    value = result.document()
    assert value["error"]["code"] == "fetch_failed", value
    assert "Fetch failed" in result.stderr


@case("environment.consumer-lake-pin-warning", "U8", "interface §1; Decisions Conformance method", "A different consumer Lake requirement emits the exact warning but cannot change a verdict")
def lake_warning(ctx):
    project = ctx.project()
    root, pin = ctx.library()
    other = ctx.commit(root, "different consumer requirement")
    assert other != pin
    (project / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\npackage consumer\n'
        f'require fvdep from git "{root}" @ "{other}"\n')
    package = {"url": str(root), "type": "git", "subDir": None, "scope": "", "rev": other,
               "name": "fvdep", "manifestFile": "lake-manifest.json", "inputRev": other,
               "inherited": False, "configFile": "lakefile.lean"}
    (project / "lake-manifest.json").write_text(json.dumps({"version": "1.1.0", "name": "consumer",
                                                         "lakeDir": ".lake", "packagesDir": ".lake/packages",
                                                         "packages": [package]}) + "\n")
    before = saved(project)
    result = ctx.call("check", "--json", cwd=project).code(0)
    result.document()
    assert f"Your Lake package requires fvdep at {other}; fvdep checks {pin}. Update the requirement to {pin}.\n" in result.stderr, result.stderr
    unchanged(project, before)
