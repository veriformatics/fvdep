"""C1–C5/C9 library fixtures: one observation reused by each fixture's assertions."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import threading
from typing import Any, Callable

S = "Fvdep.Base64.Encode.V1_0_0"
E = "Fvdep.Registry.Base64.Encode.V1_0_0"
P = "FvdepProofs.Registry.Base64.Encode.V1_0_0"
R = "Fvdep.Registry.Types.V1"
TC = "leanprover/lean4:v4.35.0"


def register(ctx: Any) -> None:
    fx = ctx.fx
    def refusal(name: str, rule: str, reason: str, mutate: Callable[[Any], None],
                subject: str = "base64.encode@1.0.0") -> None:
        ctx.refusal_case("C1." + name, "F1", "C3 " + rule + "; C9", "Library error: " +
                         subject + ": " + reason + ".", mutate)
    def entry(**kwargs: Any) -> Callable[[Any], None]:
        return lambda lib: lib.entry(imports=[S, R, "Fvdep.Abi.V1_0_0"], **kwargs)
    refusal("v1.id", "V1", "the id is not canonical", entry(id="Base64.encode"), "Base64.encode@1.0.0")
    refusal("v1.version", "V1", "the version is not canonical", entry(version="01.0.0"),
            "base64.encode@01.0.0")
    refusal("v1.module", "V1", f"the entry is declared in {E}, not Fvdep.Registry.Other.Encode.V1_0_0",
            entry(id="other.encode"), "other.encode@1.0.0")
    for codepoint in (0, 10, 133):
        bad_id = "bad" + chr(codepoint) + ".encode"
        refusal(f"v1.id-control-{codepoint:02x}", "V1; D3 raw subject", "the id is not canonical",
                entry(id=bad_id), bad_id + "@1.0.0")
    bad_version = "1.0\n.0"
    refusal("v1.version-control", "V1; D3 raw subject", "the version is not canonical",
            entry(version=bad_version), "base64.encode@" + bad_version)
    refusal("v1.order", "V1 order", "the id is not canonical",
            entry(id="Bad.encode", version="01.0.0"), "Bad.encode@01.0.0")
    refusal("v2.repeated-id", "V2", "listed twice", lambda lib: lib.registry([E, E]))
    def unlisted(lib: Any) -> None:
        lib.add_version("2.0.0")
        lib.add_version("1.0.1")
    refusal("v2.unlisted", "V2 path order", "its entry module Fvdep/Registry/Base64/Encode/V1_0_1.lean "
            "is not listed in Fvdep.Registry.modules", unlisted, "base64.encode@1.0.1")
    refusal("v3.foreign-spec", "V3", f"the spec Nat.add is not a definition in {S}",
            entry(spec="Nat.add"))
    def theorem_spec(lib: Any) -> None:
        lib.spec(f'''namespace {S}
theorem encode : True := True.intro
def bits : Prop := True
def length : Prop := True
end {S}
''')
    refusal("v3.theorem-spec", "V3 order", f"the spec {S}.encode is not a definition in {S}", theorem_spec)
    def bad_type(lib: Any) -> None:
        lib.spec(f'''namespace {S}
def encode : Nat := 0
def bits : Prop := True
def length : Prop := True
end {S}
''')
    refusal("v3.type", "V3", f"the spec type of {S}.encode is not encodable", bad_type)
    flags = {
        "partial": ("partial def helper : List UInt8 → List Char\n"
                    "  | [] => []\n"
                    "  | _ :: xs => helper xs\n"
                    "def encode (x : List UInt8) : List Char := helper x\n", "helper"),
        "unsafe": ("unsafe def encode (_ : List UInt8) : List Char := []\n", "encode"),
        "implemented_by": ("def alternate (_ : List UInt8) : List Char := []\n"
                           "@[implemented_by alternate] def helper (_ : List UInt8) : List Char := []\n"
                           "def encode (x : List UInt8) : List Char := helper x\n", "helper"),
        "extern": ('@[extern "fvdep_index_test_extern"] def helper (_ : List UInt8) : List Char := []\n'
                   "def encode (x : List UInt8) : List Char := helper x\n", "helper"),
        "opaque": ("opaque helper : List Char := []\n"
                   "def encode (_ : List UInt8) : List Char := helper\n", "helper"),
        "noncomputable": ("noncomputable def encode (_ : List UInt8) : List Char :=\n"
                          "  Classical.choice (inferInstance : Nonempty (List Char))\n", "encode"),
    }
    for flag, (body, offender) in flags.items():
        def mutate(lib: Any, body: str = body) -> None:
            lib.spec(f"namespace {S}\n" + body +
                     f"def bits : Prop := True\ndef length : Prop := True\nend {S}\n")
        refusal("v3." + flag, "V3 roots + transitive flags", f"{S}.{offender} is {flag}", mutate)
    def abi_flag(lib: Any) -> None:
        path = lib.root / "Fvdep/Abi/V1_0_0.lean"
        path.write_text(path.read_text() + '''\nnamespace Fvdep.Abi.V1_0_0
def alternate (_ : List UInt8 → List Char) (b : ByteArray) : ByteArray := b
@[implemented_by alternate] def flagged (_ : List UInt8 → List Char)
    (b : ByteArray) : ByteArray := b
end Fvdep.Abi.V1_0_0
''')
        lib.entry(abi="Fvdep.Abi.V1_0_0.flagged")
    refusal("v3.abi-root", "V3 ABI roots", "Fvdep.Abi.V1_0_0.flagged is implemented_by", abi_flag)
    refusal("v4.not-prop", "V4", f"the obligation {S}.encode is not a Prop definition in {S}",
            entry(obligations=[S + ".encode"]))
    def obligation_theorem(lib: Any) -> None:
        path = lib.root / "Fvdep/Base64/Encode/V1_0_0.lean"
        path.write_text(path.read_text() + f"\nnamespace {S}\ntheorem fact : True := True.intro\nend {S}\n")
        lib.entry(obligations=[S + ".fact"])
    refusal("v4.theorem", "V4", f"the obligation {S}.fact is not a Prop definition in {S}", obligation_theorem)
    refusal("v4.foreign", "V4", f"the obligation True is not a Prop definition in {S}",
            entry(obligations=["True"]))
    refusal("v4.repeat", "V4", f"the obligation {S}.bits is listed twice",
            entry(obligations=[S + ".bits", S + ".bits"]))
    refusal("v5.module", "V5", f"the ABI shape {S}.encode is not a definition in a "
            "Fvdep.Abi.V<x>_<y>_<z> module", entry(abi=S + ".encode"))
    def abi_type(lib: Any) -> None:
        path = lib.root / "Fvdep/Abi/V1_0_0.lean"
        path.write_text(path.read_text() + '''\nnamespace Fvdep.Abi.V1_0_0
def wrong (_ : List UInt8 → List Char) (n : Nat) : Nat := n
end Fvdep.Abi.V1_0_0
''')
        lib.entry(abi="Fvdep.Abi.V1_0_0.wrong")
    refusal("v5.type", "V5", "the ABI shape Fvdep.Abi.V1_0_0.wrong does not take the spec to "
            "ByteArray → ByteArray or ByteArray → Option ByteArray", abi_type)
    for label, value in (("unlisted", "0.0.0"), ("same", "1.0.0"), ("bad", "01.0.0")):
        refusal("v6." + label, "V6", f"compat {value} is not an earlier listed version", entry(compat=value))
    def different_type(lib: Any) -> None:
        new = lib.add_version("2.0.0", compat="1.0.0", valid_proof=False, spec_type="Nat → Nat")
        lib.registry([E, new])
    refusal("v6.type", "V6", "compat 1.0.0 has another spec type", different_type,
            "base64.encode@2.0.0")
    def unversioned(lib: Any) -> None:
        fx.write(lib.root, "Fvdep.Unversioned", "def fixtureHelper : Nat := 0\n")
        path = lib.root / "Fvdep/Base64/Encode/V1_0_0.lean"
        path.write_text("import Fvdep.Unversioned\n" + path.read_text())
    refusal("v7.holds", "V7", "its closure holds Fvdep.Unversioned", unversioned)
    def foreign_import(lib: Any) -> None:
        path = lib.root / "Fvdep/Base64/Encode/V1_0_0.lean"
        path.write_text("import Lean\n" + path.read_text())
    refusal("v7.imports", "V7", "its closure imports Lean", foreign_import)
    def linked(lib: Any, hard: bool = False) -> None:
        path = lib.root / "Fvdep/Base64/Encode/V1_0_0.lean"
        original = lib.root / "fixture-original.lean"
        path.rename(original)
        if hard:
            os.link(original, path)
        else:
            path.symlink_to(original)
    for hard in (False, True):
        refusal("c4." + ("alias" if hard else "link"), "C4",
                f"the closure module {S} is not a regular file at Fvdep/Base64/Encode/V1_0_0.lean",
                lambda lib, hard=hard: linked(lib, hard))
    def two_errors(lib: Any, reverse: bool = False) -> None:
        new = lib.add_version("1.0.1")
        lib.entry(id="Bad.encode")
        s = "Fvdep.Base64.Encode.V1_0_1"
        lib.entry(module=new, spec=s + ".encode", version="1.0.1", obligations=[s + ".encode"])
        lib.registry([new, E] if reverse else [E, new])
    refusal("entry-order.first", "C9 entry order", "the id is not canonical", two_errors,
            "Bad.encode@1.0.0")
    refusal("entry-order.reversed", "C9 entry order", "the obligation Fvdep.Base64.Encode.V1_0_1.encode "
            "is not a Prop definition in Fvdep.Base64.Encode.V1_0_1",
            lambda lib: two_errors(lib, True), "base64.encode@1.0.1")
    def profile(lib: Any) -> None:
        lib.registry([E], profiles='[{ id := "npm:fixture@1", version := "1.0.0" }]')
    refusal("v10.profiles", "V10", "profiles are not indexed yet", profile, "Fvdep.Registry.profiles")

    # F7 presence + toolchain, including chain precedence + no-write effects.
    absent = 'No fvdep library found here. Run "fvdep index" in a library working copy.'
    for part in ("lean-toolchain", "Fvdep/Registry.lean"):
        def remove(lib: Any, part: str = part) -> None:
            (lib.root / part).unlink()
        ctx.refusal_case("C7.absent." + part.replace("/", "-"), "F7", "C1/C9 presence", absent,
                         remove, preflight=False)
    def missing_beats_toolchain(lib: Any) -> None:
        (lib.root / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
        (lib.root / "Fvdep/Registry.lean").unlink()
    ctx.refusal_case("C7.presence-before-toolchain", "F7", "C9 precedence", absent,
                     missing_beats_toolchain, preflight=False)
    def wrong_toolchain(lib: Any) -> None:
        (lib.root / "lean-toolchain").write_text(" \nleanprover/lean4:v0.0.0\n\t")
        (lib.root / "Fvdep/Base64/Encode/V1_0_0.lean").write_text("this cannot compile\n")
    def control_toolchain(lib: Any) -> None:
        (lib.root / "lean-toolchain").write_text("leanprover/lean4:v0\x85.0.0\n")
    ctx.refusal_case("C7.toolchain-control", "F7", "C1/C9; D3 line escaping",
                     f"This library uses Lean leanprover/lean4:v0\x85.0.0; this fvdep checks Lean {TC}. "
                     "Install the matching fvdep.", control_toolchain, preflight=False)
    ctx.refusal_case("C7.toolchain-before-build", "F7", "C1/C9 toolchain + trim",
                     f"This library uses Lean leanprover/lean4:v0.0.0; this fvdep checks Lean {TC}. "
                     "Install the matching fvdep.", wrong_toolchain, preflight=False)

    # F8 build, unknown registry forms, load primitive failure.
    def broken(lib: Any) -> None:
        (lib.root / "Fvdep/Base64/Encode/V1_0_0.lean").write_text("def broken : Nat := missingFixtureName\n")
    def build_failure() -> None:
        obs = ctx.observe("build-failure", broken, preflight=False)
        ctx.eq(obs.proc.returncode, 2, "build failure exit")
        ctx.eq(obs.proc.stdout, b"", "build failure stdout")
        last = obs.proc.stderr.decode(errors="replace").splitlines()[-1:]
        ctx.eq(bool(last and last[0].startswith("Build failed: ") and
                    "Fvdep/Base64/Encode/V1_0_0.lean" in last[0]), True,
               "fixed build prefix + source-relative path")
        ctx.eq(obs.after, obs.before, "build failure unchanged")
    ctx.add("C8.build", "F8", "C1/C9 build", build_failure)
    for field in ("modules", "notices", "removed"):
        def unreadable(lib: Any, field: str = field) -> None:
            if field == "modules":
                lib.registry([E], expression=f"([{E}.entry] : List {R}.Module).reverse")
            elif field == "notices":
                lib.notices([], expression=f"([] : List {R}.Notice).reverse")
            else:
                lib.removed([], expression=f"([] : List {R}.Removed).reverse")
        ctx.refusal_case("C8.form." + field, "F8", "C2/C9 registry form",
                         f"The registry uses a form fvdep cannot read: Fvdep.Registry.{field}.", unreadable)
    def root_helper(lib: Any) -> None:
        lib.registry([E], prefix=f"def chunk : List {R}.Module := [{E}.entry].reverse",
                     expression="chunk")
    ctx.refusal_case("C8.form.root-helper", "F8", "C2/C9 reached constant",
                     "The registry uses a form fvdep cannot read: Fvdep.Registry.chunk.", root_helper)
    def entry_form(lib: Any) -> None:
        path = lib.root / "Fvdep/Registry/Base64/Encode/V1_0_0.lean"
        text = path.read_text().replace("def entry :", "def literal :")
        text += f"\nnamespace {E}\ndef entry : {R}.Module := Id.run do return literal\nend {E}\n"
        path.write_text(text)
    ctx.refusal_case("C8.form.entry", "F8", "C2/C9 entry form",
                     f"The registry uses a form fvdep cannot read: {E}.entry.", entry_form)
    def inline_entry(lib: Any) -> None:
        lib.registry([E], expression=f'''[{{
  id := "base64.encode"
  version := "1.0.0"
  spec := ``{S}.encode
  obligations := [``{S}.bits, ``{S}.length]
  abi := none
  compat := none
}}]''')
    ctx.refusal_case("C8.d4.inline-entry", "F8", "C2/C9; D4 entry references only",
                     "The registry uses a form fvdep cannot read: Fvdep.Registry.modules.", inline_entry)
    def outside_helper(lib: Any) -> None:
        ctx.fx.write(lib.root, "Fvdep.Registry.Notices", f'''import {R}
namespace Fvdep.Registry
def foreignChunk : List {R}.Notice := []
def notices : List {R}.Notice := foreignChunk
end Fvdep.Registry
''')
    ctx.refusal_case("C8.d4.outside-helper", "F8", "C2/C9; D4 module-of-origin boundary",
                     "The registry uses a form fvdep cannot read: Fvdep.Registry.notices.", outside_helper)
    for first in ("modules", "profiles", "notices"):
        def read_order(lib: Any, first: str = first) -> None:
            modules = f"[{E}.entry].reverse" if first == "modules" else f"[{E}.entry]"
            profiles = ("([] : List Fvdep.Registry.ProfileTypes.V1.Profile).reverse"
                        if first in ("modules", "profiles") else "[]")
            lib.registry([E], expression=modules, profiles=profiles)
            lib.notices([], expression=f"([] : List {R}.Notice).reverse")
            lib.removed([], expression=f"([] : List {R}.Removed).reverse")
            lib.entry(id="Bad.encode")
        ctx.refusal_case("C8.d4.order-" + first, "F8", "C2/C9; D4 read order before V1",
                         f"The registry uses a form fvdep cannot read: Fvdep.Registry.{first}.", read_order)
    def changed_layout(lib: Any) -> None:
        path = lib.root / "Fvdep/Registry/Types/V1.lean"
        source = path.read_text().replace("  id : String\n  version : String\n  spec : Lean.Name",
                                          "  version : String\n  id : String\n  spec : Lean.Name", 1)
        path.write_text(source)
    ctx.refusal_case("C8.form.type-layout", "F8", "C2/C9 structure fields + certificate",
                     "The registry uses a form fvdep cannot read: Fvdep.Registry.modules.", changed_layout)
    def profile_element(lib: Any) -> None:
        lib.registry([E], profiles='[Id.run do return { id := "npm:fixture@1", version := "1.0.0" }]')
    ctx.refusal_case("C8.form.profile-elements", "F8", "C2 profiles elements unread; C3 V10; C9",
                     "Library error: Fvdep.Registry.profiles: profiles are not indexed yet.", profile_element)
    def load_failure() -> None:
        lib = ctx.library("load-failure")
        ctx.build_fixture(lib)
        path = lib.root / "index.json"
        path.write_bytes(b"load sentinel\n")
        env = {"LD_PRELOAD": str(ctx.here / ".build/fault.so"), "FVDEP_INDEX_FAULT": "load",
               "FVDEP_INDEX_FAULT_ROOT": str(lib.root), "FVDEP_INDEX_FAULT_HIT": str(lib.root / "fault.hit")}
        proc = ctx.call(lib.root, ["index"], env=env)
        ctx.eq(proc.returncode, 2, "load exit")
        ctx.eq(proc.stdout, b"", "load stdout")
        last = proc.stderr.decode(errors="replace").splitlines()[-1:]
        ctx.eq(bool(last and last[0].startswith("Could not load the built library: ") and
                    last[0].endswith(".")), True, "fixed load line")
        ctx.eq(path.read_bytes(), b"load sentinel\n", "load failure no write")
    ctx.add("C8.load", "F8", "C1/C9 load", load_failure)

    register_status(ctx)
    register_compat_notices(ctx)
    register_identity_purity(ctx)
    register_cli_schema(ctx)


def register_status(ctx: Any) -> None:
    variants = ["proven", "sorry", "custom", "missing-registry", "unreadable", "unmapped",
                "twice", "not-theorem", "outside", "wrong-statement"]
    for variant in variants:
        def mutate(lib: Any, variant: str = variant) -> None:
            if variant == "missing-registry":
                (lib.root / (P.replace(".", "/") + ".lean")).unlink()
                (lib.root / "FvdepProofs.lean").write_text("/-! No proof registry. -/\n")
                return
            if variant == "proven":
                return
            if variant == "custom":
                lib.spec(f'''namespace {S}
def encode (_ : List UInt8) : List Char := []
def bits : Prop := True ∧ True
def length : Prop := True
end {S}
''')
                body = f"axiom zed : True\naxiom alpha : True\ntheorem bits : {S}.bits := ⟨zed, alpha⟩\n"
            elif variant == "sorry":
                body = f"set_option warningAsError false\ntheorem bits : {S}.bits := by sorry\n"
            elif variant == "not-theorem":
                body = f"set_option warningAsError false\ndef bits : {S}.bits := True.intro\n"
            elif variant == "wrong-statement":
                body = "theorem bits : True := True.intro\n"
            else:
                body = f"theorem bits : {S}.bits := True.intro\n"
            if variant == "outside":
                path = lib.root / "Fvdep/Base64/Encode/V1_0_0.lean"
                path.write_text(path.read_text() +
                                f"\nnamespace {S}\ntheorem outside : bits := True.intro\nend {S}\n")
            pairs = f"[(``{S}.bits, ``{S + '.outside' if variant == 'outside' else P + '.bits'}), "
            pairs += f"(``{S}.length, ``{P}.length)]"
            if variant == "unmapped":
                pairs = f"[(``{S}.length, ``{P}.length)]"
            if variant == "twice":
                pairs = f"[(``{S}.bits, ``{P}.bits), (``{S}.bits, ``{P}.length), (``{S}.length, ``{P}.length)]"
            expression = f"{{ obligations := {pairs}, compat := none }}"
            if variant == "unreadable":
                expression = "Id.run do return " + expression
            lib.proofs(source=f'''import {E}
namespace {P}
{body}theorem length : {S}.length := True.intro
def proofs : {R}.Proofs := {expression}
end {P}
''')
        get = lambda variant=variant, mutate=mutate: ctx.observe("status-" + variant, mutate)
        status = "proven" if variant == "proven" else "trusts" if variant == "custom" else "open"
        axioms = [P + ".alpha", P + ".zed"] if variant == "custom" else ["sorryAx"] if variant == "sorry" else []
        def check(get: Callable[[], Any] = get, status: str = status,
                  axioms: list[str] = axioms, variant: str = variant) -> None:
            item = ctx.op(get())
            expected = [{"name": "bits", "status": status, "axioms": axioms},
                        {"name": "length", "status": "open" if variant in ("missing-registry", "unreadable") else "proven",
                         "axioms": []}]
            ctx.eq(item.get("obligations"), expected, "obligation status + full axiom names")
        ctx.add("C3.status." + variant, "F3", "C5/C6 derived status", check)
        why = {
            "missing-registry": "no proof registry", "unreadable": "its proof registry cannot be read",
            "unmapped": "no theorem is mapped", "twice": "two theorems are mapped",
            "not-theorem": P + ".bits is not a theorem", "outside": S + ".outside is outside FvdepProofs",
            "wrong-statement": P + ".bits proves another statement",
        }.get(variant)
        def warning(get: Callable[[], Any] = get, why: str | None = why,
                    variant: str = variant) -> None:
            obs = get()
            ctx.eq(obs.proc.returncode, 0, "warning does not change exit")
            lines = [line for line in obs.proc.stderr.decode(errors="replace").splitlines()
                     if line.startswith("Warning: ")]
            wanted = [] if why is None else [f"Warning: base64.encode@1.0.0: obligation {S}.bits "
                                             f"counts as open: {why}."]
            if variant in ("missing-registry", "unreadable"):
                wanted.append(f"Warning: base64.encode@1.0.0: obligation {S}.length counts as open: {why}.")
            ctx.eq(lines, wanted, "warning lines + order")
        ctx.add("C3.warning." + variant, "F3", "C5/C9 warnings + order", warning)
    def warning_order() -> None:
        def mutate(lib: Any) -> None:
            old_entry = lib.add_version("0.9.0")
            old_spec = "Fvdep.Base64.Encode.V0_9_0"
            lib.spec(f'''namespace {old_spec}
def encode (_ : List UInt8) : List Char := []
def bits : Prop := True
def length : Prop := True
end {old_spec}
''', old_spec)
            lib.entry(compat="0.9.0")
            lib.registry([E, old_entry])
            for module in (P, "FvdepProofs.Registry.Base64.Encode.V0_9_0"):
                (lib.root / (module.replace(".", "/") + ".lean")).unlink()
            (lib.root / "FvdepProofs.lean").write_text("/-! No proof registries. -/\n")
        obs = ctx.observe("warning-order", mutate)
        ctx.eq(obs.proc.returncode, 0, "warnings preserve exit")
        lines = [line for line in obs.proc.stderr.decode(errors="replace").splitlines()
                 if line.startswith("Warning: ")]
        wanted = [f"Warning: base64.encode@1.0.0: obligation {S}.{name} counts as open: no proof registry."
                  for name in ("bits", "length")]
        wanted.append("Warning: base64.encode@1.0.0: compat counts as open: no proof registry.")
        wanted.extend(f"Warning: base64.encode@0.9.0: obligation Fvdep.Base64.Encode.V0_9_0.{name} "
                      "counts as open: no proof registry." for name in ("bits", "length"))
        ctx.eq(lines, wanted, "registry entry order, obligation order, then compat")
    ctx.add("C3.warning.registry-order", "F3", "C5/C9 full warning order", warning_order)
    def forged(lib: Any) -> None:
        lib.spec(f'''namespace {S}
def encode (_ : List UInt8) : List Char := []
def bits : Prop := False
def length : Prop := True
end {S}
''')
        lib.proofs(source=f'''import {E}
import Lean
set_option debug.skipKernelTC true
open Lean Elab Command in
run_cmd liftCoreM <| addDecl (.thmDecl {{
  name := `{P}.bits
  levelParams := []
  type := mkConst ``{S}.bits
  value := mkConst ``True.intro
}})
namespace {P}
theorem length : {S}.length := True.intro
def proofs : {R}.Proofs := {{
  obligations := [(``{S}.bits, ``{P}.bits), (``{S}.length, ``{P}.length)]
  compat := none }}
end {P}
''')
    def replay() -> None:
        obs = ctx.observe("forged-replay", forged)
        ctx.eq(obs.proc.returncode, 2, "forged kernel term exit")
        ctx.eq(obs.proc.stdout, b"", "replay refusal stdout")
        last = obs.proc.stderr.decode(errors="replace").splitlines()[-1:]
        prefix = f"Kernel replay rejected {P}: "
        ctx.eq(bool(last and last[0].startswith(prefix)), True, "replay module + fixed prefix")
        ctx.eq(obs.after, obs.before, "replay refusal no write")
    ctx.add("C3.replay.forged", "F3", "C1/C5/C9 replay", replay)


def register_compat_notices(ctx: Any) -> None:
    fx = ctx.fx
    for mode in ("proven", "wrong", "unmapped", "ignored"):
        def mutate(lib: Any, mode: str = mode) -> None:
            older = lib.add_version("0.9.0")
            old_spec = "Fvdep.Base64.Encode.V0_9_0"
            lib.spec(f'''namespace {old_spec}
def encode (_ : List UInt8) : List Char := []
def bits : Prop := True
def length : Prop := True
end {old_spec}
''', old_spec)
            lib.registry([older, E])
            lib.entry(compat=None if mode == "ignored" else "0.9.0")
            statement = "True" if mode == "wrong" else f"@{S}.encode = @{old_spec}.encode"
            term = "True.intro" if mode == "wrong" else "rfl"
            compat = "none" if mode == "unmapped" else f"some ``{P}.compatible"
            lib.proofs(source=f'''import {E}
import {older}
namespace {P}
theorem bits : {S}.bits := True.intro
theorem length : {S}.length := True.intro
theorem compatible : {statement} := {term}
def proofs : {R}.Proofs := {{
  obligations := [(``{S}.bits, ``{P}.bits), (``{S}.length, ``{P}.length)]
  compat := {compat} }}
end {P}
''')
        get = lambda mode=mode, mutate=mutate: ctx.observe("compat-" + mode, mutate)
        def edge(get: Callable[[], Any] = get, mode: str = mode) -> None:
            item = ctx.op(get())
            want = None if mode == "ignored" else {"version": "0.9.0", "axioms": [],
                                                    "status": "proven" if mode == "proven" else "open"}
            ctx.eq(item.get("compat"), want, "declared compatibility status")
        ctx.add("C4.compat." + mode, "F4", "C5/C6 compat", edge)
        def warning(get: Callable[[], Any] = get, mode: str = mode) -> None:
            obs = get()
            ctx.eq(obs.proc.returncode, 0, "compat warning exit")
            lines = [x for x in obs.proc.stderr.decode(errors="replace").splitlines() if x.startswith("Warning: ")]
            theorem = P + ".compatible"
            want = []
            if mode == "wrong":
                want = [f"Warning: base64.encode@1.0.0: compat counts as open: {theorem} proves another statement."]
            elif mode == "unmapped":
                want = ["Warning: base64.encode@1.0.0: compat counts as open: no theorem is mapped."]
            elif mode == "ignored":
                want = [f"Warning: base64.encode@1.0.0: the compat theorem {theorem} is ignored: no compat is declared."]
            ctx.eq(lines, want, "compat warning exact line")
        ctx.add("C4.warning." + mode, "F4", "C9 compat warning", warning)
    def notice_refuse(label: str, reason: str, mutate: Callable[[Any], None],
                      subject: str = "base64.encode@1.0.0") -> None:
        ctx.refusal_case("C5." + label, "F5", "C3 V8/V9; C9",
                         f"Library error: {subject}: {reason}.", mutate)
    notice_refuse("notice.unknown", "the notice names no listed or removed entry",
                  lambda lib: lib.notices([fx.notice(id="other.encode")]), "other.encode@1.0.0")
    notice_refuse("notice.replacement", "the notice replacement 2.0.0 is not a listed or removed version of base64.encode",
                  lambda lib: lib.notices([fx.notice(replacement="2.0.0")]))
    for label, reason in (("empty", ""), ("control", "bad\nreason"), ("del", "bad\x7f"),
                          ("nel", "bad\x85reason"),
                          ("large", "x" * 65537), ("multibyte-large", "é" * 32769)):
        notice_refuse("notice.reason." + label,
                      "the notice reason must be 1 to 65536 UTF-8 bytes without control characters",
                      lambda lib, reason=reason: lib.notices([fx.notice(reason=reason)]))
    for label in ("listed", "duplicate", "kind", "digest", "lastCommit", "toolchain", "notice"):
        def mutate(lib: Any, label: str = label) -> None:
            record = {"id": "other.encode", "version": "1.0.0", "digest": "1" * 64,
                      "lastCommit": "2" * 40, "toolchain": TC, "kind": "operation"}
            if label == "listed":
                record["id"] = "base64.encode"
            if label == "kind":
                record["kind"] = "profile"
            if label == "digest":
                record["digest"] = "A" * 64
            if label == "lastCommit":
                record["lastCommit"] = "A" * 40
            if label == "toolchain":
                record["toolchain"] = ""
            lib.removed([record, record] if label == "duplicate" else [record])
            if label != "notice":
                lib.notices([fx.notice(id=record["id"])])
        reasons = {
            "listed": "the removed record is still listed", "duplicate": "the removed record is recorded twice",
            "kind": "the removed record must have kind operation", "digest": "the removed digest must be 64 lowercase hex digits",
            "lastCommit": "the removed lastCommit must be 40 lowercase hex digits",
            "toolchain": "the removed toolchain must not be empty", "notice": "no notice names the removed record"}
        notice_refuse("removed." + label, reasons[label], mutate,
                      "base64.encode@1.0.0" if label == "listed" else "other.encode@1.0.0")
    def logs(lib: Any) -> None:
        removed = [{"id": id, "version": "1.0.0", "digest": "1" * 64,
                    "lastCommit": "2" * 40, "toolchain": TC, "kind": "operation"}
                   for id in ("zed.encode", "other.encode")]
        lib.removed(removed)
        lib.notices([fx.notice(reason="z first"), fx.notice(id="zed.encode", reason="m second"),
                     fx.notice(id="other.encode", reason="a third")])
    def log_order() -> None:
        obs = ctx.observe("notice-order", logs)
        value = ctx.document(obs)
        ctx.eq(value.get("notices"), [fx.notice(reason="z first"), fx.notice(id="zed.encode", reason="m second"),
                                     fx.notice(id="other.encode", reason="a third")], "notice registry order")
        ctx.eq(value.get("removed"), [fx.removed_record(id=id) for id in ("zed.encode", "other.encode")],
               "removed field spellings + registry order")
    ctx.add("C5.logs.order", "F5", "C6 registry log order", log_order)
    def cap_reason(lib: Any) -> None:
        lib.notices([fx.notice(reason="é" * 32768)])
    def cap() -> None:
        value = ctx.document(ctx.observe("notice-cap", cap_reason))
        ctx.eq(value.get("notices"), [fx.notice(reason="é" * 32768)], "65536 UTF8 bytes kept whole")
    ctx.add("C5.notice.cap", "F5", "C3 V8/C6 bound", cap)


def register_identity_purity(ctx: Any) -> None:
    def exact_frames() -> None:
        lib = ctx.library("exact-frames")
        ctx.build_fixture(lib)
        files = [module.replace(".", "/") + ".lean" for module in (S, E, R)]
        def u64(n: int) -> bytes:
            return n.to_bytes(8, "big")
        for step in range(4):
            if step:
                path = lib.root / files[step - 1]
                path.write_bytes(path.read_bytes() + b"\n-- framed byte perturbation\n")
            tag = b"fvdep/entry/1"
            framed = u64(len(tag)) + tag + u64(len(files))
            for name in sorted(files, key=lambda name: name.encode()):
                data = (lib.root / name).read_bytes()
                path_bytes = name.encode()
                framed += u64(len(path_bytes)) + path_bytes + u64(len(data)) + data
            proc = ctx.call(lib.root, ["index"])
            ctx.need(proc.returncode == 0, "reference digest index unavailable")
            value = json.loads((lib.root / "index.json").read_bytes())
            item = next(x for x in value["operations"] if x["id"] == "base64.encode")
            ctx.eq(item["digest"], hashlib.sha256(framed).hexdigest(),
                   f"independent entry framing + SHA256, closure perturbation {step}")
    ctx.add("C2.identity.reference-frames", "F2", "C4; U3 H2/H3",
            exact_frames, "minimal known three-file closure; baseline + each file perturbed")
    def identity() -> dict[str, Any]:
        lib = ctx.library("identity", launch=True)
        ctx.build_fixture(lib)
        def snapshot() -> tuple[dict[tuple[str, str], str], bytes]:
            proc = ctx.call(lib.root, ["index"])
            ctx.need(proc.returncode == 0, f"identity index exit {proc.returncode}")
            data = (lib.root / "index.json").read_bytes()
            value = json.loads(data)
            return {(x["id"], x["version"]): x["digest"] for x in value["operations"]}, data
        baseline, raw = snapshot()
        proof = lib.root / "FvdepProofs/Registry/Base64/Encode/V1_0_0.lean"
        proof.write_text(proof.read_text() + "\n-- proof bytes excluded\n")
        proof_changed, _ = snapshot()
        source = lib.root / "Fvdep/Base64/Encode/V1_0_0.lean"
        source.write_text(source.read_text() + "\n-- a source-closure comment byte\n")
        source_changed, _ = snapshot()
        shared = lib.root / "Fvdep/Base64/Rfc4648/V1_0_0.lean"
        shared.write_text(shared.read_text() + "\n-- shared source-closure bytes\n")
        shared_changed, _ = snapshot()
        return {"base": baseline, "proof": proof_changed, "source": source_changed,
                "shared": shared_changed, "raw": raw}
    get = lambda: ctx.shared("identity-sequence", identity)
    def changed() -> None:
        item = get()
        ctx.eq(item["source"].get(("base64.encode", "1.0.0")) != item["proof"].get(("base64.encode", "1.0.0")),
               True, "closure comment byte changes digest")
    ctx.add("C2.identity.comment", "F2", "C4 byte sensitivity", changed)
    ctx.add("C2.identity.proof", "F2", "C4 proof exclusion",
            lambda: ctx.eq(get()["base"], get()["proof"], "proof bytes do not change identities"))
    def shared_change() -> None:
        item = get()
        changed_ids = {key[0] for key, value in item["source"].items() if item["shared"].get(key) != value}
        ctx.eq(changed_ids, {"base64.encode", "base64.decode", "base64.encode_url", "base64.decode_url"},
               "exact shared-module importer set")
    ctx.add("C2.identity.shared", "F2", "C4 shared closure", shared_change)
    def unaffected() -> None:
        item = get()
        changed_ids = {key[0] for key, value in item["proof"].items() if item["source"].get(key) != value}
        ctx.eq(changed_ids, {"base64.encode", "base64.decode"},
               "Decode imports Encode; no unrelated closure changes")
    ctx.add("C2.identity.closure-boundary", "F2", "C4 dependency closure", unaffected)
    def unrelated() -> tuple[str, str, bool]:
        lib = ctx.library("identity-unrelated")
        ctx.build_fixture(lib)
        first = ctx.call(lib.root, ["index"])
        ctx.need(first.returncode == 0, "first index unavailable")
        values = json.loads((lib.root / "index.json").read_bytes())["operations"]
        old = next(x["digest"] for x in values if x["id"] == "base64.encode" and x["version"] == "1.0.0")
        new = lib.add_version("1.0.1")
        lib.registry([E, new])
        second = ctx.call(lib.root, ["index"])
        ctx.need(second.returncode == 0, "second index unavailable")
        values = json.loads((lib.root / "index.json").read_bytes())["operations"]
        item = next(x for x in values if x["id"] == "base64.encode" and x["version"] == "1.0.0")
        return old, item["digest"], any(x["id"] == "base64.encode" and x["version"] == "1.0.1" for x in values)
    uget = lambda: ctx.shared("unrelated-sequence", unrelated)
    ctx.add("C2.identity.unrelated", "F2", "C4 independent entry",
            lambda: ctx.eq(uget()[0], uget()[1], "unrelated version addition keeps old digest"))
    ctx.add("C12.schema.new-version-after-index", "F12", "C1 fresh build; C6 registry completeness",
            lambda: ctx.eq(uget()[2], True, "new registry entry appears after an earlier index run"))
    def alternate_root(lib: Any) -> None:
        path = lib.root / "Fvdep/Base64"
        path.rename(lib.root / "alternate-base64")
        path.symlink_to(lib.root / "alternate-base64", target_is_directory=True)
    ctx.refusal_case("C2.identity.alternate-root", "F2", "C4 canonical source path",
                     f"Library error: base64.encode@1.0.0: the closure module {S} is not a regular file at "
                     "Fvdep/Base64/Encode/V1_0_0.lean.", alternate_root)
    def purity() -> dict[str, Any]:
        lib = ctx.library("purity", launch=True)
        ctx.build_fixture(lib)
        proc = ctx.call(lib.root, ["index"])
        ctx.need(proc.returncode == 0, "purity initial index unavailable")
        path = lib.root / "index.json"
        initial = path.read_bytes()
        again = ctx.call(lib.root, ["index"])
        repeated = path.read_bytes()
        checked = ctx.call(lib.root, ["index", "--check"])
        after_check = path.read_bytes()
        changed = initial + b" "
        path.write_bytes(changed)
        drift = ctx.call(lib.root, ["index", "--check"])
        after_drift = path.read_bytes()
        path.unlink()
        absent = ctx.call(lib.root, ["index", "--check"])
        absent_stayed = not path.exists()
        planted = lib.root / ".lake/fvdep-index/.lake/build/lib/lean/Fvdep/Registry.olean"
        planted.parent.mkdir(parents=True, exist_ok=True)
        planted.write_bytes(b"not a Lean export")
        (lib.root / "lakefile.lean").write_text("this working-copy build configuration is ignored\n")
        env = {"LEAN_PATH": str(lib.root / "not-a-library"), "TZ": "Pacific/Kiritimati",
               "FVDEP_CACHE": str(lib.root / "unrelated-cache")}
        ignored = ctx.call(lib.root, ["index"], env=env)
        after_ignored = path.read_bytes() if path.exists() else None
        copy_root = ctx.work / "purity-other-path"
        shutil.copytree(lib.root, copy_root, ignore=shutil.ignore_patterns(".lake", "index.json"))
        moved = ctx.call(copy_root, ["index"])
        moved_bytes = (copy_root / "index.json").read_bytes() if (copy_root / "index.json").exists() else None
        return locals()
    pget = lambda: ctx.shared("purity-sequence", purity)
    for name, actual, expected in (("idempotent", "repeated", "initial"),
                                    ("check-readonly", "after_check", "initial"),
                                    ("drift-readonly", "after_drift", "changed"),
                                    ("environment-artifact", "after_ignored", "initial"),
                                    ("absolute-path", "moved_bytes", "initial")):
        ctx.add("C6.purity." + name, "F6", "C1 purity + pinned fresh build",
                lambda actual=actual, expected=expected, name=name: ctx.eq(pget()[actual], pget()[expected], name))
    for name, proc_key, code, stdout in (("check-current", "checked", 0, b"index.json is current\n"),
                                        ("check-drift", "drift", 1, b"index.json differs from the library\n"),
                                        ("check-absent", "absent", 1, b"index.json differs from the library\n")):
        def check(proc_key: str = proc_key, code: int = code, stdout: bytes = stdout) -> None:
            values = pget()
            proc = values[proc_key]
            ctx.eq((proc.returncode, proc.stdout), (code, stdout), "compare exact result")
            if proc_key == "absent":
                ctx.eq(values["absent_stayed"], True, "absent index not created by --check")
        ctx.add("C6.purity." + name, "F6", "C1/C9 --check", check)
    def writer_lock_ignored() -> None:
        lib = ctx.library("writer-lock-ignored")
        ctx.build_fixture(lib)
        with (lib.root / ".fvdep-writer.lock").open("a+b") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            proc = ctx.call(lib.root, ["index"])
            ctx.eq(proc.returncode, 0, "index does not take the project writer lock")
    ctx.add("C6.no-writer-lock", "F6", "C1 no writer lock", writer_lock_ignored)
    def concurrent() -> None:
        lib = ctx.library("concurrent-index")
        ctx.build_fixture(lib)
        start = threading.Barrier(2)
        def call(_: int) -> Any:
            start.wait(timeout=30)
            return ctx.call(lib.root, ["index"])
        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(call, (0, 1)))
        ctx.eq([proc.returncode for proc in results], [0, 0], "concurrent unchanged-tree index runs")
        ctx.eq(results[0].stdout, results[1].stdout, "identical result lines")
        value = json.loads((lib.root / "index.json").read_bytes())
        ctx.eq((lib.root / "index.json").read_bytes(), ctx.fx.canonical(value) + b"\n",
               "complete canonical bytes after both writers")
    ctx.add("C6.concurrent", "F6", "C1 concurrent unchanged tree", concurrent,
            "two requests released together; global subprocess width remains bounded")
    def read_error() -> None:
        lib = ctx.library("index-read-error")
        ctx.build_fixture(lib)
        (lib.root / "index.json").mkdir()
        proc = ctx.call(lib.root, ["index", "--check"])
        ctx.eq(proc.returncode, 2, "index read error exit")
        ctx.eq(proc.stdout, b"", "index read error stdout")
        last = proc.stderr.decode(errors="replace").splitlines()[-1:]
        ctx.eq(bool(last and last[0].startswith("Could not read index.json: ") and last[0].endswith(".")),
               True, "read error fixed line")
    ctx.add("C6.io.read", "F6", "C1/C9 read failure", read_error)
    def write_error() -> None:
        lib = ctx.library("index-write-error")
        ctx.build_fixture(lib)
        path = lib.root / "index.json"
        path.write_bytes(b"old complete bytes\n")
        proc = ctx.call(lib.root, ["index"], env={"LD_PRELOAD": str(ctx.here / ".build/fault.so"),
                        "FVDEP_INDEX_FAULT": "write", "FVDEP_INDEX_FAULT_ROOT": str(lib.root)})
        ctx.eq(proc.returncode, 2, "index write error exit")
        ctx.eq(proc.stdout, b"", "index write error stdout")
        last = proc.stderr.decode(errors="replace").splitlines()[-1:]
        ctx.eq(bool(last and last[0].startswith("Could not finish writing index.json: ") and last[0].endswith(".")),
               True, "write error fixed line")
        ctx.eq(path.read_bytes(), b"old complete bytes\n", "failure before temp creation keeps bytes")
    ctx.add("C6.io.write", "F6", "C1/C9 replace failure", write_error)


def register_cli_schema(ctx: Any) -> None:
    def cli_root(name: str) -> Path:
        def make() -> Path:
            root = ctx.work / name
            root.mkdir()
            return root
        return ctx.shared("cli-root:" + name, make)
    def help_check() -> None:
        root = cli_root("help")
        a = ctx.call(root, ["index", "--help"])
        b = ctx.call(root, ["help", "index"])
        for proc in (a, b):
            ctx.eq(proc.returncode, 0, "help exit")
            ctx.eq(proc.stderr, b"", "help stderr")
            ctx.eq(b"index" in proc.stdout and b"--check" in proc.stdout and proc.stdout.endswith(b"\n"),
                   True, "index usage stdout")
        ctx.eq(a.stdout, b.stdout, "equivalent help forms")
        ctx.eq(list(root.iterdir()), [], "help touches no file")
    ctx.add("C9.help", "F9", "C9 help before presence; interface §1", help_check)
    for i, args in enumerate((["--bad"], ["extra"], ["--check", "extra"], ["--json"],
                               ["--check", "--check"], ["--help", "extra"])):
        def usage(args: list[str] = args, i: int = i) -> None:
            root = cli_root("usage-" + str(i))
            proc = ctx.call(root, ["index", *args])
            ctx.eq(proc.returncode, 2, "usage exit")
            ctx.eq(proc.stdout, b"", "usage stdout")
            ctx.eq(b"usage" in proc.stderr.lower() and proc.stderr.endswith(b"\n"), True,
                   "usage stderr before library presence")
            ctx.eq(list(root.iterdir()), [], "usage touches no file")
        ctx.add(f"C9.usage.{i}", "F9", "C9 usage before presence; interface §1", usage)
    def progress_controls() -> None:
        def mutate(lib: Any) -> None:
            path = lib.root / "FvdepProofs/Registry/Base64/Encode/V1_0_0.lean"
            source = path.read_text()
            command = ("open Lean Elab Command in\nrun_cmd liftIO <| IO.eprintln " +
                       ctx.fx.quoted("progress\t\0\x1b\x85\rend") + "\n")
            path.write_text("import Lean\n" + source.replace("namespace " + P,
                            command + "namespace " + P, 1))
        lib = ctx.library("progress-controls", mutate)
        raw = ctx.build_fixture(lib)
        if raw is not None:
            text = raw.decode(errors="replace")
            ctx.need(any(ord(c) < 32 and c != "\n" or 127 <= ord(c) <= 159 for c in text),
                     "raw Lake control positive control was not observed")
        proc = ctx.call(lib.root, ["index"])
        ctx.eq(proc.returncode, 0, "progress fixture indexes")
        bad = [ord(c) for c in proc.stderr.decode() if (ord(c) < 32 and c != "\n") or 127 <= ord(c) <= 159]
        ctx.eq(bad, [], "Lake progress relayed without raw Cc; content otherwise free")
    ctx.add("C9.presentation.lake-progress", "F9", "C9/D3 rev2 progress escaping", progress_controls)
    def schema_launch() -> None:
        obs = ctx.observe("launch-schema", launch=True)
        value = ctx.document(obs)
        ctx.eq(obs.proc.stdout, b"Wrote index.json (6 entries)\n", "one stdout line + count")
        ctx.eq(set(value), {"notices", "operations", "removed", "schema", "toolchain"}, "root keys")
        ctx.eq(value["schema"], 1, "schema")
        ctx.eq(value["toolchain"], TC, "toolchain")
        ctx.eq([x["id"] for x in value["operations"]], ctx.fx.LAUNCH, "operation id byte order")
        for item in value["operations"]:
            ctx.eq(set(item), {"compat", "digest", "id", "obligations", "version"}, "operation fields")
            ctx.eq(item["version"], "1.0.0", "launch version")
            ctx.eq(bool(re.fullmatch(r"[0-9a-f]{64}", item["digest"])), True, "digest shape")
            ctx.eq(item["compat"], None, "launch compat")
            ctx.eq(item["obligations"], [{"name": n, "status": "proven", "axioms": []}
                                        for n in ctx.fx.OBLIGATIONS[item["id"]]],
                   "obligation last names + registry order")
        ctx.eq(obs.after, ctx.fx.canonical(value) + b"\n", "canonical bytes + LF")
    ctx.add("C12.schema.launch", "F12", "C6/C9 exact schema 1", schema_launch)
    for bound in ("obligation-name", "axiom-name", "removed-toolchain-cc", "removed-toolchain-long"):
        def producer_bound(bound: str = bound) -> None:
            def mutate(lib: Any) -> None:
                long_name = "a" * 1025
                if bound == "obligation-name":
                    path = lib.root / "Fvdep/Base64/Encode/V1_0_0.lean"
                    path.write_text(path.read_text() +
                                    f"\nnamespace {S}\ndef {long_name} : Prop := True\nend {S}\n")
                    lib.entry(obligations=[S + "." + long_name])
                elif bound.startswith("removed-toolchain"):
                    toolchain = "x\x85" if bound.endswith("cc") else "x" * 1025
                    lib.removed([{"id": "other.encode", "version": "1.0.0", "digest": "1" * 64,
                                  "lastCommit": "2" * 40, "toolchain": toolchain, "kind": "operation"}])
                    lib.notices([ctx.fx.notice(id="other.encode")])
                else:
                    lib.proofs(source=f'''import {E}
namespace {P}
axiom {long_name} : {S}.bits
theorem bits : {S}.bits := {long_name}
theorem length : {S}.length := True.intro
def proofs : {R}.Proofs := {{
  obligations := [(``{S}.bits, ``{P}.bits), (``{S}.length, ``{P}.length)]
  compat := none }}
end {P}
''')
            obs = ctx.observe("producer-bound-" + bound, mutate)
            ctx.eq(obs.proc.returncode, 2, "out-of-domain index refused before printing")
            ctx.eq(obs.proc.stdout, b"", "producer bound stdout")
            ctx.eq(obs.after, obs.before, "producer bound leaves index bytes intact")
            if bound.startswith("removed-toolchain"):
                last = obs.proc.stderr.splitlines(keepends=True)[-1:] or [b""]
                ctx.eq(last[0].startswith(b"The index is outside schema 1: /removed/0/toolchain bad_value "),
                       True, "D3 rev2 fixed schema-refusal prefix")
        ctx.add("C12.bound." + bound, "F12", "C6 out-of-domain producer; interface §2; D3 rev2", producer_bound)
    def schema_empty() -> None:
        def mutate(lib: Any) -> None:
            lib.registry([])
            for module in (E, P):
                (lib.root / (module.replace(".", "/") + ".lean")).unlink()
            (lib.root / "FvdepProofs.lean").write_text("/-! Empty proofs. -/\n")
        obs = ctx.observe("empty-schema", mutate)
        ctx.eq(obs.proc.returncode, 0, "empty library indexes")
        ctx.eq(obs.proc.stdout, b"Wrote index.json (0 entries)\n", "empty operation count")
        ctx.eq(ctx.document(obs), ctx.fx.index(), "schema 1 empty collections")
    ctx.add("C12.schema.empty", "F12", "C6 empty index; C9 count", schema_empty)
    def numeric_versions() -> None:
        def mutate(lib: Any) -> None:
            ten = lib.add_version("1.0.10")
            two = lib.add_version("1.0.2")
            lib.registry([ten, E, two])
        obs = ctx.observe("numeric-versions", mutate)
        value = ctx.document(obs)
        ctx.eq([item["version"] for item in value["operations"]], ["1.0.0", "1.0.2", "1.0.10"],
               "numeric ordering independent of registry order")
        ctx.eq(obs.proc.stdout, b"Wrote index.json (3 entries)\n", "operation count includes versions")
    ctx.add("C12.schema.numeric-order", "F12", "C6 numeric versions; C9 count", numeric_versions)
    def accepted_forms() -> None:
        def mutate(lib: Any) -> None:
            lib.registry([E], prefix=f"def chunk : List {R}.Module := [{E}.entry]",
                         expression=f"let xs := (show List {R}.Module from chunk); "
                                    f"xs ++ (have ys : List {R}.Module := []; ys)")
            path = lib.root / "Fvdep/Registry/Base64/Encode/V1_0_0.lean"
            name = ".anonymous"
            for part in S.split(".") + ["encode"]:
                name = f"(.str {name} {ctx.fx.quoted(part)})"
            path.write_text(path.read_text().replace("``" + S + ".encode", name))
        obs = ctx.observe("accepted-forms", mutate)
        ctx.eq(obs.proc.returncode, 0, "let, root constant, HAppend accepted")
        ctx.eq(obs.proc.stdout, b"Wrote index.json (1 entries)\n", "accepted forms count")
        ctx.eq(len(ctx.document(obs)["operations"]), 1, "literal decoded exactly once")
    ctx.add("C12.registry.accepted-forms", "F12", "C2 forms + certificate", accepted_forms)
