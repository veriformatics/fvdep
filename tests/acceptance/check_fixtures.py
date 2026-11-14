#!/usr/bin/env python3
"""Qualify seven Lean proof fixtures against signature-only stubs, not fvdep.

No lake build, product binary, real spec body, or consumer escape hook runs.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
NAMES = ("honest-fn", "forged-kernel", "custom-axiom", "sorry", "wrong-statement", "macro-statement", "native-decide")


def command(argv, cwd, env):
    proc = subprocess.run([str(x) for x in argv], cwd=cwd, env=env, text=True,
                          capture_output=True, timeout=30, check=False)
    return proc.returncode, proc.stdout + proc.stderr


def main():
    failures = 0
    with tempfile.TemporaryDirectory(prefix="fvdep-signatures-") as tmp:
        root = Path(tmp)
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        stubs = root / "stubs"
        shutil.copytree(HERE / "fixtures/signature_stubs", stubs)
        for path in stubs.rglob("*.lean.in"):
            path.rename(path.with_suffix(""))
        env = dict(os.environ, LEAN_PATH=str(stubs))
        code, output = command(["lean", "--version"], root, env)
        if code or "version 4.35.0," not in output:
            print(f"FAIL toolchain: expected Lean 4.35.0; rc={code}; {output}")
            return 2
        stub = stubs / "Fvdep/Base64/Encode/V1_0_0.lean"
        code, output = command(["lean", "-o", stub.with_suffix(".olean"), stub], stubs, env)
        if code:
            print(f"FAIL signature stub: rc={code}; {output}")
            return 1
        for name in NAMES:
            directory = root / name
            directory.mkdir()
            for file in ("Impl.lean", "Proof.lean"):
                shutil.copy2(HERE / "fixtures/consumers" / name / (file + ".in"), directory / file)
            env = dict(os.environ, LEAN_PATH=f"{directory}:{stubs}")
            for file in ("Impl.lean", "Proof.lean"):
                source = directory / file
                code, output = command(["lean", "-o", source.with_suffix(".olean"), source], directory, env)
                if code:
                    failures += 1
                    print(f"FAIL {name}/{file}: rc={code}; {output}")
                    break
            else:
                print(f"PASS {name}: signature-stub elaboration rc=0")
                continue
            if name == "forged-kernel":
                return failures
        directory = root / "forged-kernel"
        env = dict(os.environ, LEAN_PATH=f"{directory}:{stubs}")
        text = (directory / "Proof.lean").read_text()
        marker = "set_option debug.skipKernelTC true in\n"
        assert text.count(marker) == 1
        normal = directory / "NormalKernel.lean"
        normal.write_text(text.replace(marker, ""))
        code, output = command(["lean", normal], directory, env)
        if code == 0 or "(kernel) declaration type mismatch" not in output:
            failures += 1
            print(f"FAIL forgery normal-kernel control: rc={code}; {output}")
        else:
            print(f"PASS forgery normal-kernel control: rc={code}; {output.strip()}")
        audit = directory / "ForgedAxioms.lean"
        audit.write_text(text + "\n#print axioms Proof.encode_eq\n")
        code, output = command(["lean", audit], directory, env)
        if code or "'Proof.encode_eq' does not depend on any axioms" not in output:
            failures += 1
            print(f"FAIL forgery axiom-audit control: rc={code}; {output}")
        else:
            print(f"PASS forgery axiom-audit control: rc={code}; {output.strip()}")
    print(f"fixture checks: failures={failures}; product not executed")
    return failures


if __name__ == "__main__":
    sys.exit(main())
