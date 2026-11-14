#!/usr/bin/env python3
"""Idempotent consumer fixtures from docs/interface.md §7 + library API v1."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ENC = "Fvdep.Base64.Encode.V1_0_0"
DEC = "Fvdep.Base64.Decode.V1_0_0"
ENC_TYPE = "List UInt8 → List Char"
HEADER = 'schema = 1\n\n[library]\ncommit = "@LIBRARY_COMMIT@"\n\n[policy]\nproof = "@POLICY@"\n'


def emit(name, files, entries=None):
    root = HERE / "consumers" / name
    root.mkdir(parents=True, exist_ok=True)
    if entries is None:
        entries = {"base64.encode": {"version": "1.0.0", "shape": "fn", "impl_modules": ["Impl"],
                                    "proof_modules": ["Proof"], "impl": "Impl.encode", "proof": "Proof.encode_eq"}}
    manifest = HEADER
    for id, entry in entries.items():
        manifest += f'\n[modules.{json.dumps(id)}]\n'
        manifest += "".join(f"{k} = {json.dumps(v)}\n" for k, v in entry.items())
    (root / "fvdep.toml").write_text(manifest)
    for file, text in files.items():
        target = root / (file + ".in" if file.endswith(".lean") else file)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)


HONEST = f"import {ENC}\nnamespace Impl\ndef encode : {ENC_TYPE} := {ENC}.encode\nend Impl\n"
WRONG = f"import {ENC}\nnamespace Impl\ndef encode : {ENC_TYPE} := fun _ => []\nend Impl\n"
PROOF = f"import Impl\nnamespace Proof\ntheorem encode_eq : @Impl.encode = @{ENC}.encode := rfl\nend Proof\n"
FALSE_STMT = f"@Impl.encode = @{ENC}.encode"


def main():
    emit("honest-fn", {"Impl.lean": HONEST, "Proof.lean": PROOF})
    emit("wrong-implementation", {"Impl.lean": WRONG, "Proof.lean": PROOF})
    emit("sorry", {"Impl.lean": WRONG, "Proof.lean": PROOF.replace("rfl", "by sorry")})
    emit("custom-axiom", {"Impl.lean": WRONG, "Proof.lean": f"import Impl\nnamespace Proof\naxiom assumption : {FALSE_STMT}\ntheorem encode_eq : {FALSE_STMT} := assumption\nend Proof\n"})
    emit("wrong-statement", {"Impl.lean": WRONG, "Proof.lean": "import Impl\nnamespace Proof\ntheorem encode_eq : True := True.intro\nend Proof\n"})
    emit("macro-statement", {"Impl.lean": WRONG, "Proof.lean": f'import Impl\nmacro:max "@Impl.encode" : term => `(@{ENC}.encode)\nnamespace Proof\ntheorem encode_eq : @Impl.encode = @{ENC}.encode := rfl\nend Proof\n'})
    emit("native-decide", {"Impl.lean": HONEST, "Proof.lean": f"import Lean\nimport Impl\nnamespace Proof\ntheorem native_fact : True := by native_decide\ntheorem encode_eq : {FALSE_STMT} := True.rec rfl native_fact\nend Proof\n"})
    forged = f'''import Lean
import Impl
open Lean in
set_option debug.skipKernelTC true in
run_cmd do
  let encodeType : Expr := .forallE `xs
    (mkApp (mkConst ``List [.zero]) (mkConst ``UInt8))
    (mkApp (mkConst ``List [.zero]) (mkConst ``Char)) .default
  let impl := mkConst ``Impl.encode
  let spec := mkConst ``{ENC}.encode
  let equation := mkApp3 (mkConst ``Eq [.succ .zero]) encodeType impl spec
  let falseProof := mkApp2 (mkConst ``Eq.refl [.succ .zero]) encodeType impl
  Elab.Command.liftCoreM <| addDecl (.thmDecl {{
    name := `Proof.encode_eq
    levelParams := []
    type := equation
    value := falseProof }})
'''
    emit("forged-kernel", {"Impl.lean": WRONG, "Proof.lean": forged})
    emit("implemented-by", {"Impl.lean": f"import {ENC}\nnamespace Impl\ndef rogue : {ENC_TYPE} := fun _ => []\n@[implemented_by rogue]\ndef encode : {ENC_TYPE} := {ENC}.encode\nend Impl\n", "Proof.lean": PROOF})
    emit("extern", {"Impl.lean": f'import {ENC}\nnamespace Impl\n@[extern "acceptance_replacement"]\ndef encode : {ENC_TYPE} := {ENC}.encode\nend Impl\n', "Proof.lean": PROOF})
    emit("run-cmd", {"Impl.lean": HONEST + '\nrun_cmd IO.FS.writeFile ".lake/build/ir/Impl.c" "/* rewritten */"\n', "Proof.lean": PROOF})
    emit("initialize", {"Impl.lean": HONEST + '\ninitialize attack : IO.Ref Nat ← do\n  IO.FS.writeFile "rewritten.c" "/* rewritten */"\n  IO.mkRef 0\n', "Proof.lean": PROOF})
    emit("unsafe", {"Impl.lean": HONEST.replace("def encode", "unsafe def encode"), "Proof.lean": PROOF})
    emit("partial", {"Impl.lean": HONEST.replace("def encode", "partial def encode"), "Proof.lean": PROOF})
    emit("opaque", {"Impl.lean": HONEST.replace("def encode", "opaque encode"), "Proof.lean": PROOF})
    emit("metaprogram", {"Impl.lean": HONEST + '\nmacro "consumer_macro" : term => `(0)\n', "Proof.lean": PROOF})
    emit("import-lean", {"Impl.lean": "import Lean\n" + HONEST, "Proof.lean": PROOF})
    emit("import-lake", {"Impl.lean": "import Lake\n" + HONEST, "Proof.lean": PROOF})
    emit("skip-kernel-option", {"Impl.lean": HONEST.replace("namespace Impl", "set_option debug.skipKernelTC true\nnamespace Impl"), "Proof.lean": PROOF})
    emit("proof-write-outside", {"Impl.lean": HONEST, "Proof.lean": 'import Lean\nimport Impl\nrun_cmd do\n  try IO.FS.writeFile "@OUTSIDE@" "escaped" catch _ => pure ()\n' + PROOF.replace("import Impl\n", "")})
    emit("proof-network", {"Impl.lean": HONEST, "Proof.lean": 'import Lean\nimport Impl\nrun_cmd do\n  try\n    let _ ← IO.Process.output { cmd := "python3", args := #["-I", "-c", "import socket; socket.create_connection((\\\"127.0.0.1\\\", @PORT@), 1).sendall(b\\\"escaped\\\")"] }\n    pure ()\n  catch _ => pure ()\n' + PROOF.replace("import Impl\n", "")})
    emit("proof-symlink", {"Impl.lean": HONEST, "Proof.lean": 'import Lean\nimport Impl\nrun_cmd do\n  try\n    let _ ← IO.Process.output { cmd := "ln", args := #["-s", "@OUTSIDE@", "proof-plant"] }\n    pure ()\n  catch _ => pure ()\n' + PROOF.replace("import Impl\n", "")})
    emit("tampered-vendor", {"Impl.lean": WRONG, "Proof.lean": PROOF,
                              ".lake/packages/fvdep/Fvdep/Base64/Encode/V1_0_0.lean": f"namespace {ENC}\ndef encode : {ENC_TYPE} := fun _ => []\nend {ENC}\n"})
    emit("consumer-build-hook", {"Impl.lean": HONEST, "Proof.lean": PROOF,
                                 "lakefile.lean": 'import Lake\nopen Lake DSL\nrun_cmd IO.FS.writeFile "@OUTSIDE@" "consumer build hook ran"\npackage consumer\n'})
    entry = {"version": "1.0.0", "shape": "fn", "impl_modules": [ENC], "proof_modules": ["Proof"],
             "impl": f"{ENC}.encode", "proof": "Proof.encode_eq"}
    emit("reserved-module", {f'{ENC.replace(".", "/")}.lean': f"namespace {ENC}\ndef encode : {ENC_TYPE} := fun _ => []\nend {ENC}\n", "Proof.lean": f"import {ENC}\nnamespace Proof\ntheorem encode_eq : @{ENC}.encode = @{ENC}.encode := rfl\nend Proof\n"}, {"base64.encode": entry})
    renamed = {"version": "1.0.0", "shape": "fn", "impl_modules": ["Acme.Core", "Acme.Export"],
               "proof_modules": ["Acme.Proofs"], "impl": "Acme.Export.encode", "proof": "Acme.Proofs.correct"}
    emit("renamed-multimodule", {"Acme/Core.lean": f"import {ENC}\nnamespace Acme.Core\ndef encode : {ENC_TYPE} := {ENC}.encode\nend Acme.Core\n",
                                "Acme/Export.lean": f"import Acme.Core\nnamespace Acme.Export\ndef encode : {ENC_TYPE} := Acme.Core.encode\nend Acme.Export\n",
                                "Acme/Proofs.lean": f"import Acme.Export\nnamespace Acme.Proofs\ntheorem correct : @Acme.Export.encode = @{ENC}.encode := rfl\nend Acme.Proofs\n"}, {"base64.encode": renamed})
    abi_entries = {
        "base64.encode": {"version": "1.0.0", "shape": "abi", "impl_modules": ["Impl"], "proof_modules": ["Proof"], "impl": "Impl.encode", "proof": "Proof.encode_eq"},
        "base64.decode": {"version": "1.0.0", "shape": "abi", "impl_modules": ["Impl"], "proof_modules": ["Proof"], "impl": "Impl.decode", "proof": "Proof.decode_eq"}}
    abi_impl = f"import {ENC}\nimport {DEC}\nimport Fvdep.Abi.V1_0_0\nnamespace Impl\ndef encode := Fvdep.Abi.V1_0_0.encoder {ENC}.encode\ndef decode := Fvdep.Abi.V1_0_0.decoder {DEC}.decode\nend Impl\n"
    abi_proof = f"import Impl\nnamespace Proof\ntheorem encode_eq : @Impl.encode = Fvdep.Abi.V1_0_0.encoder @{ENC}.encode := rfl\ntheorem decode_eq : @Impl.decode = Fvdep.Abi.V1_0_0.decoder @{DEC}.decode := rfl\nend Proof\n"
    emit("honest-abi", {"Impl.lean": abi_impl, "Proof.lean": abi_proof}, abi_entries)
    ops = [("base64.encode", ENC, "encode"), ("base64.decode", DEC, "decode"),
           ("base64.encode_url", "Fvdep.Base64.EncodeUrl.V1_0_0", "encodeUrl"),
           ("base64.decode_url", "Fvdep.Base64.DecodeUrl.V1_0_0", "decodeUrl"),
           ("semver.parse", "Fvdep.Semver.Parse.V1_0_0", "parse"),
           ("semver.compare", "Fvdep.Semver.Compare.V1_0_0", "compare")]
    impl = "".join(f"import {module}\n" for _, module, _ in ops) + "namespace Impl\n"
    proofs = "import Impl\nnamespace Proof\n"
    entries = {}
    for id, module, fn in ops:
        impl += f"def {fn} := {module}.{fn}\n"
        proofs += f"theorem {fn}_eq : @Impl.{fn} = @{module}.{fn} := rfl\n"
        entries[id] = {"version": "1.0.0", "shape": "fn", "impl_modules": ["Impl"], "proof_modules": ["Proof"], "impl": f"Impl.{fn}", "proof": f"Proof.{fn}_eq"}
    emit("honest-launch", {"Impl.lean": impl + "end Impl\n", "Proof.lean": proofs + "end Proof\n"}, entries)


if __name__ == "__main__":
    main()
