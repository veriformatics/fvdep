#!/usr/bin/env python3
"""Small lockfile inputs; never installed. Reader subset qualification is U12."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def put(directory, file, value):
    root = HERE / directory
    root.mkdir(parents=True, exist_ok=True)
    (root / file).write_text(value)


def main():
    put("pnpm", "pnpm-lock.yaml", """lockfileVersion: '9.0'
settings:
  autoInstallPeers: true
  excludeLinksFromLockfile: false
importers:
  .:
    dependencies:
      base64-js:
        specifier: ^1.5.0
        version: 1.5.1
packages:
  base64-js@1.5.1: {}
  semver@7.7.3: {}
snapshots:
  base64-js@1.5.1:
    dependencies:
      semver: 7.7.3
  semver@7.7.3: {}
""")
    npm = {"name": "acceptance-consumer", "version": "0.1.0", "lockfileVersion": 3, "requires": True,
           "packages": {"": {"name": "acceptance-consumer", "version": "0.1.0", "dependencies": {"base64-js": "^1.5.0"}},
                        "node_modules/base64-js": {"version": "1.5.1", "dependencies": {"semver": "7.7.3"}},
                        "node_modules/semver": {"version": "7.7.3"}}}
    put("npm", "package-lock.json", json.dumps(npm, indent=2) + "\n")
    old = json.loads(json.dumps(npm))
    old["packages"]["node_modules/base64-js"]["version"] = "1.5.0"
    put("npm-other-version", "package-lock.json", json.dumps(old, indent=2) + "\n")
    unresolved = {"name": "acceptance-consumer", "version": "0.1.0", "lockfileVersion": 3, "requires": True,
                  "packages": {"": {"name": "acceptance-consumer", "version": "0.1.0", "dependencies": {"not-resolved": "^1.2.0"}}}}
    put("npm-unresolved", "package-lock.json", json.dumps(unresolved, indent=2) + "\n")
    put("cargo", "Cargo.lock", '''version = 4

[[package]]
name = "acceptance-consumer"
version = "0.1.0"
dependencies = ["base64"]

[[package]]
name = "base64"
version = "0.22.1"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "0000000000000000000000000000000000000000000000000000000000000000"
dependencies = ["semver"]

[[package]]
name = "semver"
version = "1.0.27"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "1111111111111111111111111111111111111111111111111111111111111111"
''')
    put("cargo", "Cargo.toml", '''[package]
name = "acceptance-consumer"
version = "0.1.0"
edition = "2024"

[dependencies]
base64 = "0.22.1"
''')
    put("uv", "uv.lock", '''version = 1
revision = 3
requires-python = ">=3.14"

[[package]]
name = "acceptance-consumer"
version = "0.1.0"
source = { virtual = "." }
dependencies = [{ name = "direct-leaf" }]

[package.metadata]
requires-dist = [{ name = "direct-leaf", specifier = "==1.2.3" }]

[[package]]
name = "direct-leaf"
version = "1.2.3"
source = { registry = "https://pypi.org/simple" }
dependencies = [{ name = "indirect-leaf" }]

[[package]]
name = "indirect-leaf"
version = "2.3.4"
source = { registry = "https://pypi.org/simple" }
''')
    put("uv", "pyproject.toml", '''[project]
name = "acceptance-consumer"
version = "0.1.0"
requires-python = ">=3.14"
dependencies = ["direct-leaf==1.2.3"]
''')
    packages = []
    for name, sha, inherited in [("direct-lib", "a" * 40, False), ("indirect-lib", "b" * 40, True)]:
        packages.append({"url": f"https://example.invalid/{name}", "type": "git", "subDir": None,
                         "scope": "", "rev": sha, "name": name, "manifestFile": "lake-manifest.json",
                         "inputRev": "main", "inherited": inherited, "configFile": "lakefile.lean"})
    lake = {"version": "1.1.0", "packagesDir": ".lake/packages", "packages": packages,
            "name": "acceptance-consumer", "lakeDir": ".lake"}
    put("lake", "lake-manifest.json", json.dumps(lake, indent=2) + "\n")
    put("unsupported", "package-lock.json", '{"lockfileVersion":999,"packages":{}}\n')
    put("malformed", "pnpm-lock.yaml", "lockfileVersion: [unterminated\n")


if __name__ == "__main__":
    main()
