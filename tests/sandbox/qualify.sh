#!/usr/bin/env bash
# Authoring qualification only: fixture typing independent of U5's unavailable driver.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
mkdir -p "$root/tests/sandbox/.runs"
work=$(mktemp -d "$root/tests/sandbox/.runs/qualify.XXXXXXXX")
trap 'rm -rf -- "$work"' EXIT
for fixture in honest module-proof; do
  dir=$work/$fixture
  mkdir -p "$dir"
  cp -R "$root/tests/sandbox/fixtures/$fixture/SandboxTrial" "$dir/"
  cp "$root/lean-toolchain" "$dir/lean-toolchain"
  printf 'import Lake\nopen Lake DSL\npackage «sandbox-fixture»\nrequire fvdep from "%s"\n@[default_target] lean_lib SandboxTrial\n' "$root" > "$dir/lakefile.lean"
  printf 'import SandboxTrial.Proof\n' > "$dir/SandboxTrial.lean"
  (cd -- "$dir" && lake build) > "$work/$fixture.log" 2>&1 || {
    tail -n 40 "$work/$fixture.log" >&2
    exit 1
  }
  printf 'QUALIFY %s PASS\n' "$fixture"
done
# B.incomplete requires an actually over-cap input view, not merely large source text.
python3 -I - "$work/bundle-view" "$root" <<'PY'
from pathlib import Path
import sys
p, root = map(Path, sys.argv[1:])
p.mkdir()
(p / 'lean-toolchain').write_bytes((root / 'lean-toolchain').read_bytes())
(p / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage «sandbox-bundle-view»\n@[default_target] lean_lib Fvdep\n')
imports = []
for i in range(20):
    module = f'Fvdep.BundleFill.M{i:02}'
    imports.append('import ' + module)
    f = p / (module.replace('.', '/') + '.lean')
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text(f'def bundlePayload{i:02} : String := "' + 'x' * 900000 + '"\n')
(p / 'Fvdep.lean').write_text('\n'.join(imports) + '\n')
PY
(cd -- "$work/bundle-view" && lake build) > "$work/bundle-view.log" 2>&1 || {
  tail -n 40 "$work/bundle-view.log" >&2
  exit 1
}
python3 -I - "$work/bundle-view" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1]) / '.lake/build'
size = sum(f.stat().st_size for f in p.rglob('M*') if f.is_file() and
           f.suffix in {'.olean', '.ilean', '.c'})
assert size > 32 * 1024 * 1024, size
print(f'QUALIFY bundle-view {size} bytes > 33554432 PASS')
PY
