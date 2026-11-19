import Lake

open Lake DSL System

/-- The `fvdep` tool: proven pure core (`FvdepCore`) + thin IO interpreter (`FvdepIO`), requiring
the library by path. Shipped modules import Init, Std, Lean, Lake + fvdep's own libraries alone
(gate stage `imports`); tests may import more. -/
package fvdeptool where
  version := v!"0.1.0"
  description := "The fvdep command-line tool: checks Lean implementations against fvdep specs."
  license := "Apache-2.0 WITH LLVM-exception"
  testDriver := "«fvdep-tests»"
  -- Lints ride the build (warnings are errors): a separate `lake lint --linters` build would
  -- rebuild every module twice per gate run (measured: 4 → 4 → 4 rebuilt modules).
  leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.dupNamespace, true⟩, ⟨`linter.extra.unnecessarySeqFocus, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.extra.unusedDecidableInType, true⟩,
    ⟨`linter.redundantVisibility, true⟩]

require fvdep from ".."

/-! ## Native code: HACL*'s verified SHA-256 + fvdep's shim (`docs/contracts/U3-codecs.md` S2) -/

/-- Vendored HACL* (pinned by `vendor/hacl-star/lock.json`) + fvdep's own C, at the repo root. -/
def haclDist : FilePath := ".." / "vendor" / "hacl-star" / "dist"

def cDir : FilePath := ".." / "c"

/-- `-I` roots + the toolchain compiler's own flags: host paths, so weak (a moved checkout must not
rebuild); their content is traced through `cTrace`. The toolchain's clang ships no libc headers
(`-nostdinc`) and HACL's headers need some (`string.h`, `endian.h`): the system's glibc headers
(`libc6-dev`) follow clang's builtin ones. -/
def cWeakArgs (pkg : Package) : FetchM (Array String) := do
  let roots :=
    #[haclDist / "gcc-compatible", haclDist / "karamel" / "include",
      haclDist / "karamel" / "krmllib" / "dist" / "minimal"]
  return (roots.flatMap fun r => #["-I", (pkg.dir / r).toString]) ++
      #["-I", (← getLeanIncludeDir).toString] ++
      (← getLeanInstall).ccFlags ++
      #["-isystem", "/usr/include/x86_64-linux-gnu", "-isystem", "/usr/include"]

/-- Lake traces a C source + its flags alone: every header (vendored + fvdep's) and the toolchain
(compiler + `lean.h`) join the trace, so a changed header or toolchain rebuilds the objects.
`computeFileHash`, not `fetchFileTrace`: the latter caches `<file>.hash` beside each header,
littering the byte-checked vendored tree. -/
def cTrace (pkg : Package) : JobM BuildTrace := do
  let headers := (← (pkg.dir / haclDist).walkDir) ++ (← (pkg.dir / cDir).walkDir)
  let mut trace ← getLeanTrace
  for h in headers.qsort (·.toString < ·.toString) do
    if h.extension == some "h" then
      trace := trace.mix (.ofHash (← computeFileHash h) h.toString)
  return trace

input_file hacl_sha2.c where path := haclDist / "gcc-compatible" / "Hacl_Hash_SHA2.c"

input_file fvdep_sha256_core.c where path := cDir / "fvdep_sha256_core.c"

input_file fvdep_sha256.c where path := cDir / "fvdep_sha256.c"

input_file fvdep_sys.c where path := cDir / "fvdep_sys.c"

input_file fvdep_spawn.c where path := cDir / "fvdep_spawn.c"

input_file fvdep_cache.c where path := cDir / "fvdep_cache.c"

input_file fvdep_snapshot.c where path := cDir / "fvdep_snapshot.c"

/-- HACL's upstream build flags; fvdep's shim adds warnings as errors (HACL's generated C keeps its
own warning policy). -/
target hacl_sha2.o pkg : FilePath := do
  buildO (pkg.buildDir / "c" / "hacl_sha2.o") (← hacl_sha2.c.fetch) (← cWeakArgs pkg)
      #["-std=gnu11", "-O3", "-fPIC"] (← getLeanCc) (cTrace pkg)

target fvdep_sha256_core.o pkg : FilePath := do
  buildO (pkg.buildDir / "c" / "fvdep_sha256_core.o") (← fvdep_sha256_core.c.fetch)
      (← cWeakArgs pkg) #["-std=gnu11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"] (← getLeanCc)
      (cTrace pkg)

target fvdep_sha256.o pkg : FilePath := do
  buildO (pkg.buildDir / "c" / "fvdep_sha256.o") (← fvdep_sha256.c.fetch) (← cWeakArgs pkg)
      #["-std=gnu11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"] (← getLeanCc) (cTrace pkg)

/-- F1's persistence shim: one libc call per export + fvapi's writer guard. -/
target fvdep_sys.o pkg : FilePath := do
  buildO (pkg.buildDir / "c" / "fvdep_sys.o") (← fvdep_sys.c.fetch) (← cWeakArgs pkg)
      #["-std=gnu11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"] (← getLeanCc) (cTrace pkg)

/-- U5 R2 + R8's spawn shim: the mechanism alone (pipes, posix_spawn, poll, kill, waitpid, the
helper's prctl, fcntl, rlimit, statvfs + open). -/
target fvdep_spawn.o pkg : FilePath := do
  buildO (pkg.buildDir / "c" / "fvdep_spawn.o") (← fvdep_spawn.c.fetch) (← cWeakArgs pkg)
      #["-std=gnu11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"] (← getLeanCc) (cTrace pkg)

/-- U5 K4 + K5's cache shim: the mechanism alone (`link`, `utimensat`). -/
target fvdep_cache.o pkg : FilePath := do
  buildO (pkg.buildDir / "c" / "fvdep_cache.o") (← fvdep_cache.c.fetch) (← cWeakArgs pkg)
      #["-std=gnu11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"] (← getLeanCc) (cTrace pkg)

/-- U5 S1's snapshot shim: the mechanism alone (`openat` + `fstat` of one path component). -/
target fvdep_snapshot.o pkg : FilePath := do
  buildO (pkg.buildDir / "c" / "fvdep_snapshot.o") (← fvdep_snapshot.c.fetch) (← cWeakArgs pkg)
      #["-std=gnu11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"] (← getLeanCc) (cTrace pkg)

target libfvdepnative pkg : FilePath := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "fvdepnative")
      #[← hacl_sha2.o.fetch, ← fvdep_sha256_core.o.fetch, ← fvdep_sha256.o.fetch,
        ← fvdep_sys.o.fetch, ← fvdep_spawn.o.fetch, ← fvdep_cache.o.fetch, ← fvdep_snapshot.o.fetch]

/-! ## Lean targets -/

lean_lib FvdepCore

/-- `Main` (the exe root) belongs here too: lib modules (the ledger's rows) import it, and Lake
tracks an import only into a library's modules. -/
lean_lib FvdepIO where
  roots := #[`FvdepIO, `Main]
  moreLinkObjs := #[libfvdepnative]

/-- Target name ≠ `fvdep`: the `require` above already declares that name. -/
@[default_target] lean_exe «fvdep-cli» where
  root := `Main
  exeName := "fvdep"

lean_exe «fvdep-tests» where root := `Tests

/-- The persistence API's dev driver (contract U3 F6: `fvdep-dev sys run OP…`): tests drive the
real syscalls through it; never shipped (`Main` imports none of it; gate stage `imports`). -/
lean_lib FvdepDev where roots := #[`FvdepDev, `DevMain]

lean_exe «fvdep-dev» where root := `DevMain

/-- The step helper (contract U5 R8): pid 2 of every sandbox step, located beside the executable
that runs the step; `StepMain.main` = `FvdepIO.Step.main`. Every script that runs a step builds it
by name (`extraDepTargets` on the runner's executable left a stale helper in place). -/
lean_exe «fvdep-step» where root := `StepMain

/-- Fuzz targets (contract U3 "Fuzz"; `tools/fuzz.sh`): one `@[export]` entry per module, its IR C
+ import closure compiled into the engine + replay builds; never shipped (gate stage `imports`). -/
lean_lib FvdepFuzz

/-- Specs + proofs about the shipped code (contract `docs/contracts/U3-codecs.md` A): gate-only,
imported by the ledger alone (gate stage `imports`), replayed by the ledger's kernel check. -/
lean_lib FvdepAudit where globs := #[.andSubmodules `FvdepAudit]

/-- Coverage ledger + its checker (gate stage `coverage`; contract U2 L1–L8): a gate tool, never
shipped (`Main` imports none of it). -/
lean_lib FvdepLedger

lean_exe «fvdep-ledger» where
  root := `LedgerMain
  supportInterpreter := true

/-- Planted ledger breaches + clean controls (contract U2 L9; `tests/ledger/run.sh`). `sorry` +
forged fixtures build on purpose ⇒ warnings stay warnings in this library alone. -/
lean_lib FvdepLedgerFixtures where
  globs := #[.andSubmodules `FvdepLedgerFixtures]
  leanOptions := #[⟨`warningAsError, false⟩]
