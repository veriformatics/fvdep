#!/usr/bin/env bash
# Coverage-guided fuzzing (contract docs/contracts/U3-codecs.md "Fuzz"; .claude/rules/checks.md):
# AFL++ from tools/afl.lock, built project-local by the host gcc into .tools/afl/<version>/;
# targets = the FvdepFuzz Lean entries + the C harnesses in tests/fuzz/, each corpus (seeds +
# every crash input, pinned) = tests/fuzz/<target>/.
#   fuzz.sh engine                   verify the pinned tarball + build afl-fuzz, afl-cmin, the
#                                    compiler runtime + aflpp_driver (cached per version)
#   fuzz.sh build TARGET MODE        MODE cov = engine build (SanCov + UBSan trap) | ctl = engine
#                                    control (the harness alone instrumented) | replay = no engine
#                                    (C targets under gcc ASan + UBSan); prints the binary
#   fuzz.sh replay [TARGET…]         every corpus file through each replay build (stage
#                                    `fuzz-replay`); an abort names its input
#   fuzz.sh campaign TARGET SECONDS [MODE]   build, then an afl-fuzz time box →
#                                            .gate/fuzz/out/TARGET[-MODE]
#   fuzz.sh run TARGET SECONDS [MODE]        the time box alone, on the built binary (parallel runs
#                                            in one workspace: build each first, then run)
#   fuzz.sh cmin TARGET              minimize corpus + campaign queue → .gate/fuzz/cmin/TARGET
#   fuzz.sh pin VERSION              print tools/afl.lock's line for VERSION
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$root"

TARGETS=(json-decode lock-decode unframe manifest-decode sha256 sys-actions)

die() {
    printf 'fuzz: %s\n' "$*" >&2
    exit 1
}

read -r _ version _ digest url < <(grep -v '^#' tools/afl.lock) || die "tools/afl.lock: no pin line"
afl="$root/.tools/afl/$version"
out="$root/.gate/fuzz"
tc=""

sha() { sha256sum <"$1" | cut -c1-64; }

toolchain() { [[ -n $tc ]] || tc="$(cd tool && lean --print-prefix)"; }

# Lean targets: module, @[export] entry, IO entry (0 | 1).
lean_target() {
    case "$1" in
    json-decode) echo "FvdepFuzz.Json fvdep_fuzz_json 0" ;;
    lock-decode) echo "FvdepFuzz.Lock fvdep_fuzz_lock 0" ;;
    unframe) echo "FvdepFuzz.Frame fvdep_fuzz_unframe 0" ;;
    manifest-decode) echo "FvdepFuzz.Manifest fvdep_fuzz_manifest 1" ;;
    *) return 1 ;;
    esac
}

engine() {
    [[ -x $afl/afl-fuzz && -x $afl/afl-cmin && -f $afl/afl-rt.o && -f $afl/afl-driver.o ]] &&
        return 0
    local tarball="$root/.tools/cache/afl-$version.tar.gz" src
    mkdir -p "$root/.tools/cache" "$afl"
    if [[ ! -f $tarball || "$(sha "$tarball")" != "$digest" ]]; then
        curl -fsSL --max-time 300 -o "$tarball.part" "$url" || die "fetch $url failed"
        [[ "$(sha "$tarball.part")" == "$digest" ]] ||
            die "$url: sha256 $(sha "$tarball.part") differs from tools/afl.lock"
        mv "$tarball.part" "$tarball"
    fi
    src="$(mktemp -d)"
    # shellcheck disable=SC2064 # the path is fixed now; expanding it at trap time is the intent
    trap "rm -rf -- '$src'" RETURN
    tar -xzf "$tarball" -C "$src" --strip-components=1
    # The engine never runs AFL++'s own instrumenting compilers: its install paths stay unset.
    local defs=(-DAFL_PATH='"/nonexistent"' -DBIN_PATH='"/nonexistent"' -DDOC_PATH='"/nonexistent"')
    local common=(src/afl-common.c src/afl-sharedmem.c src/afl-forkserver.c src/afl-performance.c)
    (
        cd "$src"
        gcc -std=gnu11 -O3 -funroll-loops -Iinclude "${defs[@]}" src/afl-main.c src/afl-fuzz*.c \
            "${common[@]}" -o "$afl/afl-fuzz" -lm -ldl -lrt -lpthread
        gcc -std=gnu11 -O3 -funroll-loops -Iinclude "${defs[@]}" src/afl-cmin.c "${common[@]}" \
            -o "$afl/afl-cmin" -lm -ldl -lrt -lpthread
        gcc -O3 -fPIC -Iinclude -c instrumentation/afl-compiler-rt.o.c -o "$afl/afl-rt.o"
        gcc -O3 -fPIC -Iinclude -c utils/aflpp_driver/aflpp_driver.c -o "$afl/afl-driver.o"
    ) >&2 || die "engine build failed"
    printf 'fuzz: AFL++ %s built\n' "$version" >&2
}

# obj CC SRC FLAGS… → a cached object keyed by compiler path, flags + source bytes (Lean IR C
# includes lean.h alone, whose toolchain the compiler path names).
obj() {
    local cc="$1" src="$2" key o
    shift 2
    key="$({ printf '%s\0' "$cc" "$@"; cat -- "$src"; } | sha256sum | cut -c1-32)"
    o="$out/obj/$key.o"
    if [[ ! -f $o ]]; then
        mkdir -p "$out/obj"
        "$cc" "$@" -c "$src" -o "$o.part" >&2 || die "$src: compile failed"
        mv "$o.part" "$o"
    fi
    printf '%s\n' "$o"
}

# closure MODULE → the IR C of MODULE + of every fvdep module it imports: Lake's setup data lists
# the transitive closure; toolchain modules (Init, Std, Lean, Lake) link prebuilt.
closure() {
    python3 -I - "$root" "$1" <<'PY'
import json, pathlib, sys
root, mod = pathlib.Path(sys.argv[1]), sys.argv[2]
ir = root / "tool/.lake/build/ir"
rel = mod.replace(".", "/")
paths = [ir / (rel + ".c")]
arts = json.loads((ir / (rel + ".setup.json")).read_text(encoding="utf-8"))["importArts"]
for name, groups in sorted(arts.items()):
    if name.split(".")[0] in ("Init", "Std", "Lean", "Lake"):
        continue
    olean = next(p for g in groups for p in g if p.endswith(".olean"))
    paths.append(pathlib.Path(olean.replace("/lib/lean/", "/ir/").removesuffix(".olean") + ".c"))
for p in paths:
    if not p.is_file():
        sys.exit(f"fuzz: {p}: no IR C")
    print(p)
PY
}

build_lean() {
    local t="$1" mode="$2" mod entry io src bin
    read -r mod entry io < <(lean_target "$t")
    toolchain
    (cd tool && lake build FvdepFuzz libfvdepnative >&2) || die "lake build FvdepFuzz failed"
    local cov=("-fsanitize-coverage=trace-pc-guard,trace-cmp" -fsanitize=undefined
        -fsanitize-trap=undefined)
    local irf=(-O2) hf=(-O2 -isystem /usr/include/x86_64-linux-gnu -isystem /usr/include)
    case "$mode" in
    cov) irf+=("${cov[@]}") hf+=("${cov[@]}") ;;
    ctl) hf+=(-fsanitize-coverage=trace-pc-guard) ;;
    replay) ;;
    *) die "build: mode cov | ctl | replay" ;;
    esac
    local objs=() link=()
    while read -r src; do
        objs+=("$(obj "$tc/bin/leanc" "$src" "${irf[@]}")")
    done < <(closure "$mod")
    objs+=("$(obj "$tc/bin/leanc" tests/fuzz/lean.c "${hf[@]}" -DFUZZ_ENTRY="$entry" \
        -DFUZZ_INIT="initialize_fvdeptool_${mod//./_}" -DFUZZ_IO="$io")")
    if [[ $mode == replay ]]; then
        link=("$(obj gcc tests/fuzz/replay.c -O2)")
    else
        engine
        link=("$afl/afl-driver.o" "$afl/afl-rt.o")
    fi
    bin="$out/bin/$t-$mode"
    mkdir -p "$out/bin"
    gcc -o "$bin" "${objs[@]}" "${link[@]}" tool/.lake/build/lib/libfvdepnative.a \
        -L"$tc/lib/lean" -Wl,--start-group -lInit -lStd -lLean -lLake -lleancpp -lleanrt \
        -Wl,--end-group -L"$tc/lib" -l:libc++.a -l:libc++abi.a -l:libgmp.a -l:libuv.a \
        -lpthread -ldl -lrt -lm >&2 || die "$t: link failed"
    printf '%s\n' "$bin"
}

# cov_c BIN FLAGS… -- SRC… -- LINK… → a C target's engine build: each SRC compiled by the
# toolchain clang (`leanc`: it carries clang's builtin headers) with SanCov + UBSan trap (rebuilt
# every time: small, so a header change always counts), linked by the host gcc against the engine
# + LINK.
cov_c() {
    local bin="$1" flags=() srcs=() tmp s
    shift
    while [[ $1 != -- ]]; do
        flags+=("$1")
        shift
    done
    shift
    while [[ $# -gt 0 && $1 != -- ]]; do
        srcs+=("$1")
        shift
    done
    [[ $# -gt 0 ]] && shift
    toolchain
    engine
    tmp="$(mktemp -d)"
    for s in "${srcs[@]}"; do
        "$tc/bin/leanc" -std=gnu11 -O2 -isystem /usr/include/x86_64-linux-gnu \
            -isystem /usr/include "${flags[@]}" "-fsanitize-coverage=trace-pc-guard,trace-cmp" \
            -fsanitize=undefined -fsanitize-trap=undefined -c "$s" -o "$tmp/$(basename "$s" .c).o" \
            >&2 ||
            die "$s: compile failed"
    done
    gcc -o "$bin" "$tmp"/*.o "$afl/afl-driver.o" "$afl/afl-rt.o" "$@" >&2 ||
        die "$bin: link failed"
    rm -rf -- "$tmp"
}

# sha256: S5's lowered limits (tests/sha256/build.sh) reach the chunk loop + the total limit.
build_sha256() {
    local mode="$1" v=vendor/hacl-star/dist bin="$out/bin/sha256-$1"
    local inc=(-I c -I "$v/gcc-compatible" -I "$v/karamel/include"
        -I "$v/karamel/krmllib/dist/minimal")
    local small=(-DFVDEP_SHA256_ONESHOT_MAX=127 -DFVDEP_SHA256_CHUNK=64
        -DFVDEP_SHA256_TOTAL_MAX=513)
    local srcs=(tests/fuzz/sha256.c c/fvdep_sha256_core.c "$v/gcc-compatible/Hacl_Hash_SHA2.c")
    mkdir -p "$out/bin"
    case "$mode" in
    cov) cov_c "$bin" "${inc[@]}" "${small[@]}" -- "${srcs[@]}" -- -lm -ldl -lpthread ;;
    replay)
        gcc -std=gnu11 -O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined \
            -fno-sanitize-recover=all "${inc[@]}" "${small[@]}" "${srcs[@]}" tests/fuzz/replay.c \
            -o "$bin" >&2 || die "sha256: build failed"
        ;;
    *) die "build sha256: mode cov | replay" ;;
    esac
    printf '%s\n' "$bin"
}

# sys-actions: the shim + guard (c/fvdep_sys.c) over the Lean runtime alone (no module).
build_sys_actions() {
    local mode="$1" bin="$out/bin/sys-actions-$1"
    toolchain
    local srcs=(tests/fuzz/sys_actions.c c/fvdep_sys.c)
    # The runtime's IO errors are Init's exports: both archives in one group.
    local rt=(-L"$tc/lib/lean" "-Wl,--start-group" -lInit -lleanrt "-Wl,--end-group" -L"$tc/lib"
        -l:libc++.a -l:libc++abi.a -l:libgmp.a -l:libuv.a -lpthread -ldl -lrt -lm)
    mkdir -p "$out/bin"
    case "$mode" in
    cov) cov_c "$bin" -I c -I "$tc/include" -- "${srcs[@]}" -- "${rt[@]}" ;;
    replay)
        gcc -std=gnu11 -O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined \
            -fno-sanitize-recover=all -I c -I "$tc/include" "${srcs[@]}" tests/fuzz/replay.c \
            -o "$bin" "${rt[@]}" >&2 || die "sys-actions: build failed"
        ;;
    *) die "build sys-actions: mode cov | replay" ;;
    esac
    printf '%s\n' "$bin"
}

build() {
    if lean_target "$1" >/dev/null; then
        build_lean "$1" "$2"
    elif [[ $1 == sha256 ]]; then
        build_sha256 "$2"
    elif [[ $1 == sys-actions ]]; then
        build_sys_actions "$2"
    else
        die "unknown target $1 (${TARGETS[*]})"
    fi
}

corpus() { git ls-files -co --exclude-standard -- "tests/fuzz/$1/" | sort; }

replay() {
    local targets=("$@") t bin rc=0 n log
    [[ ${#targets[@]} -gt 0 ]] || targets=("${TARGETS[@]}")
    log="$(mktemp)"
    for t in "${targets[@]}"; do
        mapfile -t inputs < <(corpus "$t")
        if [[ ${#inputs[@]} -eq 0 ]]; then
            printf 'fuzz-replay: %s: no corpus in tests/fuzz/%s/\n' "$t" "$t"
            rc=1
            continue
        fi
        bin="$(build "$t" replay)" || {
            rc=1
            continue
        }
        if "$bin" "${inputs[@]}" >/dev/null 2>"$log"; then
            printf 'fuzz-replay: %s: %d inputs\n' "$t" "${#inputs[@]}"
        else
            n=$?
            # The input it died on (the driver names each before running it) + the first lines
            # of the failure (a panic's message precedes the runtime's backtrace).
            printf 'fuzz-replay: %s: rc %d at %s\n' "$t" "$n" \
                "$(grep '^replay ' "$log" | tail -n 1 | cut -d' ' -f2)"
            grep -v '^replay ' "$log" | head -n 5
            rc=1
        fi
    done
    rm -f -- "$log"
    return "$rc"
}

campaign() { engine_run "$1" "$2" "${3:-cov}" "$(build "$1" "${3:-cov}")"; }

engine_run() {
    local t="$1" secs="$2" mode="$3" bin="$4" dir
    [[ -x $bin ]] || die "$bin: not built (fuzz.sh build $t $mode)"
    engine
    dir="$out/out/$t$([[ $mode == cov ]] || printf -- '-%s' "$mode")"
    rm -rf -- "$dir"
    mkdir -p "$dir"
    AFL_SKIP_CPUFREQ=1 AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 AFL_NO_UI=1 AFL_NO_AFFINITY=1 \
        LEAN_ABORT_ON_PANIC=1 "$afl/afl-fuzz" -V "$secs" -i "tests/fuzz/$t" -o "$dir" -- "$bin" \
        >"$dir/log" 2>&1 || {
        tail -n 20 "$dir/log" >&2
        die "$t: afl-fuzz failed"
    }
    printf 'campaign %s %s %ss:' "$t" "$mode" "$secs"
    local keys='execs_done|execs_per_sec|corpus_count|edges_found|total_edges|saved_crashes'
    awk -F' *: *' -v keys="^($keys|saved_hangs)$" '$1 ~ keys { printf " %s=%s", $1, $2 }
        END { print "" }' "$dir/default/fuzzer_stats"
    # A crash or a hang = red: each input is a finding (pinned in tests/fuzz/<target>/ + fixed).
    local found
    found="$(find "$dir/default/crashes" "$dir/default/hangs" -type f -name 'id*' 2>/dev/null |
        sort)"
    [[ -z $found ]] || {
        printf '%s\n' "$found"
        return 1
    }
}

cmin() {
    local t="$1" bin in="$out/cmin-in/$1" dir="$out/cmin/$1" seeds
    bin="$(build "$t" cov)"
    rm -rf -- "$in" "$dir"
    mkdir -p "$in" "$out/cmin" # afl-cmin creates its -o directory, never a parent
    mapfile -t seeds < <(corpus "$t")
    cp -- "${seeds[@]}" "$in/"
    find "$out/out/$t/default/queue" -maxdepth 1 -type f -name 'id*' -exec cp -- {} "$in/" \; \
        2>/dev/null || true
    # Input by file (`@@`): over stdin, 5.03c's afl-cmin feeds aflpp_driver's shared-memory loop no
    # test case ⇒ every input reads as a crash.
    AFL_SKIP_CPUFREQ=1 AFL_NO_AFFINITY=1 LEAN_ABORT_ON_PANIC=1 \
        "$afl/afl-cmin" -i "$in" -o "$dir" -- "$bin" @@ >&2 || die "$t: afl-cmin failed"
    printf 'cmin %s: %d → %d inputs in %s\n' "$t" "$(find "$in" -type f | wc -l)" \
        "$(find "$dir" -type f | wc -l)" "$dir"
}

pin() {
    local v="$1" tmp line
    tmp="$(mktemp)"
    line="https://github.com/AFLplusplus/AFLplusplus/archive/refs/tags/v$v.tar.gz"
    curl -fsSL --max-time 300 -o "$tmp" "$line" || die "fetch $line failed"
    printf 'afl++ %s source %s %s\n' "$v" "$(sha "$tmp")" "$line"
    rm -f -- "$tmp"
}

case "${1:-}" in
engine) engine ;;
build) [[ $# -eq 3 ]] || die "usage: fuzz.sh build TARGET MODE"; build "$2" "$3" ;;
replay) shift; replay "$@" ;;
campaign)
    [[ $# -ge 3 ]] || die "usage: fuzz.sh campaign TARGET SECONDS [MODE]"
    campaign "$2" "$3" "${4:-cov}"
    ;;
run)
    [[ $# -ge 3 ]] || die "usage: fuzz.sh run TARGET SECONDS [MODE]"
    engine_run "$2" "$3" "${4:-cov}" "$out/bin/$2-${4:-cov}"
    ;;
cmin) [[ $# -eq 2 ]] || die "usage: fuzz.sh cmin TARGET"; cmin "$2" ;;
pin) [[ $# -eq 2 ]] || die "usage: fuzz.sh pin VERSION"; pin "$2" ;;
*)
    die "usage: fuzz.sh engine | build TARGET MODE | replay [TARGET…] |" \
        "campaign TARGET SECONDS [MODE] | run TARGET SECONDS [MODE] | cmin TARGET | pin VERSION"
    ;;
esac
