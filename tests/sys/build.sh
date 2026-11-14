#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname -- "$0")/../.."
mkdir -p tests/sys/.build
prefix=$(lean --print-prefix)
common=(-std=gnu11 -O1 -g -Wall -Wextra -Werror -pthread)
headers=(-I"$prefix/include" -Ic)
libs=(-L"$prefix/lib/lean" "-Wl,-rpath,$prefix/lib/lean" -lleanshared -lInit_shared)
gcc -std=gnu11 -O2 -fPIC -shared -Wall -Wextra -Werror -pthread \
    tests/sys/fault.c -o tests/sys/.build/fault.so
gcc -std=gnu11 -O2 -Wall -Wextra -Werror tests/sys/control.c -o tests/sys/.build/control
gcc "${common[@]}" "${headers[@]}" tests/sys/native.c c/fvdep_sys.c \
    "${libs[@]}" -o tests/sys/.build/native
gcc "${common[@]}" -fsanitize=address,undefined -fno-omit-frame-pointer \
    "${headers[@]}" tests/sys/native.c c/fvdep_sys.c "${libs[@]}" \
    -o tests/sys/.build/native-asan
gcc "${common[@]}" -fsanitize=address,undefined -fno-omit-frame-pointer \
    "${headers[@]}" tests/sys/native.c c/fvdep_sys.c tests/sys/leak-canary.c \
    "${libs[@]}" -Wl,--wrap=fvdep_sys_open_file -o tests/sys/.build/native-leak-canary
for sanitizer in address undefined; do
    gcc "${common[@]}" -fsanitize="$sanitizer" -fno-omit-frame-pointer \
        tests/sys/san-control.c -o "tests/sys/.build/san-control-$sanitizer"
done
(cd tool && lake build fvdep-dev)
(cd tests/sys && lake build sys-extra)
