#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
(cd tool && lake build fvdep-cli fvdep-dev)
mkdir -p tests/index/.build
cc -shared -fPIC -O2 -Wall -Wextra -Werror tests/index/fault.c \
  -o tests/index/.build/fault.so -ldl
cc -DFAULT_CONTROL -O2 -Wall -Wextra -Werror tests/index/fault.c \
  -o tests/index/.build/fault-control -ldl
mkdir -p tests/index/.build/.lake/fvdep-index
printf 'control\n' > tests/index/.build/.lake/fvdep-index/control.olean
env FVDEP_INDEX_FAULT=load tests/index/.build/fault-control \
  tests/index/.build/.lake/fvdep-index/control.olean
env FVDEP_INDEX_FAULT=write tests/index/.build/fault-control \
  tests/index/.build/.index.json.tmp-control
printf 'CONTROL load-write-fault PASS\n'
rm -rf tests/index/.build/.lake
python3 -I tests/index/suite.py \
  --binary tool/.lake/build/bin/fvdep --dev tool/.lake/build/bin/fvdep-dev
