/* Fuzz target `sha256` (contract docs/contracts/U3-codecs.md "Fuzz"): the Lean-free C core over
 * HACL* (c/fvdep_sha256_core.c), built with S5's lowered limits (tools/fuzz.sh) so small inputs
 * reach the chunk loop + the total limit. One input = a split plan + a message: the one-shot digest
 * equals the streamed one (whole blocks absorbed in plan-sized steps, the tail squeezed), and both
 * refuse together at the total limit; a mismatch aborts. */
#include "fvdep_sha256_core.h"

#include <stdlib.h>
#include <string.h>

int LLVMFuzzerInitialize(int *argc, char ***argv) {
    (void)argc;
    (void)argv;
    return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size == 0) return 0;
    /* Byte 0: the plan's length k ≤ 15; the next k bytes: blocks per absorb step (0 = 1). */
    size_t k = data[0] & 15;
    if (size < 1 + k) return 0;
    const uint8_t *plan = data + 1, *msg = data + 1 + k;
    size_t n = size - 1 - k;
    uint8_t one[32], streamed[32];
    int refused_one = fvdep_sha256_raw(one, msg, n);
    uint32_t st[8];
    fvdep_sha256_init_raw(st);
    size_t whole = n - n % 64, off = 0, step = 0;
    while (off < whole) {
        size_t blocks = k ? plan[step++ % k] : 1;
        size_t len = (blocks ? blocks : 1) * 64;
        if (len > whole - off) len = whole - off;
        fvdep_sha256_absorb_raw(st, msg + off, len);
        off += len;
    }
    int refused_streamed = fvdep_sha256_squeeze_raw(st, msg + off, n - off, n, streamed);
    if ((refused_one != 0) != (refused_streamed != 0)) abort();
    if (refused_one == 0 && memcmp(one, streamed, sizeof one) != 0) abort();
    return 0;
}
