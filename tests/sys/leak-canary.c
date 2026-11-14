#include "fvdep_sys.h"
#include <stdlib.h>

extern lean_obj_res __real_fvdep_sys_open_file(b_lean_obj_arg path, uint32_t mode);

__attribute__((noinline)) static void owned_leak(void) {
    volatile unsigned char *p = malloc(8193);
    if (!p) abort();
    p[0] = 1;
}

LEAN_EXPORT lean_obj_res __wrap_fvdep_sys_open_file(b_lean_obj_arg path, uint32_t mode) {
    owned_leak();
    return __real_fvdep_sys_open_file(path, mode);
}
