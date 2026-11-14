/* One Lean fuzz target (contract docs/contracts/U3-codecs.md "Fuzz"): FUZZ_ENTRY = the target
 * module's @[export] entry, FUZZ_INIT = its module initializer, FUZZ_IO = 1 for an IO entry.
 * Linked with aflpp_driver (engine) or tests/fuzz/replay.c (gate replay). */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void lean_initialize_runtime_module(void);
extern lean_object *FUZZ_INIT(uint8_t builtin);
#if FUZZ_IO
extern lean_object *FUZZ_ENTRY(lean_object *bytes, lean_object *world);
#else
extern uint8_t FUZZ_ENTRY(lean_object *bytes);
#endif

int LLVMFuzzerInitialize(int *argc, char ***argv) {
    (void)argc;
    (void)argv;
    /* A violated property panics: abort (SIGABRT) is what the engine + the replay count. */
    setenv("LEAN_ABORT_ON_PANIC", "1", 1);
    lean_initialize_runtime_module();
    lean_object *r = FUZZ_INIT(1);
    if (!lean_io_result_is_ok(r)) {
        lean_io_result_show_error(r);
        abort();
    }
    lean_dec_ref(r);
    lean_io_mark_end_initialization();
    return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(bytes), data, size);
#if FUZZ_IO
    lean_object *r = FUZZ_ENTRY(bytes, lean_io_mk_world());
    if (!lean_io_result_is_ok(r)) {
        lean_io_result_show_error(r);
        abort();
    }
    lean_dec_ref(r);
#else
    FUZZ_ENTRY(bytes);
#endif
    return 0;
}
