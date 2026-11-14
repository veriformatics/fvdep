/* Fuzz target `sys-actions` (contract docs/contracts/U3-codecs.md "Fuzz"; F1 + F6): action
 * sequences over the persistence shim + writer guard (c/fvdep_sys.c) in a private directory —
 * opens, writes (offset + count from the input: the shim's bounds check), reads, syncs, closes,
 * renames, unlinks, flock + the guard's new / acquire / mark-closed / release / drop, the guarded
 * operations in FvdepIO.Sys.Writer.run's order. The Lean runtime alone is initialized (the shim
 * needs its allocator, IO results + external class: no module). Every answer must be an IO success
 * holding `Except Nat Nat` (`read`: `Except Nat ByteArray` of at most the requested bytes); any
 * other shape aborts. After each input every descriptor it left open is closed + the directory
 * emptied. Descriptor ownership moves into a writer at `writer_new`: the harness never closes a
 * writer's descriptor itself. */
#include "fvdep_sys.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

enum { NAMES = 3, SLOTS = 4, WRITERS = 2, MODE = 0644 };

static const char *const names[NAMES] = {"a", "b", ".fvdep-writer.lock"};
static char dir[64];
static lean_object *dir_path, *paths[NAMES];
static int fds[SLOTS];
static lean_object *writers[WRITERS];

struct answer {
    int ok;
    size_t value;
};

/* An `Except Nat Nat` IO answer (`bytes` set: `Except Nat ByteArray`, its size ≤ `limit`). */
static struct answer take(lean_object *r, int bytes, size_t limit) {
    if (!lean_io_result_is_ok(r)) abort();
    lean_object *v = lean_io_result_get_value(r);
    if (lean_is_scalar(v) || lean_obj_tag(v) > 1 || lean_ctor_num_objs(v) != 1) abort();
    struct answer a = {lean_obj_tag(v) == 1, 0};
    lean_object *x = lean_ctor_get(v, 0);
    if (a.ok && bytes) {
        if (lean_is_scalar(x) || !lean_is_sarray(x) || lean_sarray_size(x) > limit) abort();
        a.value = lean_sarray_size(x);
    } else {
        if (!lean_is_scalar(x)) abort();
        a.value = lean_unbox(x);
    }
    lean_dec(r);
    return a;
}

static void unit(lean_object *r) {
    if (!lean_io_result_is_ok(r)) abort();
    lean_dec(r);
}

static void close_slot(unsigned s) {
    if (fds[s] >= 0) (void)take(fvdep_sys_close((uint32_t)fds[s]), 0, 0);
    fds[s] = -1;
}

static void opened(unsigned s, lean_object *r) {
    close_slot(s);
    struct answer a = take(r, 0, 0);
    if (a.ok) fds[s] = (int)a.value;
}

/* A slot's descriptor, or one no open returns (EBADF paths). */
static uint32_t fd_of(unsigned s) { return fds[s] >= 0 ? (uint32_t)fds[s] : 1000000u; }

/* Under the guard: the writer's (fd, closed), then `act` unless closed, then release. */
static void guarded(unsigned w, int act, lean_object *payload, size_t off, size_t count) {
    if (writers[w] == NULL) return;
    lean_object *r = fvdep_sys_writer_acquire(writers[w]);
    if (!lean_io_result_is_ok(r)) abort();
    lean_object *pair = lean_io_result_get_value(r);
    if (lean_is_scalar(pair) || lean_ctor_num_objs(pair) != 2) abort();
    uint32_t fd = lean_unbox_uint32(lean_ctor_get(pair, 0));
    int closed = lean_unbox(lean_ctor_get(pair, 1)) != 0;
    lean_dec(r);
    if (!closed) {
        switch (act) {
        case 0: /* close: mark first, then the one close attempt */
            unit(fvdep_sys_writer_mark_closed(writers[w]));
            (void)take(fvdep_sys_close(fd), 0, 0);
            break;
        case 1: {
            struct answer a = take(fvdep_sys_write(fd, payload, off, count), 0, 0);
            if (a.ok && a.value > count) abort();
            break;
        }
        default:
            (void)take(fvdep_sys_sync(fd), 0, 0);
        }
    }
    unit(fvdep_sys_writer_release(writers[w]));
}

static void drop_writer(unsigned w) {
    if (writers[w] != NULL) lean_dec(writers[w]); /* the finalizer closes a descriptor still open */
    writers[w] = NULL;
}

static void reset(void) {
    for (unsigned w = 0; w < WRITERS; w++) drop_writer(w);
    for (unsigned s = 0; s < SLOTS; s++) close_slot(s);
    for (unsigned n = 0; n < NAMES; n++) (void)take(fvdep_sys_unlink(paths[n]), 0, 0);
}

static void finish(void) {
    reset();
    for (unsigned n = 0; n < NAMES; n++) lean_dec(paths[n]);
    lean_dec(dir_path);
    (void)rmdir(dir);
    lean_finalize_thread(); /* frees the thread heap: LeakSanitizer sees no runtime residue */
}

int LLVMFuzzerInitialize(int *argc, char ***argv) {
    (void)argc;
    (void)argv;
    lean_initialize_runtime_module();
    lean_initialize_thread();
    strcpy(dir, "/tmp/fvdep-sys-actions.XXXXXX");
    if (mkdtemp(dir) == NULL) abort();
    dir_path = lean_mk_string(dir);
    for (unsigned n = 0; n < NAMES; n++) {
        char p[96];
        snprintf(p, sizeof p, "%s/%s", dir, names[n]);
        paths[n] = lean_mk_string(p);
    }
    for (unsigned s = 0; s < SLOTS; s++) fds[s] = -1;
    atexit(finish);
    return 0;
}

/* Two bytes per action: an op + its argument; write offsets + counts read the next two bytes
 * (argument bit 7 set: counted back from SIZE_MAX, the bounds check's overflow edge). */
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    lean_object *payload = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(payload), data, size);
    size_t i = 0;
    while (i + 1 < size) {
        uint8_t op = data[i], arg = data[i + 1];
        i += 2;
        unsigned s = arg % SLOTS, n = arg % NAMES, w = arg % WRITERS;
        size_t off = i < size ? data[i] : 0, count = i + 1 < size ? data[i + 1] : 0;
        if (arg & 0x80) off = SIZE_MAX - off;
        switch (op % 16) {
        case 0: opened(s, fvdep_sys_open_file(paths[n], MODE)); break;
        case 1: opened(s, fvdep_sys_open_read(paths[n])); break;
        case 2: opened(s, fvdep_sys_open_lock(paths[n])); break;
        case 3: opened(s, fvdep_sys_open_dir(dir_path)); break;
        case 4: {
            struct answer a = take(fvdep_sys_write(fd_of(s), payload, off, count), 0, 0);
            if (a.ok && a.value > count) abort();
            i += 2;
            break;
        }
        case 5: (void)take(fvdep_sys_read(fd_of(s), count), 1, count); i += 2; break;
        case 6: (void)take(fvdep_sys_sync(fd_of(s)), 0, 0); break;
        case 7: close_slot(s); break;
        case 8: (void)take(fvdep_sys_rename(paths[n], paths[(n + 1) % NAMES]), 0, 0); break;
        case 9: (void)take(fvdep_sys_unlink(paths[n]), 0, 0); break;
        case 10: (void)take(fvdep_sys_lock(fd_of(s)), 0, 0); break;
        case 11:
            if (fds[s] >= 0 && writers[w] == NULL) {
                lean_object *r = fvdep_sys_writer_new((uint32_t)fds[s], paths[n]);
                if (!lean_io_result_is_ok(r)) abort();
                writers[w] = lean_io_result_get_value(r);
                lean_inc(writers[w]);
                lean_dec(r);
                fds[s] = -1; /* owned by the writer now */
            }
            break;
        case 12: guarded(w, 0, payload, 0, 0); break;
        case 13: guarded(w, 1, payload, off, count); i += 2; break;
        case 14: drop_writer(w); break;
        default: guarded(w, 2, payload, 0, 0);
        }
    }
    reset();
    lean_dec(payload);
    return 0;
}
