#define _GNU_SOURCE
#include "fvdep_sys.h"
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

struct answer { bool io, shape, ok; size_t number; lean_object *bytes; };
static atomic_uint checks, failures;

static bool expect(bool condition, const char *label) {
    checks++;
    if (!condition) { failures++; fprintf(stderr, "ASSERT %s\n", label); }
    return condition;
}

static lean_object *take_io(lean_object *r) {
    if (!expect(lean_io_result_is_ok(r), "IO result")) { lean_dec(r); return NULL; }
    lean_object *v = lean_io_result_get_value(r);
    lean_inc(v);
    lean_dec(r);
    return v;
}

static struct answer answer(lean_object *r, bool bytes) {
    struct answer a = { .io = lean_io_result_is_ok(r) };
    if (!a.io) { lean_dec(r); return a; }
    lean_object *v = lean_io_result_get_value(r);
    if (lean_is_scalar(v) || lean_obj_tag(v) > 1 || lean_ctor_num_objs(v) != 1) {
        lean_dec(r);
        return a;
    }
    a.shape = true;
    a.ok = lean_obj_tag(v) == 1;
    lean_object *value = lean_ctor_get(v, 0);
    if (bytes && a.ok) {
        if (lean_is_scalar(value)) a.shape = false;
        else { a.number = lean_sarray_size(value); a.bytes = value; lean_inc(value); }
    } else if (lean_is_scalar(value)) a.number = lean_unbox(value);
    else a.shape = false;
    lean_dec(r);
    return a;
}

static void print_answer(struct answer a, bool unchanged) {
    printf("{\"io\":%s,\"shape\":%s,\"ok\":%s,\"number\":%zu,\"unchanged\":%s,\"bytes\":\"",
        a.io ? "true" : "false", a.shape ? "true" : "false", a.ok ? "true" : "false",
        a.number, unchanged ? "true" : "false");
    if (a.bytes) for (size_t i = 0; i < lean_sarray_size(a.bytes); i++)
        printf("%02x", lean_sarray_cptr(a.bytes)[i]);
    printf("\",\"checks\":%u,\"failures\":%u}\n", checks, failures);
    if (a.bytes) lean_dec(a.bytes);
}

static bool join_path(char out[PATH_MAX], const char *dir, const char *name) {
    int n = snprintf(out, PATH_MAX, "%s/%s", dir, name);
    return n >= 0 && n < PATH_MAX;
}

static bool acquire(lean_object *writer, unsigned *fd, bool *closed) {
    lean_object *pair = take_io(fvdep_sys_writer_acquire(writer));
    if (!pair) return false;
    bool good = !lean_is_scalar(pair) && lean_obj_tag(pair) == 0 && lean_ctor_num_objs(pair) == 2;
    if (expect(good, "guard pair shape")) {
        *fd = lean_unbox_uint32(lean_ctor_get(pair, 0));
        *closed = lean_unbox(lean_ctor_get(pair, 1)) != 0;
    }
    lean_dec(pair);
    return good;
}

static bool guard_unit(lean_object *result) {
    lean_object *v = take_io(result);
    if (!v) return false;
    lean_dec(v);
    return true;
}

struct thread_data { lean_object *writer; atomic_int started, acquired; bool good; unsigned fd; };
static void *guard_thread(void *arg) {
    struct thread_data *d = arg;
    lean_initialize_thread();
    atomic_store(&d->started, 1);
    unsigned fd = 0; bool closed = true;
    d->good = acquire(d->writer, &fd, &closed);
    d->fd = fd;
    atomic_store(&d->acquired, 1);
    if (d->good) d->good = guard_unit(fvdep_sys_writer_release(d->writer));
    lean_dec(d->writer);
    lean_finalize_thread();
    return NULL;
}

static int guard_test(const char *mode, const char *root) {
    char file[PATH_MAX], second[PATH_MAX];
    if (!join_path(file, root, "guard") || !join_path(second, root, "reused")) return 2;
    int fd = (int)syscall(SYS_openat, AT_FDCWD, file, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (fd < 0) return 2;
    lean_object *writer = take_io(fvdep_sys_writer_new((uint32_t)fd));
    if (!writer) { (void)syscall(SYS_close, fd); goto done; }
    if (!strcmp(mode, "guard-live")) {
        lean_dec(writer);
        errno = 0;
        long value = syscall(SYS_fcntl, fd, F_GETFD, 0);
        expect(value == -1 && errno == EBADF, "live guard finalizer closes descriptor");
        if (value != -1) (void)syscall(SYS_close, fd);
        goto done;
    }
    unsigned observed = 0; bool closed = true;
    if (!acquire(writer, &observed, &closed)) { lean_dec(writer); (void)syscall(SYS_close, fd); goto done; }
    bool sane = expect(observed == (unsigned)fd && !closed, "first guard acquisition");
    if (!sane) { (void)guard_unit(fvdep_sys_writer_release(writer)); lean_dec(writer); (void)syscall(SYS_close, fd); goto done; }
    if (!strcmp(mode, "guard-mutex")) {
        lean_mark_mt(writer);
        lean_inc(writer);
        struct thread_data d = { .writer = writer, .started = 0, .acquired = 0, .good = false, .fd = 0 };
        pthread_t thread;
        if (!expect(pthread_create(&thread, NULL, guard_thread, &d) == 0, "guard thread starts")) {
            lean_dec(writer);
            (void)guard_unit(fvdep_sys_writer_release(writer));
            lean_dec(writer);
            (void)syscall(SYS_close, fd);
            goto done;
        }
        struct timespec tick = { .tv_sec = 0, .tv_nsec = 1000000 };
        for (unsigned i = 0; i < 2000 && !atomic_load(&d.started); i++) nanosleep(&tick, NULL);
        expect(atomic_load(&d.started) == 1, "guard thread reaches acquire");
        for (unsigned i = 0; i < 30; i++) nanosleep(&tick, NULL);
        expect(atomic_load(&d.acquired) == 0, "second acquisition blocks while held");
        (void)guard_unit(fvdep_sys_writer_release(writer));
        struct timespec deadline;
        (void)clock_gettime(CLOCK_REALTIME, &deadline);
        deadline.tv_sec += 5;
        int joined = pthread_timedjoin_np(thread, NULL, &deadline);
        if (!expect(joined == 0, "guard thread unblocks")) _exit(124);
        expect(d.good && d.fd == (unsigned)fd, "guard thread owns the same descriptor");
        lean_dec(writer);
        errno = 0;
        long value = syscall(SYS_fcntl, fd, F_GETFD, 0);
        expect(value == -1 && errno == EBADF, "shared guard finalizer closes once");
        if (value != -1) (void)syscall(SYS_close, fd);
        goto done;
    }
    (void)guard_unit(fvdep_sys_writer_mark_closed(writer));
    struct answer c = answer(fvdep_sys_close((uint32_t)fd), false);
    expect(c.io && c.shape && c.ok, "explicit guarded close");
    (void)guard_unit(fvdep_sys_writer_release(writer));
    unsigned after_fd = 0; bool after_closed = false;
    if (acquire(writer, &after_fd, &after_closed)) {
        expect(after_fd == (unsigned)fd && after_closed, "closed flag persists");
        (void)guard_unit(fvdep_sys_writer_release(writer));
    }
    if (!strcmp(mode, "guard-reuse")) {
        int reused = (int)syscall(SYS_openat, AT_FDCWD, second, O_RDWR | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
        if (!expect(reused >= 0, "replacement descriptor opens")) { lean_dec(writer); goto done; }
        if (reused != fd) {
            expect(syscall(SYS_dup2, reused, fd) == fd, "force descriptor-number reuse");
            (void)syscall(SYS_close, reused);
        }
        lean_dec(writer);
        const char marker[] = "still-open";
        long n = syscall(SYS_write, fd, marker, sizeof(marker) - 1);
        expect(n == (long)sizeof(marker) - 1, "old guard finalizer keeps reused descriptor open");
        (void)syscall(SYS_close, fd);
    } else lean_dec(writer);
 done:
    printf("{\"guard_ok\":%s,\"checks\":%u,\"failures\":%u}\n", failures ? "false" : "true", checks, failures);
    return failures ? 1 : 0;
}

static void *runtime_thread(void *arg) {
    lean_initialize_thread();
    lean_object *s = lean_mk_string("F6-thread-control");
    *(int *)arg = strcmp(lean_string_cstr(s), "F6-thread-control") == 0;
    lean_dec(s);
    lean_finalize_thread();
    return NULL;
}

static int native_main(int argc, char **argv) {
    if (argc < 3 || argc > 5) return 2;
    const char *op = argv[1], *root = argv[2];
    if (!strcmp(op, "runtime-thread")) {
        int good = 0;
        pthread_t thread;
        if (pthread_create(&thread, NULL, runtime_thread, &good) != 0 ||
            pthread_join(thread, NULL) != 0) return 2;
        printf("{\"runtime_ok\":%s}\n", good ? "true" : "false");
        return good ? 0 : 1;
    }
    if (!strncmp(op, "guard-", 6)) return guard_test(op, root);
    size_t offset = argc >= 4 ? (size_t)strtoull(argv[3], NULL, 10) : 0;
    size_t count = argc >= 5 ? (size_t)strtoull(argv[4], NULL, 10) : 16;
    char file[PATH_MAX], source[PATH_MAX], target[PATH_MAX];
    if (!join_path(file, root, "file") || !join_path(source, root, "source") || !join_path(target, root, "target")) return 2;
    lean_object *p = lean_mk_string(file);
    lean_object *dir = lean_mk_string(root);
    lean_object *s = lean_mk_string(source), *t = lean_mk_string(target);
    lean_object *input = lean_alloc_sarray(1, 256, 256);
    unsigned char original[256];
    for (size_t i = 0; i < 256; i++) original[i] = (unsigned char)i;
    memcpy(lean_sarray_cptr(input), original, 256);
    struct answer a = { 0 };
    int fd = -1;
    bool returns_fd = false;
    if (!strcmp(op, "create")) { a = answer(fvdep_sys_open_file(p, 0644), false); returns_fd = true; }
    else if (!strcmp(op, "openDir")) { a = answer(fvdep_sys_open_dir(dir), false); returns_fd = true; }
    else if (!strcmp(op, "openRead")) { a = answer(fvdep_sys_open_read(p), false); returns_fd = true; }
    else if (!strcmp(op, "openLock")) { a = answer(fvdep_sys_open_lock(p), false); returns_fd = true; }
    else if (!strcmp(op, "rename")) a = answer(fvdep_sys_rename(s, t), false);
    else if (!strcmp(op, "unlink")) a = answer(fvdep_sys_unlink(p), false);
    else {
        bool directory = !strcmp(op, "syncDir") || !strcmp(op, "closeDir");
        fd = (int)syscall(SYS_openat, AT_FDCWD, directory ? root : file,
            directory ? O_RDONLY | O_DIRECTORY | O_CLOEXEC : O_RDWR | O_CLOEXEC, 0);
        if (fd < 0) { fprintf(stderr, "fixture open failed\n"); return 2; }
        if (!strcmp(op, "write")) a = answer(fvdep_sys_write((uint32_t)fd, input, offset, count), false);
        else if (!strcmp(op, "read")) a = answer(fvdep_sys_read((uint32_t)fd, count), true);
        else if (!strcmp(op, "sync") || !strcmp(op, "syncDir")) a = answer(fvdep_sys_sync((uint32_t)fd), false);
        else if (!strcmp(op, "close") || !strcmp(op, "closeDir")) a = answer(fvdep_sys_close((uint32_t)fd), false);
        else if (!strcmp(op, "lock")) a = answer(fvdep_sys_lock((uint32_t)fd), false);
        else { fprintf(stderr, "unknown native fixture\n"); return 2; }
    }
    if (returns_fd && a.io && a.shape && a.ok) (void)syscall(SYS_close, a.number);
    if (fd >= 0 && strcmp(op, "close") && strcmp(op, "closeDir")) (void)syscall(SYS_close, fd);
    bool unchanged = memcmp(lean_sarray_cptr(input), original, 256) == 0;
    expect(unchanged, "borrowed input unchanged");
    print_answer(a, unchanged);
    lean_dec(input); lean_dec(p); lean_dec(dir); lean_dec(s); lean_dec(t);
    return failures ? 1 : 0;
}

int main(int argc, char **argv) {
    lean_initialize_runtime_module();
    lean_initialize_thread();
    int result = native_main(argc, argv);
    lean_finalize_thread();
    return result;
}
