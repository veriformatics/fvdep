#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

/* Test-only. Script = OP START COUNT ACTION ARG; START is 1-based per OP, '*' = all calls.
 * ACTION = pass | errno | posterrno | short | zero | over | crash | aftercrash | virtual.
 * Linux syscalls implement the real leg; trace/script I/O bypasses the hooks entirely. */
struct rule { char op[32], action[32]; uint64_t start, count, arg, left; };
struct counter { char op[32]; uint64_t n; };
struct remembered { char path[PATH_MAX]; bool dir; };
static struct rule rules[256];
static struct counter counters[32];
static struct remembered fds[1024];
static size_t nrules, ncounters, root_len;
static uint64_t sequence;
static char root[PATH_MAX];
static int trace_fd = -1;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static void raw_write_all(int fd, const char *p, size_t n) {
    while (n) {
        long k = syscall(SYS_write, fd, p, n);
        if (k < 0 && errno == EINTR) continue;
        if (k <= 0) _exit(122);
        p += (size_t)k;
        n -= (size_t)k;
    }
}

static void copy_path(char out[PATH_MAX], const char *s) {
    size_t n = strlen(s);
    if (n >= PATH_MAX) { out[0] = '\0'; return; }
    memcpy(out, s, n + 1);
}

static void initialize(void) {
    int saved = errno;
    const char *r = getenv("FVDEP_SYS_ROOT");
    if (r) copy_path(root, r);
    root_len = strlen(root);
    while (root_len > 1 && root[root_len - 1] == '/') root[--root_len] = '\0';
    const char *trace = getenv("FVDEP_SYS_TRACE");
    if (trace && root_len) trace_fd = (int)syscall(SYS_openat, AT_FDCWD, trace,
        O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0600);
    const char *script = getenv("FVDEP_SYS_SCRIPT");
    if (script && root_len) {
        int fd = (int)syscall(SYS_openat, AT_FDCWD, script, O_RDONLY | O_CLOEXEC, 0);
        if (fd < 0) _exit(120);
        char text[65536];
        size_t used = 0;
        for (;;) {
            long n = syscall(SYS_read, fd, text + used, sizeof(text) - 1 - used);
            if (n < 0 && errno == EINTR) continue;
            if (n < 0) _exit(120);
            if (!n) break;
            used += (size_t)n;
            if (used == sizeof(text) - 1) _exit(120);
        }
        (void)syscall(SYS_close, fd);
        text[used] = '\0';
        char *save = NULL;
        for (char *line = strtok_r(text, "\n", &save); line; line = strtok_r(NULL, "\n", &save)) {
            if (!line[0] || line[0] == '#') continue;
            if (nrules == 256) _exit(120);
            struct rule *q = &rules[nrules++];
            unsigned long long start, count, arg;
            if (sscanf(line, "%31s %llu %llu %31s %llu", q->op, &start, &count,
                       q->action, &arg) != 5 || !start || !count) _exit(120);
            q->start = (uint64_t)start;
            q->count = (uint64_t)count;
            q->arg = q->left = (uint64_t)arg;
        }
    }
    errno = saved;
}

static bool owned(const char *path) {
    size_t n = strlen(path);
    return root_len && n >= root_len && strncmp(path, root, root_len) == 0 &&
        (n == root_len || path[root_len] == '/');
}

static void absolute_path(int dirfd, const char *path, char out[PATH_MAX]) {
    if (path[0] == '/') { copy_path(out, path); return; }
    char base[PATH_MAX];
    if (dirfd == AT_FDCWD) {
        if (syscall(SYS_getcwd, base, sizeof(base)) < 0) { out[0] = '\0'; return; }
    } else {
        char proc[64];
        (void)snprintf(proc, sizeof(proc), "/proc/self/fd/%d", dirfd);
        long n = syscall(SYS_readlinkat, AT_FDCWD, proc, base, sizeof(base) - 1);
        if (n < 0) { out[0] = '\0'; return; }
        base[n] = '\0';
    }
    size_t a = strlen(base), b = strlen(path);
    if (a + b + 2 > PATH_MAX) { out[0] = '\0'; return; }
    memcpy(out, base, a);
    out[a] = '/';
    memcpy(out + a + 1, path, b + 1);
}

static bool fd_path(int fd, char path[PATH_MAX], bool *is_dir) {
    char proc[64];
    (void)snprintf(proc, sizeof(proc), "/proc/self/fd/%d", fd);
    long n = syscall(SYS_readlinkat, AT_FDCWD, proc, path, PATH_MAX - 1);
    if (n >= 0) {
        path[n] = '\0';
        struct stat st;
        *is_dir = syscall(SYS_fstat, fd, &st) == 0 && S_ISDIR(st.st_mode);
        return owned(path);
    }
    if (fd >= 0 && fd < 1024 && fds[fd].path[0]) {
        copy_path(path, fds[fd].path);
        *is_dir = fds[fd].dir;
        return owned(path);
    }
    path[0] = '\0';
    *is_dir = false;
    return false;
}

static void remember(int fd, const char *path, bool dir) {
    if (fd >= 0 && fd < 1024) {
        copy_path(fds[fd].path, owned(path) ? path : "");
        fds[fd].dir = dir;
    }
}

static uint64_t next_index(const char *op) {
    for (size_t i = 0; i < ncounters; i++)
        if (strcmp(counters[i].op, op) == 0) return ++counters[i].n;
    if (ncounters == 32) _exit(121);
    (void)snprintf(counters[ncounters].op, sizeof(counters[ncounters].op), "%s", op);
    counters[ncounters].n = 1;
    ncounters++;
    return 1;
}

static struct rule *select_rule(const char *op, uint64_t index) {
    for (size_t i = 0; i < nrules; i++) {
        struct rule *q = &rules[i];
        uint64_t at = strcmp(q->op, "*") == 0 ? sequence : index;
        if ((strcmp(q->op, op) == 0 || strcmp(q->op, "*") == 0) &&
            at >= q->start && at - q->start < q->count) return q;
    }
    return NULL;
}

static size_t append_hex(char *out, size_t pos, const char *s) {
    const char digits[] = "0123456789abcdef";
    for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
        out[pos++] = digits[*p >> 4];
        out[pos++] = digits[*p & 15];
    }
    return pos;
}

static void event(const char *op, uint64_t index, const char *path, const char *aux,
                  int fd, unsigned flags, uint64_t count, long result, int err,
                  const char *action) {
    if (trace_fd < 0) _exit(123);
    char line[PATH_MAX * 4 + 512];
    int written = snprintf(line, sizeof(line), "%llu\t%s\t%llu\t%d\t%u\t%llu\t%ld\t%d\t%s\t",
        (unsigned long long)sequence, op, (unsigned long long)index, fd, flags,
        (unsigned long long)count, result, err, action);
    if (written < 0 || (size_t)written >= sizeof(line)) _exit(123);
    size_t n = append_hex(line, (size_t)written, path);
    line[n++] = '\t';
    n = append_hex(line, n, aux);
    line[n++] = '\n';
    raw_write_all(trace_fd, line, n);
}

static bool action_is(const struct rule *q, const char *name) {
    return q && strcmp(q->action, name) == 0;
}

static struct rule *begin(const char *op, uint64_t *index, const char *path,
                          const char *aux, int fd, unsigned flags, uint64_t count) {
    sequence++;
    *index = next_index(op);
    struct rule *q = select_rule(op, *index);
    if (action_is(q, "crash")) {
        event(op, *index, path, aux, fd, flags, count, -1, 0, "crash");
        _exit(99);
    }
    return q;
}

static long finish(const char *op, uint64_t index, const char *path, const char *aux,
                   int fd, unsigned flags, uint64_t count, long value, int err,
                   const struct rule *q) {
    if (action_is(q, "posterrno")) { value = -1; err = (int)q->arg; }
    event(op, index, path, aux, fd, flags, count, value, value < 0 ? err : 0,
          q ? q->action : "pass");
    if (action_is(q, "aftercrash")) _exit(99);
    (void)pthread_mutex_unlock(&mutex);
    errno = value < 0 ? err : 0;
    return value;
}

static int open_common(int dirfd, const char *path, int flags, unsigned mode) {
    (void)pthread_once(&once, initialize);
    char full[PATH_MAX];
    absolute_path(dirfd, path, full);
    if (!owned(full)) {
        int n = (int)syscall(SYS_openat, dirfd, path, flags, mode);
        if (n >= 0) {
            (void)pthread_mutex_lock(&mutex);
            remember(n, "", false);
            (void)pthread_mutex_unlock(&mutex);
        }
        return n;
    }
    (void)pthread_mutex_lock(&mutex);
    const char *op = (flags & O_DIRECTORY) ? "openDir" :
        ((flags & O_ACCMODE) == O_RDWR && (flags & O_CREAT)) ? "openLock" :
        (flags & O_CREAT) ? "create" : "openRead";
    uint64_t at;
    struct rule *q = begin(op, &at, full, "", -1, (unsigned)flags, mode);
    long value;
    if (action_is(q, "errno")) { errno = (int)q->arg; value = -1; }
    else value = syscall(SYS_openat, dirfd, path, flags, mode);
    int err = errno;
    if (value >= 0) remember((int)value, full, (flags & O_DIRECTORY) != 0);
    return (int)finish(op, at, full, "", -1, (unsigned)flags, mode, value, err, q);
}

static unsigned open_mode(int flags, va_list ap) {
    if ((flags & O_CREAT) || ((flags & O_TMPFILE) == O_TMPFILE)) return va_arg(ap, unsigned);
    return 0;
}

int open(const char *path, int flags, ...) {
    va_list ap; va_start(ap, flags); unsigned mode = open_mode(flags, ap); va_end(ap);
    return open_common(AT_FDCWD, path, flags, mode);
}
int open64(const char *path, int flags, ...) {
    va_list ap; va_start(ap, flags); unsigned mode = open_mode(flags, ap); va_end(ap);
    return open_common(AT_FDCWD, path, flags, mode);
}
int __open_2(const char *path, int flags) { return open_common(AT_FDCWD, path, flags, 0); }
int __open64_2(const char *path, int flags) { return open_common(AT_FDCWD, path, flags, 0); }
int openat(int dirfd, const char *path, int flags, ...) {
    va_list ap; va_start(ap, flags); unsigned mode = open_mode(flags, ap); va_end(ap);
    return open_common(dirfd, path, flags, mode);
}
int openat64(int dirfd, const char *path, int flags, ...) {
    va_list ap; va_start(ap, flags); unsigned mode = open_mode(flags, ap); va_end(ap);
    return open_common(dirfd, path, flags, mode);
}

static long descriptor_call(const char *base, int fd, void *buffer, size_t count, int extra) {
    (void)pthread_once(&once, initialize);
    char path[PATH_MAX]; bool dir;
    (void)pthread_mutex_lock(&mutex);
    bool match = fd_path(fd, path, &dir);
    const char *op = dir && strcmp(base, "sync") == 0 ? "syncDir" :
        dir && strcmp(base, "close") == 0 ? "closeDir" : base;
    if (!match) {
        (void)pthread_mutex_unlock(&mutex);
        if (strcmp(base, "write") == 0) return syscall(SYS_write, fd, buffer, count);
        if (strcmp(base, "read") == 0) return syscall(SYS_read, fd, buffer, count);
        if (strcmp(base, "sync") == 0) return syscall(SYS_fsync, fd);
        if (strcmp(base, "close") == 0) return syscall(SYS_close, fd);
        return syscall(SYS_flock, fd, extra);
    }
    uint64_t at;
    struct rule *q = begin(op, &at, path, "", fd, (unsigned)extra, count);
    size_t actual_count = count;
    if (action_is(q, "short") && q->arg < actual_count) actual_count = (size_t)q->arg;
    long value;
    if (action_is(q, "errno")) { value = -1; errno = (int)q->arg; }
    else if (action_is(q, "zero")) value = 0;
    else if (action_is(q, "over")) value = (long)(count + q->arg);
    else if (action_is(q, "virtual") && strcmp(base, "read") == 0) {
        size_t n = q->left < count ? (size_t)q->left : count;
        memset(buffer, 0, n);
        q->left -= n;
        value = (long)n;
    } else if (strcmp(base, "write") == 0) value = syscall(SYS_write, fd, buffer, actual_count);
    else if (strcmp(base, "read") == 0) value = syscall(SYS_read, fd, buffer, actual_count);
    else if (strcmp(base, "sync") == 0) value = syscall(SYS_fsync, fd);
    else if (strcmp(base, "close") == 0) value = syscall(SYS_close, fd);
    else value = syscall(SYS_flock, fd, extra);
    int err = errno;
    return finish(op, at, path, "", fd, (unsigned)extra, count, value, err, q);
}

ssize_t write(int fd, const void *buf, size_t count) {
    return (ssize_t)descriptor_call("write", fd, (void *)buf, count, 0);
}
ssize_t read(int fd, void *buf, size_t count) {
    return (ssize_t)descriptor_call("read", fd, buf, count, 0);
}
int fsync(int fd) { return (int)descriptor_call("sync", fd, NULL, 0, 0); }
int close(int fd) { return (int)descriptor_call("close", fd, NULL, 0, 0); }
int flock(int fd, int operation) { return (int)descriptor_call("lock", fd, NULL, 0, operation); }

static int path_call(const char *op, const char *source, const char *target) {
    (void)pthread_once(&once, initialize);
    char a[PATH_MAX], b[PATH_MAX];
    absolute_path(AT_FDCWD, source, a);
    absolute_path(AT_FDCWD, target ? target : source, b);
    if (!owned(a) || !owned(b)) return (int)(target ? syscall(SYS_rename, source, target) : syscall(SYS_unlink, source));
    (void)pthread_mutex_lock(&mutex);
    uint64_t at;
    const char *path = target ? b : a;
    struct rule *q = begin(op, &at, path, target ? a : "", -1, 0, 0);
    long value;
    if (action_is(q, "errno")) { value = -1; errno = (int)q->arg; }
    else value = target ? syscall(SYS_rename, source, target) : syscall(SYS_unlink, source);
    int err = errno;
    return (int)finish(op, at, path, target ? a : "", -1, 0, 0, value, err, q);
}
int rename(const char *source, const char *target) { return path_call("rename", source, target); }
int unlink(const char *path) { return path_call("unlink", path, NULL); }
