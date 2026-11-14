#include "fvdep_sha256_core.h"
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void hex(const uint8_t *b, size_t n) {
  for (size_t i = 0; i < n; ++i) printf("%02x", b[i]);
}
static uint8_t *read_file(const char *path, size_t *size) {
  FILE *f = fopen(path, "rb");
  if (!f || fseek(f, 0, SEEK_END)) exit(2);
  long n = ftell(f);
  if (n < 0 || fseek(f, 0, SEEK_SET)) exit(2);
  uint8_t *b = malloc((size_t)n + 1);
  if (!b || fread(b, 1, (size_t)n, f) != (size_t)n || fclose(f)) exit(2);
  *size = (size_t)n;
  return b;
}
int main(int argc, char **argv) {
  if (argc < 3) return 2;
  uint8_t out[48], pristine[48];
  memset(out, 0xa5, sizeof out);
  memcpy(pristine, out, sizeof out);
  if (!strcmp(argv[1], "refuse")) {
    uint32_t st[8];
    fvdep_sha256_init_raw(st);
    errno = 0;
    char *end;
    uint64_t total = strtoull(argv[2], &end, 10);
    if (errno || *end) return 2;
    int rc = fvdep_sha256_squeeze_raw(st, (const uint8_t *)"", 0, total, out + 8);
    if (rc) printf("refused:%s\n", memcmp(out, pristine, sizeof out) ? "changed" : "untouched");
    else { printf("ok:"); hex(out + 8, 32); puts(""); }
    return 0;
  }
  size_t n;
  uint8_t *b = read_file(argv[2], &n);
  uint8_t *copy = malloc(n + 1);
  if (!copy) return 2;
  memcpy(copy, b, n);
  int rc;
  if (!strcmp(argv[1], "raw")) {
    rc = fvdep_sha256_raw(out + 8, b, n);
  } else if (!strcmp(argv[1], "stream")) {
    uint32_t st[8];
    fvdep_sha256_init_raw(st);
    size_t full = n - n % 64;
    size_t step = argc > 3 ? (size_t)strtoul(argv[3], NULL, 10) : 64;
    if (!step || step % 64) return 2;
    for (size_t i = 0; i < full;) {
      size_t take = full - i < step ? full - i : step;
      fvdep_sha256_absorb_raw(st, b + i, take);
      i += take;
    }
    rc = fvdep_sha256_squeeze_raw(st, b + full, n - full, n, out + 8);
  } else if (!strcmp(argv[1], "monte")) {
    if (n != 32) return 2;
    uint8_t x[32], y[32], z[32], msg[96];
    memcpy(x, b, 32); memcpy(y, b, 32); memcpy(z, b, 32);
    rc = 0;
    for (size_t j = 0; j < 1000; ++j) {
      memcpy(msg, x, 32); memcpy(msg + 32, y, 32); memcpy(msg + 64, z, 32);
      if (fvdep_sha256_raw(out + 8, msg, 96)) { rc = 1; break; }
      memcpy(x, y, 32); memcpy(y, z, 32); memcpy(z, out + 8, 32);
    }
  } else return 2;
  int unchanged = !memcmp(b, copy, n);
  if (rc) printf("refused:%s", memcmp(out, pristine, sizeof out) ? "changed" : "untouched");
  else { printf("ok:"); hex(out + 8, 32); }
  int guard = !memcmp(out, pristine, 8) && !memcmp(out + 40, pristine + 40, 8);
  printf(":input=%d:guard=%d\n", unchanged, guard);
  free(copy); free(b);
  return 0;
}
