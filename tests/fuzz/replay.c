/* Engine-free replay (gate stage `fuzz-replay`): every file argument through the target's
 * LLVMFuzzerTestOneInput, its name printed first, so an abort names the input that caused it. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int LLVMFuzzerInitialize(int *argc, char ***argv);
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int main(int argc, char **argv) {
    LLVMFuzzerInitialize(&argc, &argv);
    for (int i = 1; i < argc; i++) {
        FILE *f = fopen(argv[i], "rb");
        if (f == NULL) {
            perror(argv[i]);
            return 2;
        }
        size_t cap = 4096, n = 0;
        uint8_t *buf = malloc(cap);
        size_t got;
        while (buf != NULL && (got = fread(buf + n, 1, cap - n, f)) > 0) {
            n += got;
            if (n == cap) buf = realloc(buf, cap *= 2);
        }
        if (buf == NULL || ferror(f)) {
            fprintf(stderr, "%s: read failed\n", argv[i]);
            return 2;
        }
        fclose(f);
        fprintf(stderr, "replay %s (%zu bytes)\n", argv[i], n);
        LLVMFuzzerTestOneInput(buf, n);
        free(buf);
    }
    printf("replayed %d inputs\n", argc - 1);
    return 0;
}
