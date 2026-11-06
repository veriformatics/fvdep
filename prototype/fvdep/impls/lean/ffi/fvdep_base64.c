/* Plain C API over the proven Lean exports (Base64Ffi). Trusted glue: no proof covers this file.
 * Strings are NUL-terminated UTF-8 ⇒ text containing NUL cannot cross this API. */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

void lean_initialize_runtime_module(void); /* declared by Lean-generated C, not lean.h */
lean_object *initialize_base64acc_Base64Ffi(uint8_t builtin);
lean_object *fvdep_base64_encode(lean_object *bytes);
lean_object *fvdep_base64_decode(lean_object *text);

static int ready = 0;

/* 0 = ok. Call once, from the thread that calls the other functions. */
int fvdep_init(void) {
  if (ready) return 0;
  lean_initialize_runtime_module();
  lean_object *r = initialize_base64acc_Base64Ffi(1);
  int failed = lean_io_result_is_error(r);
  lean_dec_ref(r);
  if (failed) return 1;
  lean_io_mark_end_initialization();
  ready = 1;
  return 0;
}

/* base64 text of `n` bytes; caller frees with fvdep_free. */
char *fvdep_b64_encode(const uint8_t *in, size_t n) {
  lean_object *ba = lean_alloc_sarray(1, n, n);
  memcpy(lean_sarray_cptr(ba), in, n);
  lean_object *s = fvdep_base64_encode(ba); /* consumes ba */
  char *out = strdup(lean_string_cstr(s));
  lean_dec_ref(s);
  return out;
}

/* 0 = decoded into *out (*n bytes, caller frees with fvdep_free); 1 = rejected by the spec. */
int fvdep_b64_decode(const char *in, uint8_t **out, size_t *n) {
  lean_object *r = fvdep_base64_decode(lean_mk_string(in)); /* consumes the string */
  if (lean_is_scalar(r)) { *out = NULL; *n = 0; return 1; } /* Option.none */
  lean_object *ba = lean_ctor_get(r, 0);
  size_t m = lean_sarray_size(ba);
  *out = malloc(m ? m : 1);
  memcpy(*out, lean_sarray_cptr(ba), m);
  *n = m;
  lean_dec_ref(r);
  return 0;
}

void fvdep_free(void *p) { free(p); }
