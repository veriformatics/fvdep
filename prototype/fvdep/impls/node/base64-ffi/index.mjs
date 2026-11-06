// Node binding of the proven Lean base64 (Base64Ffi: proven equal to base64.encode@1.0.0 /
// base64.decode@1.0.0) through koffi. Trusted: Lean compiler + runtime, the C shim, koffi, this file.
import koffi from "koffi";
import { fileURLToPath } from "node:url";

const path = process.env.FVDEP_BASE64_LIB ??
  fileURLToPath(new URL("../../lean/.lake/build/ffi/libfvdep_base64.so", import.meta.url));
const lib = koffi.load(path);
const init = lib.func("int fvdep_init(void)");
const enc = lib.func("void *fvdep_b64_encode(const uint8_t *in, size_t n)");
const dec = lib.func("int fvdep_b64_decode(const char *in, _Out_ uint8_t **out, _Out_ size_t *n)");
const free = lib.func("void fvdep_free(void *p)");
if (init() !== 0) throw new Error("Lean runtime initialization failed");

export function encode(bytes) {
  const p = enc(bytes, bytes.length);
  try { return koffi.decode(p, "char", -1); } finally { free(p); }
}

/** `null` = rejected by the spec (also text containing NUL, which the C API cannot carry). */
export function decode(text) {
  if (text.includes("\0")) return null;
  const out = [null], n = [0];
  if (dec(text, out, n) !== 0) return null;
  try { return Buffer.from(koffi.decode(out[0], "uint8_t", n[0])); } finally { free(out[0]); }
}
