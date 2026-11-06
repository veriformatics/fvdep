//! Safe Rust API over the proven Lean base64 (`Base64Ffi`: proven equal to base64.encode@1.0.0 /
//! base64.decode@1.0.0). Trusted: Lean compiler + runtime, the C shim, this file.
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::sync::Once;

extern "C" {
    fn fvdep_init() -> c_int;
    fn fvdep_b64_encode(input: *const u8, n: usize) -> *mut c_char;
    fn fvdep_b64_decode(input: *const c_char, out: *mut *mut u8, n: *mut usize) -> c_int;
    fn fvdep_free(p: *mut c_void);
}

static INIT: Once = Once::new();

fn init() {
    // SAFETY: called once; the Lean runtime then serves this thread (the adapter is single-threaded).
    INIT.call_once(|| assert_eq!(unsafe { fvdep_init() }, 0, "Lean runtime initialization failed"));
}

pub fn encode(bytes: &[u8]) -> String {
    init();
    // SAFETY: the shim returns a malloc'd NUL-terminated string, freed here.
    unsafe {
        let p = fvdep_b64_encode(bytes.as_ptr(), bytes.len());
        let s = CStr::from_ptr(p).to_string_lossy().into_owned();
        fvdep_free(p.cast());
        s
    }
}

/// `None` = rejected by the spec (also text containing NUL, which the C API cannot carry).
pub fn decode(text: &str) -> Option<Vec<u8>> {
    init();
    let c = CString::new(text).ok()?;
    let (mut out, mut n) = (std::ptr::null_mut(), 0usize);
    // SAFETY: on 0 the shim hands over a malloc'd buffer of n bytes, copied then freed here.
    unsafe {
        if fvdep_b64_decode(c.as_ptr(), &mut out, &mut n) != 0 {
            return None;
        }
        let v = std::slice::from_raw_parts(out, n).to_vec();
        fvdep_free(out.cast());
        Some(v)
    }
}
