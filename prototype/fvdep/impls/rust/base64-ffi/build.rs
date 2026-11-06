// Links libfvdep_base64.so built by impls/lean/ffi/build.sh; rpath ⇒ runs without LD_LIBRARY_PATH.
fn main() {
    let dir = std::env::var("FVDEP_BASE64_LIB_DIR").unwrap_or_else(|_| {
        let here = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
        here.join("../../lean/.lake/build/ffi").canonicalize().expect("build impls/lean/ffi first").display().to_string()
    });
    println!("cargo:rustc-link-search=native={dir}");
    println!("cargo:rustc-link-lib=dylib=fvdep_base64");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{dir}");
    println!("cargo:rerun-if-env-changed=FVDEP_BASE64_LIB_DIR");
}
