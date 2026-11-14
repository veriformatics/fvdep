import Lake

open Lake DSL

package «fvdep-codec-tests» where leanOptions := #[⟨`autoImplicit, false⟩]

require fvdeptool from "../../tool"

lean_lib CodecHarness

@[default_target] lean_exe «codec-driver» where root := `Driver

lean_exe «codec-driver-small» where
  root := `SmallDriver
  moreLinkArgs :=
  #[(__dir__ / ".." / "sha256" / ".build" / "libsha-small.a").toString,
    "-Wl,--wrap=fvdep_sha256_init_raw", "-Wl,--wrap=fvdep_sha256_absorb_raw",
    "-Wl,--wrap=fvdep_sha256_squeeze_raw", "-Wl,--wrap=fvdep_sha256_raw"]
