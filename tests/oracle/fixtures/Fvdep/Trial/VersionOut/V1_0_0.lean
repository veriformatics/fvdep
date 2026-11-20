import Fvdep.Semver.Version.V1_0_0

namespace Fvdep.Trial.VersionOut.V1_0_0

open Fvdep.Semver.Version.V1_0_0 (Version)

def reverseMarks (v : Version) : Version :=
  { v with pre := v.pre.reverse, build := v.build.reverse }

end Fvdep.Trial.VersionOut.V1_0_0
