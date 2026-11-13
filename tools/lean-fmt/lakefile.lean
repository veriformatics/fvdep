import Lake
open Lake DSL

/-- Dev-only package pinning the Lean formatter + linter the gate runs (stage `lean-style`):
nothing in fvdep imports it and the shipped packages never require it. -/
package «fvdep-lean-fmt»

require «lean-fmt» from git "https://github.com/jcreinhold/lean-fmt" @ "v4.35.0"
