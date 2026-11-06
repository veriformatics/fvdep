# Deferred

- fva + fvtrace dependencies → fvdep specs (user: "eventually"). Accept: `fvdep scan` over each repo's manifests lists ≥1 dependency with a spec, + a documented path for each repo to adopt fvdep checks in its own gate.
- semver open obligations `semver.compare.compare_trans`, `semver.parse.parse_render` (`sorry`). Accept: `prototype/fvdep/fvdep list` shows 0 open for `semver.parse` + `semver.compare`.
