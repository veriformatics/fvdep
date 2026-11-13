# Deferred

- fva + fvtrace dependencies → fvdep specs (user: "eventually"). Accept: `fvdep scan` over each repo's manifests lists ≥1 dependency with a spec, + a documented path for each repo to adopt fvdep checks in its own gate.
- Commercial requests (user ruling, orientation: not in this phase). Accept: `fvdep request <pkg> [--lang L]` files a request (GitHub issue from a template) naming package, operations + language; automated customer work runs on an API integration the provider's commercial terms permit, never the subscription; a planted request round-trips into the issue tracker.
- Paid update alerts + signed releases (user ruling, orientation: deferred). Accept: a subscriber registers pins and receives an alert (email or webhook) for a new version, proven compatibility or retraction touching them; release tags + index are signed and `fvdep outdated` verifies the signature against a pinned key, a tampered index fails.
