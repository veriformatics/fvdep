/-! Library snapshots' limits (contract `docs/contracts/U5b-oracle.md` L2–L4, T): a leaf module, so
the effect vocabulary (`FvdepCore.Plan`) names the `snapshot` effect's limits. -/

namespace FvdepCore.Library

/-- L4's caps (T): entries, path bytes, depth, cumulative path bytes, file + total blob bytes. -/
structure Caps where
  entries : Nat := 10000
  pathBytes : Nat := 4096
  depth : Nat := 32
  pathTotal : Nat := 4194304
  fileBytes : Nat := 1048576
  totalBytes : Nat := 67108864
  deriving DecidableEq, Repr

/-- T's library limits (L2–L4): seconds one git process may run, seconds to wait for the store
lock, bytes kept per git diagnostic stream, the tree caps (`treeEntries` = `caps.entries`,
`snapshotBytes` = `caps.totalBytes`). -/
structure Limits where
  fetchSeconds : Nat := 300
  lockSeconds : Nat := 60
  gitBytes : Nat := 65536
  caps : Caps := {}
  deriving DecidableEq, Repr

/-- One `--limit <name>=<n>` of the dev seam (Q3): `none` = no library limit of that name. -/
def Limits.set (l : Limits) (name : String) (n : Nat) : Option Limits :=
  match name with
  | "fetchSeconds" => some { l with fetchSeconds := n }
  | "lockSeconds" => some { l with lockSeconds := n }
  | "gitBytes" => some { l with gitBytes := n }
  | "treeEntries" => some { l with caps := { l.caps with entries := n } }
  | "snapshotBytes" => some { l with caps := { l.caps with totalBytes := n } }
  | _ => none

end FvdepCore.Library
