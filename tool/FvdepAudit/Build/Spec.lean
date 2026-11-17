import FvdepAudit.Json.Spec
import FvdepCore.Build

/-! Specs for the build cache's pure parts (contract `docs/contracts/U5-sandbox.md` K1, K2, K5, K6),
written from the contract apart from `FvdepCore.Build`'s code: what a build graph's nodes import,
which modules a plan must reach, what a valid build order is, the eviction order + stopping rule,
an entry's validity. -/

namespace FvdepAudit.Build.Spec

open FvdepCore.Build

/-- `m` imports `i` in the graph: some node named `m` lists `i`. -/
def Imports (nodes : List Node) (m i : String) : Prop := ∃ n ∈ nodes, n.name = m ∧ i ∈ n.imports

/-- K2: the modules a plan must reach: the roots + every import of a reached module. -/
inductive Reach (nodes : List Node) (roots : List String) : String → Prop where
  | root {m : String} : m ∈ roots → Reach nodes roots m
  | step {a i : String} : Reach nodes roots a → Imports nodes a i → Reach nodes roots i

/-- `i` stands before `m` in `order`. -/
def Before (order : List String) (i m : String) : Prop :=
  ∃ k l : Nat, order[k]? = some i ∧ order[l]? = some m ∧ k < l

/-- K2: a build order: every reached module exactly once, each a node, each after all its imports.
-/
def ValidOrder (nodes : List Node) (roots order : List String) : Prop :=
  order.Nodup ∧
    (∀ m, m ∈ order ↔ Reach nodes roots m) ∧
    (∀ m ∈ order, m ∈ nodes.map (·.name)) ∧ ∀ m ∈ order, ∀ i, Imports nodes m i → Before order i m

/-- A string within the JSON profile's string bound (U3 J1: 65,536 bytes). -/
def Fits (s : String) : Prop := s.utf8ByteSize ≤ FvdepAudit.Json.Spec.maxStringBytes

/-- K1's domain: every string a key input holds fits the profile's bound + its thread count fits a
profile integer (the canonical JSON printer's laws hold there). -/
def Bounded (k : KeyInput) : Prop :=
  (∀ s ∈ [k.recipe.id, k.recipe.release, k.recipe.fingerprint, k.module, k.path, k.source],
      Fits s) ∧
    (∀ s ∈ k.recipe.argv, Fits s) ∧
    (∀ s ∈ k.recipe.leanPath, Fits s) ∧
    (∀ s ∈ k.recipe.options, Fits s) ∧
    (∀ e ∈ k.recipe.env, Fits e.1 ∧ Fits e.2) ∧
    (∀ i ∈ k.imports, Fits i.module ∧ Fits i.key) ∧ k.recipe.threads ≤ FvdepAudit.Json.Spec.maxInt

/-- K5's order: the least recently used first, ties by key. -/
def LruBefore (a b : Entry) : Prop := a.used < b.used ∨ (a.used = b.used ∧ a.key ≤ b.key)

/-- The charged bytes of `es`. -/
def charged (es : List Entry) : Nat := (es.map (·.bytes)).sum

/-- K6: an entry is valid when its manifest is schema 1, its key inputs hash to its directory's
name, no artifact takes a metadata file's name, both metadata files are present, every listed
artifact is present with its size + digest, + every file present is an artifact or one of the two
metadata files. -/
def EntryValid (h : ByteArray → String) (dir : String) (m : Manifest) (files : List FileRec) :
    Prop :=
  m.schema = 1 ∧
    h (preimage m.input) = dir ∧
    (∀ a ∈ m.artifacts, a.path ≠ "manifest.json" ∧ a.path ≠ "used") ∧
    (∃ f ∈ files, f.path = "manifest.json") ∧
    (∃ f ∈ files, f.path = "used") ∧
    (∀ a ∈ m.artifacts, a ∈ files) ∧
    ∀ f ∈ files, f.path = "manifest.json" ∨ f.path = "used" ∨ ∃ a ∈ m.artifacts, a.path = f.path

end FvdepAudit.Build.Spec
