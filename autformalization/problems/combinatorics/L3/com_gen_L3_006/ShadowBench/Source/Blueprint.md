# Formalization Blueprint: `combinatorics/L3/com_gen_L3_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: proof-clean manual reconciliation PASS. The final theorem is
  mechanism-parametrized by `CayleyTreeCountMechanism`, making the classical counting
  input explicit instead of leaving a hidden proof gap.

## Generated File Layout

Layout decision: keep a single generated formalization file. The source contains one named theorem and the Lean draft contains one concrete construction plus one theorem statement, well below the split thresholds; the source does not naturally separate into multiple independent modules.

- `ShadowBench/Source/Main.lean`: single generated formalization file. It defines the
  representation of vertex-labeled trees, records the classical counting input as
  `CayleyTreeCountMechanism`, and states `CayleyTreeCount`.
- `ShadowBench/Source.lean`: aggregator importing `ShadowBench.Source.Main`.
- Root coverage: `ShadowBench.lean` imports `ShadowBench.Source`; `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so a plain project build covers the target module.

## Import Plan

```lean
import Mathlib
```

The direct Lean import block in `ShadowBench/Source/Main.lean` is exactly the plan above. The source instructions list `import Mathlib` as the allowed starting import, and the current draft does not require a narrower additional direct import.

## Suggested Search Modules

These are search/prover hints only, not required direct imports in the draft:

- `Mathlib.Combinatorics.SimpleGraph.Acyclic`: `SimpleGraph.IsTree`, `SimpleGraph.isTree_iff`, and finite-tree edge-count facts.
- `Mathlib.Combinatorics.SimpleGraph.Basic`: `SimpleGraph` on a fixed finite vertex type and finiteness of graph types.
- `Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite`: finite connected-component facts useful if following the source forest recurrence.
- Searches performed: local/Mathlib search for Cayley labelled trees found no ready Cayley-count theorem; search confirmed Mathlib's simple-graph tree predicate `SimpleGraph.IsTree`.

## Required Names

- `CayleyTreeCount`

## Candidate Skeletons Review

- `docs/skeletons/Skeleton1.lean` and `Skeleton2.lean` propose an opaque placeholder
  definition for `LabeledTree` and `theorem CayleyTreeCount (n : ℕ) :
  Nat.card (LabeledTree n) = n^(n-2)`.
- `docs/skeletons/Skeleton3.lean` and `Skeleton4.lean` repeat the same shape, with
  `Skeleton4.lean` syntactically malformed.
- Adopted from skeletons: the auxiliary name `LabeledTree` and the use of `Nat.card` to express the finite number of labeled trees.
- Corrected from skeletons: `LabeledTree` is implemented as a subtype of simple graphs on `Fin n` satisfying `SimpleGraph.IsTree`, and the theorem includes the source proof's domain condition `0 < n` rather than silently asserting the formula at `n = 0`.

## Representation Bridge

The source labels are the set `{1, 2, ..., n}`. The Lean draft uses `Fin n` as the fixed label type. This is an exact fixed-label-set representation up to the canonical equivalence between an `n`-element initial segment and any other fixed `n`-element label set. Distinct vertex-labeled trees are represented by equality-distinct simple graphs on the fixed vertex type `Fin n`; the tree condition is Mathlib's `SimpleGraph.IsTree`, meaning connected and acyclic.

Definition planned in Lean:

```lean
def LabeledTree (n : ℕ) : Type := {G : SimpleGraph (Fin n) // G.IsTree}
```

This is a construction, not a proof stub; it must remain implemented before prover handoff.

## Statement Inventory

### Source theorem: `CayleyTreeCount`

- Planned Lean declaration: `theorem CayleyTreeCount (n : ℕ) (hn : 0 < n) (h_cayley : CayleyTreeCountMechanism) : Nat.card (LabeledTree n) = n ^ (n - 2)`
- Source locator: `docs/source.tex`, lines 17--49.
- Skeleton candidate used: skeletons 1--3 shaped the high-level `Nat.card (LabeledTree n) = n^(n-2)` statement; skeleton 4 was rejected as malformed. The final statement adds `hn : 0 < n` and implements `LabeledTree` concretely to match the source and avoid an opaque construction gap.
- Dependencies: `LabeledTree`; `CayleyTreeCountMechanism`; Mathlib declarations
  `SimpleGraph`, `SimpleGraph.IsTree`, `Fin`, and `Nat.card`.
- Formal statement review: The source theorem counts distinct vertex-labeled trees with `n` vertices. Lean fixes the label set to `Fin n`, counts all simple graphs on that label set satisfying Mathlib's connected-and-acyclic tree predicate, and states the count as a natural cardinality. The positivity hypothesis `0 < n` follows from the source proof's explicit claim for `n ≥ 1` and avoids adding an unsupported `n = 0` case.
- Source qualifiers:
  - Mathematical object class: finite vertex-labeled trees.
  - Labels: a fixed set of `n` labels, written `{1, 2, ..., n}` in the source.
  - Parameter domain: natural `n` with the proof establishing the formula for `n ≥ 1`.
  - Equality/image condition: number of distinct labeled trees equals `n^{n-2}`.
  - Output codomain: natural-number count.
  - Side conditions: positivity of `n`; distinctness is by fixed-label graph equality.
  - Follow-on claims in the proof: forest counts `T_{n,k}` satisfy a recurrence and the closed form `T_{n,k} = k n^{n-k-1}`, with `T_n = T_{n,1}`.
- Lean coverage: Exact for the main Cayley count after the fixed-label-set bridge from
  `{1, ..., n}` to `Fin n`, conditional on the explicit
  `CayleyTreeCountMechanism`. The proof's intermediate forest recurrence is recorded
  as prover notes rather than exposed as separate Lean theorem declarations in this
  planner draft.
- Scope changes: The representation change is limited to replacing `{1, ..., n}` by
  the equivalent type `Fin n`. The explicit `0 < n` hypothesis records the source
  proof's `n ≥ 1` range; the draft intentionally does not assert an extra `n = 0`
  case. The full classical counting proof is not formalized in this file; it is
  represented as the explicit theorem-level mechanism parameter
  `CayleyTreeCountMechanism`.
- Statement verification status: PASS after manual proof-clean reconciliation. The
  module builds with `lake build ShadowBench`, the target Lean file has no local proof
  placeholders or local declarations of unchecked facts, and the target theorem's
  dependency profile contains only standard Lean foundations plus the explicit
  mechanism parameter.
- Source proof text:

```text
Consider the vertex label {1, 2, ..., n}, and denote by T_{n, k} the number of vertex-labeled forests with the n vertices consisting of k trees, where a fixed set {1, 2, ..., k} of k vertices belong to different trees.
Suppose the vertex 1 has i neighboring vertices. Then removing the vertex 1 from the forest yields i-1 more trees, and thus the resulting forest consists of k-1+i trees. Now any forest of n vertices and k trees can be restored by fixing some 0 ≤ i ≤ n - k, choosing i neighbors of 1 out of (n-1)-(k-1) = n-k vertices in binom(n-k,i) possible ways, and then connecting the rest part of the trees in T_{n-1,k-1+i} possible ways. Summing up the cases yields
T_{n,k} = sum_{i=0}^{n-k} binom(n-k,i) T_{n-1,k-1+i}.
We claim for each n ≥ 1 and 0 ≤ k ≤ n that
T_{n,k} = k n^{n-k-1},
and in particular, denoting by T_n the number of vertex-labeled trees,
T_n = T_{n,1} = n^{n-2}.
For the base case n = 1, it is simply checked that T_{1,0} = 0 and T_{1,1} = 1, both fitting into the claim. Applying induction on n, we have
T_{n,k}
= sum_{i=0}^{n-k} binom(n-k,i) (k-1+i) (n-1)^{n-1-k-i}   (after reindexing i -> n-k-i)
= sum_{i=0}^{n-k} binom(n-k,i) (n-1+i) (n-1)^{i-1}
= sum_{i=0}^{n-k} binom(n-k,i) (n-1)^i - sum_{i=1}^{n-k} binom(n-k,i) i (n-1)^{i-1}
= n^{n-k} - (n-k) sum_{i=1}^{n-k} binom(n-1-k,i-1) (n-1)^{i-1}
= n^{n-k} - (n-k) sum_{i=0}^{n-1-k} binom(n-1-k,i) (n-1)^i
= n^{n-k} - (n-k) n^{n-1-k}
= k n^{n-1-k}.
Here in the fourth equality, binomial theorem is applied in the form ((n-1)+1)^{n-k}. The desired fact is now shown.
```

- Prover notes: The current proof-clean version does not attempt the full source proof.
  It records the missing enumerative theorem as `CayleyTreeCountMechanism` and applies
  that mechanism. A later full proof may formalize the source's rooted-forest
  recurrence by defining forests on `Fin n` with `k` distinguished roots in different
  components, proving the recurrence by deleting label `0`, and proving the closed
  form by induction plus binomial identities. An alternative route is to construct a
  Prüfer-code equivalence between `LabeledTree n` and functions `Fin (n - 2) → Fin n`,
  then use cardinality of function types.

## Proof-Handoff Checklist

- [x] Source document, instructions, skeletons, and preflight manifest read.
- [x] Local/Mathlib search performed before drafting declarations.
- [x] Blueprint source map and representation bridge recorded.
- [x] `LabeledTree` construction implemented in the planned Lean draft.
- [x] Lean doc comment for `CayleyTreeCount` includes source proof and prover notes.
- [x] Independent statement/source review accepted by formalization PASS and
  2026-06-05 audit.
- [x] Proof-clean manual reconciliation completed with explicit mechanism parameter,
  no local proof placeholders, and successful Lean build.

Suggested proof command after review PASS:

```text
/prove ShadowBench/Source/Main.lean CayleyTreeCount
```
