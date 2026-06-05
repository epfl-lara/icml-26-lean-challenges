# Formalization Blueprint: `combinatorics/L3/com_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Document and Support Files Read

- `docs/source.tex` inspected with `formalization_document_inspect`; source labels are `line-17` and `line-27`.
- Preflight manifest read from `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Planner context read from `.epflemma/workflow-state/formalization/docs-source/context.md`.
- Required ShadowBench support files read: `docs/instructions.md`, `docs/skeletons/README.md`, and `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean`.
- The manifest listed no bibliography files, citations, local PDFs, or figures.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: source-backed declarations `IsBipartiteWith` and `isBipartiteWith_sum_degrees_eq_card_edges`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level `lake build` covers the target module.

## Import Plan

```lean
import Mathlib.Combinatorics.SimpleGraph.Bipartite
```

## Suggested Search Modules

- `Mathlib.Combinatorics.SimpleGraph.Bipartite`: contains `SimpleGraph.IsBipartiteWith` and `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges`.
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum`: dependency for degree-sum and `edgeFinset` facts.
- `Mathlib.Combinatorics.Enumerative.DoubleCounting`: dependency used by the Mathlib bipartite counting proof.

## Required Names

- `IsBipartiteWith`
- `isBipartiteWith_sum_degrees_eq_card_edges`

## Search and Skeleton Notes

- Mathlib search found `SimpleGraph.IsBipartiteWith`, whose fields are exactly the two source conditions: disjointness and every adjacent pair crosses between the sides.
- Mathlib search found `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges`, the standard bipartite degree-sum formula.
- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` proposed the required global names and source predicate shape. The final draft keeps the required global names, wraps Mathlib's predicate, and uses `G.edgeFinset.card` for `|E(G)|`.
- `Skeleton4.lean` has an extra malformed trailing proof marker, so only its intended statement shape was used as a hint.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, lines 17--25.
- Source kind/title: definition `[IsBipartiteWith]`.
- Source statement: Let `G` be a simple graph on a vertex set `V`, and let `s,t ⊆ V`. The graph is bipartite with respect to `s` and `t` when (1) `s` and `t` are disjoint and (2) every edge connects a vertex in `s` to a vertex in `t` in one direction or the other.
- Planned Lean declarations: `IsBipartiteWith`
- Lean statement:
  ```lean
  def IsBipartiteWith {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
    G.IsBipartiteWith s t
  ```
- Dependencies: `SimpleGraph`, `Set`, `Disjoint`, and Mathlib's `SimpleGraph.IsBipartiteWith` from `Mathlib.Combinatorics.SimpleGraph.Bipartite`.
- Formal statement review: The Lean declaration has the required source name and the same parameters `G`, `s`, and `t`. It is a transparent wrapper around Mathlib's exact predicate, whose fields give disjointness and the across-edge condition.
- Source qualifiers:
  - Mathematical object class: a simple graph `G` on a vertex set/type `V`.
  - Quantifier order / parameter domain: for arbitrary `V`, take `G : SimpleGraph V`, then subsets `s t : Set V`.
  - Output codomain: a proposition defining when `G` is bipartite with respect to `s` and `t`.
  - Equality/image condition: no numerical equality or image condition; the definition is exactly the conjunction of the side conditions below.
  - Side condition 1: `s` and `t` are disjoint.
  - Side condition 2: every edge/adjacency of `G` has one endpoint in `s` and the other in `t`, in either direction.
  - Follow-on claims: none; in particular, the source definition does not require `s ∪ t = V`, nonemptiness, or uniqueness of the two sides.
- Lean coverage: exact coverage through the global wrapper `IsBipartiteWith`, which transparently aliases `SimpleGraph.IsBipartiteWith`; Mathlib's predicate has fields `disjoint : Disjoint s t` and `mem_of_adj : G.Adj v w → (v ∈ s ∧ w ∈ t) ∨ (v ∈ t ∧ w ∈ s)`.
- Scope changes: none. The theorem phrase "bipartition of `G` in the above sense" is interpreted as this definition, with no added vertex-covering condition.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: This is a definition, so there is no source proof. During proof work, unfold `IsBipartiteWith` to use Mathlib's `G.IsBipartiteWith s t` structure.

### line-27

- Source locator: `docs/source.tex`, theorem lines 27--33 and proof lines 35--39.
- Source kind/title: theorem `[isBipartiteWith_sum_degrees_eq_card_edges]`.
- Source statement: Let `G` be a finite simple graph, and let `s,t ⊆ V` be a bipartition of `G` in the above sense. Then `∑_{v ∈ s} deg_G(v) = |E(G)|`.
- Complete source proof text: Each edge of a bipartite graph has exactly one endpoint in `s` and the other endpoint in `t`. When summing degrees over `s`, every edge is counted exactly once via its unique endpoint in `s`. Therefore the sum of degrees over `s` equals the total number of edges.
- Planned Lean declarations: `isBipartiteWith_sum_degrees_eq_card_edges`
- Lean statement:
  ```lean
  theorem isBipartiteWith_sum_degrees_eq_card_edges {V : Type*} [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Set V)
      [DecidablePred (fun v => v ∈ s)] (h : IsBipartiteWith G s t) :
      ∑ v ∈ s.toFinset, G.degree v = G.edgeFinset.card := by sorry
  ```
- Dependencies: `IsBipartiteWith`; `SimpleGraph.degree`; `SimpleGraph.edgeFinset`; `Set.toFinset`; `Finset.sum`; and the Mathlib theorem `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` for the future proof.
- Formal statement review: The Lean theorem keeps the required source name, the graph parameter, the two subset parameters, and the bipartite-with-respect-to hypothesis from `line-17`. The conclusion is the same degree sum equals edge-cardinality statement, with `s.toFinset` enumerating the source subset and `G.edgeFinset.card` representing `|E(G)|`.
- Source qualifiers:
  - Mathematical object class: a finite simple graph `G` on vertex set/type `V`.
  - Quantifier order / parameter domain: for arbitrary finite `V`, take `G : SimpleGraph V`, subsets `s t : Set V`, and the hypothesis that `s,t` form a bipartition of `G` in the sense of `line-17`.
  - Output codomain: an equality of natural numbers.
  - Equality condition: the sum over vertices `v ∈ s` of `deg_G(v)` equals the cardinality `|E(G)|` of the graph's edge set.
  - Side conditions: the bipartition hypothesis includes exactly the two source defining conditions, disjointness of `s,t` and every edge crossing between them in one direction or the other.
  - Follow-on claims: none beyond the displayed equality; the proof's "counted exactly once" sentence is proof explanation, not a separate claimed equivalence.
- Lean coverage: full coverage for the source theorem under the standard Lean finite-vertex representation. `[Fintype V]` represents the finite vertex set, `G : SimpleGraph V` represents the simple graph, `s t : Set V` are the two subsets, `h : IsBipartiteWith G s t` is the `line-17` bipartition predicate, `s.toFinset` enumerates the source subset for the finite sum, `G.degree v` is `deg_G(v)`, and `G.edgeFinset.card` represents `|E(G)|`. The explicit `[DecidableRel G.Adj]` and `[DecidablePred (fun v => v ∈ s)]` instances are Lean enumeration/degree API requirements.
- Scope changes: no mathematical weakening or strengthening. The Lean statement represents "finite simple graph" by a finite vertex type and exposes decidability instances needed by Lean; these are representation choices under classical finite graph reasoning. No covering condition `s ∪ t = V` is added because the source says "in the above sense" and the source definition does not include such a condition.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Unfold `IsBipartiteWith` to view `h` as `G.IsBipartiteWith s t`; convert the set-side finite enumerator `s.toFinset` to the finset formulation used by Mathlib; apply `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges`. The source counting argument is that every crossing edge contributes exactly once to the sum over `s`.

## Formal Statement Review Summary

- `line-17` is represented by a global source name wrapping Mathlib's exact bipartite-with-respect-to predicate.
- `line-27` preserves the finite graph, subset parameters, bipartite-with-respect-to hypothesis, degree sum over the left side, and edge-cardinality conclusion.
- The draft deliberately leaves the theorem proof as `by sorry` for a later `/prove` workflow, as required by the document-formalization contract.

## Verification Plan and Handoff

- Draft readiness checks: `lean_inspect ShadowBench/Source/Main.lean`, then project-level `lean_verify(mode=project)`.
- Independent statement/source review must approve or correct both source entries before proof handoff.
- Suggested next proof command after review approval: `/prove ShadowBench/Source/Main.lean isBipartiteWith_sum_degrees_eq_card_edges`.

## Proof-Ready Checklist

- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.
