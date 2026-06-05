# Formalization Blueprint: `combinatorics/L3/com_gen_L3_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed edge-count bridge, the extremality definition, the named lemma `IsExtremal.prop`, and the theorem `exists_isExtremal_iff_exists`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No split into additional Lean files is planned for this short source document.

## Import Plan

```lean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
```

Import justification: the first two imports are the allowed starting imports from `docs/instructions.md`; `Mathlib.Combinatorics.SimpleGraph.Finite` is added because Lean verification showed that the edge-count formalization needs `SimpleGraph.edgeFinset` and related finite-edge-set declarations.

## Suggested Search Modules

These are search hints for the later prover pass, not direct imports required by the current draft:

- `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic`: Mathlib's namespace-qualified `SimpleGraph.IsExtremal` and `SimpleGraph.exists_isExtremal_iff_exists` may be useful proof references, but the source-required declarations here have the unqualified names from `docs/instructions.md`.

## Required Names

- `IsExtremal.prop`
- `exists_isExtremal_iff_exists`

## Source Statement Inventory

### line-17

- Source inventory id: `line-17`.
- Source locator: `docs/source.tex`, lines 17-26.
- Source statement: Let `V` be a finite vertex set, and let `p` be a property of simple graphs on `V`. A simple graph `G` on `V` is called extremal with respect to `p` if `p(G)` and, for every simple graph `G'` on `V` with `p(G')`, `|E(G')| ≤ |E(G)|`.
- Planned Lean declarations: `simpleGraphEdgeCount`, `IsExtremal`, `IsExtremal.prop`.
- Lean statement shape: `simpleGraphEdgeCount` returns the finite edge count of a graph; `IsExtremal p G` is `p G ∧ ∀ G', p G' → simpleGraphEdgeCount G' ≤ simpleGraphEdgeCount G`; `IsExtremal.prop` states the biconditional between `IsExtremal p G` and that conjunction.
- Skeleton candidate used: adapted from `docs/skeletons/Skeleton1.lean`. Skeleton1 gives the faithful `IsExtremal` definition and main theorem shape, but uses a non-existent `G.edges.card` projection and lacks the required named lemma `IsExtremal.prop`; the draft corrects the edge-count representation and adds that lemma. Skeletons 2 and 3 use a trivial `IsExtremal.prop : True`, and Skeleton4 conflates `IsExtremal.prop` with the existence theorem, so those parts were not adopted.
- Dependencies: Lean `SimpleGraph V`; `[Fintype V]` to express finite vertex set; the implemented `simpleGraphEdgeCount` bridge using `G.edgeFinset.card`; no proof dependencies beyond unfolding `IsExtremal` for the later prover.
- Formal statement review: The Lean definition records the source phrase “is called extremal” as a proposition on a graph `G`. The named lemma states that this proposition is equivalent to the exact conjunction displayed in the source, with `simpleGraphEdgeCount` representing `|E(-)|`.
- Source qualifiers:
  - Mathematical object class: simple graphs on a fixed finite vertex set.
  - Quantifier order: `V`, finite instance, property `p`, graph `G`, then every comparison graph `G'`.
  - Parameter domain: `p : SimpleGraph V → Prop`, `G G' : SimpleGraph V`.
  - Output codomain: proposition.
  - Equality/image condition: none.
  - Side conditions: `p G`; for all `G'`, if `p G'` then edge count of `G'` is at most edge count of `G`.
  - Follow-on claims: none.
- Lean coverage: `V : Type*` with `[Fintype V]` covers the finite vertex set; `SimpleGraph V` covers “simple graph on V”; `p : SimpleGraph V → Prop` covers the graph property; `∀ G' : SimpleGraph V, p G' → simpleGraphEdgeCount G' ≤ simpleGraphEdgeCount G` covers the maximal edge-count condition; `simpleGraphEdgeCount` covers `|E(-)|` via `G.edgeFinset.card` under classical decidability.
- Scope changes: none. The Lean representation uses Mathlib simple graphs and an explicit edge-count bridge; this is a direct encoding of the source object class and edge cardinality.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: This source block is definitional. For the later proof, unfold `IsExtremal` and prove the biconditional by reflexive simplification or constructor/simp.

### line-28

- Source inventory id: `line-28`.
- Source locator: `docs/source.tex`, lines 28-36; proof at lines 38-48.
- Source statement: Let `V` be a finite vertex set, and let `p` be a property of simple graphs on `V`. Then `∃ G` on `V` such that `p(G)` if and only if `∃ G` on `V` that is extremal with respect to `p`.
- Planned Lean declarations: `exists_isExtremal_iff_exists`.
- Lean statement shape: `(∃ G : SimpleGraph V, p G) ↔ (∃ G : SimpleGraph V, IsExtremal p G)`.
- Skeleton candidate used: adapted from `docs/skeletons/Skeleton1.lean`, whose theorem order matches the displayed source equivalence. The added `IsExtremal.prop` lemma supplies the required source-named definition bridge.
- Dependencies: `simpleGraphEdgeCount`; `IsExtremal`; `IsExtremal.prop`; finiteness of the type of simple graphs on a finite vertex type for the maximum-edge argument. Search found Mathlib references `SimpleGraph.IsExtremal` and `SimpleGraph.exists_isExtremal_iff_exists` in `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic`, which may guide the later proof.
- Formal statement review: The Lean theorem preserves the displayed order of the source equivalence: existence of a graph satisfying `p` on the left, existence of an extremal graph on the right.
- Source qualifiers:
  - Mathematical object class: simple graphs on a fixed finite vertex set.
  - Quantifier order: choose finite vertex type `V`, property `p`, then compare the two existential propositions over graphs on `V`.
  - Parameter domain: `p : SimpleGraph V → Prop`.
  - Output codomain: proposition-valued equivalence.
  - Equality/image condition: equivalence between the two existence statements.
  - Side conditions: finite vertex set only.
  - Follow-on claims: existence of an extremal witness whenever any graph satisfying `p` exists.
- Lean coverage: `[Fintype V]` covers finite `V`; both existential quantifiers range over `SimpleGraph V`; the right side uses the definition bridge `IsExtremal p G` from `line-17`, whose edge condition is measured by `simpleGraphEdgeCount`.
- Scope changes: none. Note only that the source prose names the implication directions opposite to the displayed formula: the immediate direction is right-to-left for the displayed Lean statement, and the maximum-edge construction proves left-to-right.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: “The forward implication is immediate, since any extremal graph satisfies `p` by definition. For the reverse implication, assume there exists at least one simple graph on `V` satisfying `p`. Because the set of simple graphs on a fixed finite vertex set is finite, the number of edges attained among graphs satisfying `p` has a maximum. Choose a graph `G` satisfying `p` with the maximum possible number of edges. Then `G` satisfies `p`, and for any other graph `G'` on `V` with `p(G')`, we have `|E(G')| ≤ |E(G)|`. Thus `G` is extremal with respect to `p`.”
- Source proof / prover notes: For the displayed Lean equivalence, prove the right-to-left direction by extracting `p G` from `IsExtremal.prop`. For the left-to-right direction, use finiteness of `SimpleGraph V` to choose a witness satisfying `p` with maximal `simpleGraphEdgeCount G`; then package the witness and the universal maximality condition. The Mathlib theorem `SimpleGraph.exists_isExtremal_iff_exists` may be a reusable guide after reconciling namespace and equivalence order.

## Search Log

- Local/semantic search for `SimpleGraph edges card Finset edge set finite graph` found `SimpleGraph.edgeFinset`, `SimpleGraph.edgeFinset_card`, and related finite edge-set lemmas in `Mathlib.Combinatorics.SimpleGraph.Finite`.
- Search for `SimpleGraph.IsExtremal.prop` found Mathlib's namespace-qualified `SimpleGraph.IsExtremal`, `SimpleGraph.IsExtremal.prop`, and `SimpleGraph.exists_isExtremal_iff_exists` in `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic`.

## Statement/Source Review Gate

- [x] Source document and preflight manifest read.
- [x] Candidate skeletons compared against the source.
- [x] Planner blueprint entries for `line-17` and `line-28` drafted with source qualifiers, Lean coverage, scope changes, and prover notes.
- [x] Lean declaration skeletons drafted with source-aware doc comments.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
