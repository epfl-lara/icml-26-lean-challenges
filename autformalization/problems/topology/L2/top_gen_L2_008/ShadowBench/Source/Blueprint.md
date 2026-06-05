# Formalization Blueprint: `topology/L2/top_gen_L2_008`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed declaration `paths_homotopic` and theorem skeleton `simply_connected_iff_paths_homotopic`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target is covered by the project root target.

## Import Plan

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.CategoryTheory.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
```

## Suggested Search Modules

- `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`: Mathlib contains the same conceptual definition as `SimplyConnectedSpace` and a theorem named `simply_connected_iff_paths_homotopic`; this module is a proof-reference/search hint, not a direct import for `Main.lean`, because it would introduce a global declaration name that collides with the required source theorem name.
- `Mathlib.Topology.Homotopy.Path`: definitions around `Path.Homotopic` and `Path.Homotopic.Quotient`.
- `Mathlib.Topology.Connected.PathConnected`: `PathConnectedSpace` and path-connected API.

## Required Names

- `paths_homotopic`
- `simply_connected_iff_paths_homotopic`

## Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` suggest `Nonempty (FundamentalGroupoid X ≃ PUnit)` and morphisms `x ⟶ y`; this does not faithfully represent categorical equivalence of groupoids and does not directly express paths modulo homotopy.
- `docs/skeletons/Skeleton4.lean` gives the useful categorical-equivalence shape `FundamentalGroupoid X ≌ CategoryTheory.Discrete PUnit` and a direct homotopy statement. The final draft adapts this by using Mathlib's one-object discrete category representation `Discrete Unit`, and by representing “at most one path up to homotopy” as `Subsingleton (Path.Homotopic.Quotient x y)`.
- Mathlib search found `SimplyConnectedSpace` and `simply_connected_iff_paths_homotopic` in `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`; the final source declarations mirror their mathematical content while preserving the required ShadowBench declaration names.

## Detected Theorem-Like Blocks

1. `line-17` (definition, lines 17-19) - paths_homotopic
2. `line-21` (theorem, lines 21-23; proof lines 24-26) - simply_connected_iff_paths_homotopic

## Source Map

- line-17 -> `paths_homotopic` (`docs/source.tex` lines 17-19)
- line-21 -> `simply_connected_iff_paths_homotopic` (`docs/source.tex` lines 21-23; proof lines 24-26)

## Source inventory

- label: line-17
  source_id: line-17
  kind: definition
  source_title: paths_homotopic
  planned_lean_declaration: paths_homotopic
  source_locator: docs/source.tex lines 17-19
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.
- label: line-21
  source_id: line-21
  kind: theorem
  source_title: simply_connected_iff_paths_homotopic
  planned_lean_declaration: simply_connected_iff_paths_homotopic
  source_locator: docs/source.tex lines 21-23, proof lines 24-26
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.

## Source Statement Inventory

### line-17

- Source inventory entry `line-17`: definition `[paths_homotopic]` in `docs/source.tex`.
- Source label: `line-17`
- Source inventory entry: `line-17`
- Source inventory label: `line-17`
- Source block label: `line-17`
- Preflight label: `line-17`
- Planned Lean declarations: `paths_homotopic`.
- Adopted Lean statement:
  ```lean
  def paths_homotopic (X : Type*) [TopologicalSpace X] : Prop :=
    Nonempty (FundamentalGroupoid X ≌ Discrete Unit)
  ```
- Source locator: `docs/source.tex`, lines 17-19.
- Source statement: “A topological space $X$ is simply connected if its fundamental groupoid is equivalent to the the groupoid with one object and the identity morphism.”
- Skeleton candidate used: based mainly on `Skeleton4.lean`; adjusted from `Discrete PUnit` to Mathlib's `Discrete Unit` convention for the singleton discrete category.
- Dependencies: `FundamentalGroupoid`, categorical equivalence notation `≌`, and `CategoryTheory.Discrete Unit` from the direct imports above.
- Formal statement review: The Lean definition is a proposition on a type with a `TopologicalSpace` instance. It defines the source's simply-connected condition as nonempty categorical equivalence between the fundamental groupoid of `X` and the discrete one-object category.
- Source qualifiers:
  - Mathematical object class: topological spaces.
  - Quantifier order / parameter domain: a space `X : Type*` with `[TopologicalSpace X]`.
  - Output codomain: proposition expressing simple connectedness.
  - Equality / equivalence condition: categorical equivalence of groupoids, not type equivalence.
  - Side conditions: none beyond the topology.
  - Follow-on claims: this definition supplies the left side of theorem `line-21`.
- Lean coverage: `FundamentalGroupoid X ≌ Discrete Unit` covers “fundamental groupoid equivalent to the groupoid with one object and the identity morphism”; `Discrete Unit` is the explicit one-object identity-morphism groupoid in Mathlib.
- Scope changes: no substantive mathematical change. Representation bridge: the source's unnamed one-object identity groupoid is represented by `CategoryTheory.Discrete Unit`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition only, no source proof. Provers should unfold `paths_homotopic` to obtain the categorical equivalence hypothesis.

### line-21

- Source inventory entry `line-21`: theorem `[simply_connected_iff_paths_homotopic]` in `docs/source.tex`.
- Source label: `line-21`
- Source inventory entry: `line-21`
- Source inventory label: `line-21`
- Source block label: `line-21`
- Preflight label: `line-21`
- Planned Lean declarations: `simply_connected_iff_paths_homotopic`.
- Adopted Lean statement:
  ```lean
  theorem simply_connected_iff_paths_homotopic (X : Type*) [TopologicalSpace X] :
      paths_homotopic X ↔
        PathConnectedSpace X ∧ ∀ x y : X, Subsingleton (Path.Homotopic.Quotient x y) := by
    sorry
  ```
- Source locator: `docs/source.tex`, statement lines 21-23; proof lines 24-26.
- Source statement: “A topological space is simply connected if and only if it is path connected, and there is at most one path up to homotopy between any two points.”
- Complete source proof text: “Let $X$ be a simply connected space. The fundamental groupoid $\Pi X$ being equivalent to a groupoid $\mathcal{E}$ with one object $e$ and the identity morphism, is equivalent to being a groupoid having a unique morphism between any two objects. It is equivalent to say that any two points of $X$ have a unique path between them up to homotopy equivalence. In partiular, $X$ is path connected in such case.”
- Skeleton candidate used: `Skeleton4.lean` suggested the path-based right-hand side; final statement uses quotient subsingletons to match the phrase “at most one path up to homotopy” exactly.
- Dependencies: `paths_homotopic`, `PathConnectedSpace`, `Path.Homotopic.Quotient`, and the fundamental groupoid/path-homotopy correspondence in Mathlib.
- Formal statement review: The Lean theorem quantifies over an arbitrary topological space `X`. The left side is the source definition `paths_homotopic X`; the right side is path connectedness plus uniqueness of path-homotopy classes between every ordered pair of points.
- Source qualifiers:
  - Mathematical object class: topological spaces.
  - Quantifier order / parameter domain: for every `X : Type*` with `[TopologicalSpace X]`, then for every pair `x y : X` on the right-hand uniqueness clause.
  - Output codomain: biconditional proposition.
  - Equality / image condition: uniqueness is represented as a subsingleton of homotopy classes `Path.Homotopic.Quotient x y`.
  - Side conditions: none beyond topological-space structure.
  - Follow-on claims: path connectedness is included explicitly as `PathConnectedSpace X`.
- Lean coverage: `PathConnectedSpace X` covers “path connected”; `∀ x y : X, Subsingleton (Path.Homotopic.Quotient x y)` covers “at most one path up to homotopy between any two points”.
- Scope changes: no substantive mathematical change. Representation bridge: the source's “path up to homotopy” is represented by Mathlib's quotient of paths by `Path.Homotopic`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Unfold `paths_homotopic`. The source proof converts equivalence of the fundamental groupoid with the one-object groupoid into uniqueness of morphisms between any two objects. In Mathlib, morphisms in `FundamentalGroupoid X` correspond to path-homotopy classes, and object nonemptiness/path existence supplies `PathConnectedSpace X`. The reverse direction should build the equivalence to `Discrete Unit` from path-connectedness plus subsingleton homotopy classes, following the proof strategy in `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`.

## Handoff Notes

- Definition construction gaps: none; `paths_homotopic` is implemented without `sorry`.
- Theorem proof obligations intentionally left for the post-review `/prove` workflow: `simply_connected_iff_paths_homotopic`.
- Statement/source verification must review the two inventory entries above before any proof queue is launched.
