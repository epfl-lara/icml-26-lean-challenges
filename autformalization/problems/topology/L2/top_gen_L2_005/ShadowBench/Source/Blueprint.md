# Formalization Blueprint: `topology/L2/top_gen_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Document Inventory

- `docs/source.tex`, lines 17-39, definition environment titled `[setoid]`.
  The block defines the generalized `N`-loop space `Ω^N(X,x)` as continuous maps `I^N → X` sending the boundary `∂I^N` to the basepoint `x`, endowed with the subspace topology inherited from the compact-open topology on continuous maps. It also states continuity of the evaluation map `Ω^N(X,x) × I^N → X`, `(f,y) ↦ f(y)`, and the fixed-point evaluation maps `f ↦ f(y)`.
- No labels, references, citations, bibliography files, PDF files, figures, or support files were detected in the preflight manifest.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: all generated declarations for the source block.
- `ShadowBench/Source.lean`: root project module importing `ShadowBench.Source.Main`, so project builds cover the generated target.

## Import Plan

```lean
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UnitInterval
```

## Suggested Search Modules

- `Mathlib.Topology.CompactOpen` for `ContinuousMap.compactOpen`, fixed evaluation continuity, and full evaluation continuity for locally compact domains.
- `Mathlib.Topology.Compactness.LocallyCompact` for locally compact finite products of compact spaces, used by compact-open evaluation.
- `Mathlib.Topology.UnitInterval` for `unitInterval` as the Lean representation of `I = [0,1]`.

## Required Names

- `setoid`

## Candidate Skeletons

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose the same shape: `setoid` as a subtype of continuous maps from `Π i : Fin N, unitInterval` satisfying a coordinate-boundary condition, plus two continuity theorems.
- `docs/skeletons/Skeleton4.lean` uses the same mathematical encoding with the syntactically simpler domain `Fin N → unitInterval`, an explicit evaluation map, and theorem names `continuous_ev` and `continuous_ev_at`.
- Adopted shape: Skeleton4's encoding, with added source-fidelity companion declarations `cubeBoundary` and `setoid.toContinuousMap`, and theorem names placed in the `setoid` namespace. This matches the source definition of `Ω^N(X,x)` while making the inherited compact-open topology bridge explicit.

## Source Statement Inventory

### line-17

- Planned Lean declarations: cubeBoundary, setoid, instTopologicalSpace, toContinuousMap, ev, continuous_ev, continuous_ev_at
- Source locator: `docs/source.tex`, lines 17-39, theorem-like block label `line-17`, title `setoid`.
- Complete source statement:
  ```text
  Let X be a topological space, x ∈ X and Ω^N(X,x) denote the space of generalized N-loops in X based at x i.e.
  Ω^N(X,x) := { f : I^N → X continuous | f(y)=x for all y ∈ ∂ I^N }.
  With respect to the usual topology on Ω^N(X,x) inherited from the compact-open topology on continuous maps, the evaluation map
  ev : Ω^N(X,x) × I^N → X, (f,y) ↦ f(y),
  is continuous. In particular, for each fixed y ∈ I^N, the map Ω^N(X,x) → X, f ↦ f(y), is continuous.
  ```
- Source proof text: none supplied; the environment is named `definition` but includes continuity assertions.
- Dependencies:
  - `unitInterval` for the interval `I = [0,1]`.
  - Finite product type `Fin N → unitInterval` for `I^N`.
  - `C(Fin N → unitInterval, X)` for bundled continuous maps with compact-open topology.
  - Subtype topology on `setoid X x N` inherited from the continuous-map space.
  - Compact-open evaluation facts, especially fixed evaluation continuity and full evaluation continuity when the domain is locally compact.
- Source qualifiers:
  - Mathematical object class: arbitrary topological space `X`, basepoint `x : X`, natural dimension `N : ℕ`.
  - Parameter domain: `I^N`; Lean representation is `Fin N → unitInterval`.
  - Map class: continuous maps `I^N → X`; Lean uses bundled continuous maps `C(Fin N → unitInterval, X)`.
  - Boundary condition: `f(y)=x` for every `y ∈ ∂I^N`; Lean representation is `∃ i : Fin N, y i = 0 ∨ y i = 1`.
  - Topology: topology on `Ω^N(X,x)` inherited as a subtype of the compact-open topology on bundled continuous maps.
  - Output/codomain: evaluation maps land in the original space `X`.
  - Follow-on claims: continuity of full evaluation and, for each fixed `y`, continuity of fixed-point evaluation.
- Lean coverage:
  - `cubeBoundary N` covers the selected coordinate-face representation of `∂I^N`.
  - `setoid X x N` covers `Ω^N(X,x)` as a subtype of bundled continuous maps satisfying the boundary condition.
  - `setoid.toContinuousMap` records the representation bridge/inherited topology via the subtype inclusion into the compact-open continuous-map space.
  - `setoid.ev` covers the source evaluation function `(f,y) ↦ f(y)`.
  - `setoid.continuous_ev` covers the source full-evaluation continuity assertion.
  - `setoid.continuous_ev_at` covers the fixed-`y` continuity assertion.
- Formal statement review:
  - Quantifier order is `X`, topological-space structure, basepoint `x`, dimension `N`; fixed-evaluation additionally quantifies `y : Fin N → unitInterval` after `N`.
  - The Lean statements keep the source codomain `X` and do not add separation, compactness, or discreteness assumptions on `X`.
  - The Lean domain `Fin N → unitInterval` is the standard finite-product encoding of `I^N`.
  - The chosen boundary predicate is the usual coordinate-face boundary of a cube; this is explicit in `cubeBoundary` rather than hidden in comments.
- Scope changes:
  - Representation bridge: `I^N` is represented by `Fin N → unitInterval`.
  - Boundary representation: `∂I^N` is represented by the coordinate-face predicate `∃ i, y i = 0 ∨ y i = 1`. This is exact for the standard cube boundary convention, but it is an explicit formalization choice because the source does not define `∂I^N` separately.
  - No source assumption on `X` is added or removed.
- Skeleton candidate used: Skeleton4, with the same core type and evaluation shape; extra bridge declarations were added to document source fidelity.
- Source proof / prover notes:
  - There is no explicit proof in the source. For `setoid.continuous_ev`, unfold `setoid.ev`; view `setoid X x N` as a subtype of `C(Fin N → unitInterval, X)` via `setoid.toContinuousMap`; compose the continuous inclusion/product map with the compact-open evaluation map. The finite product `Fin N → unitInterval` should be locally compact/compact, enabling full compact-open evaluation continuity.
  - For `setoid.continuous_ev_at`, either compose `setoid.continuous_ev` with the continuous map `f ↦ (f,y)` or use fixed evaluation continuity for `ContinuousMap` and compose with the subtype inclusion.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Verification Notes

- `lean_search` results used before drafting: `ContinuousMap.compactOpen`, `ContinuousMap.instContinuousEvalConst`, `ContinuousMap.instContinuousEvalOfLocallyCompactPair`, `ContinuousEval`, `ContinuousEvalConst`, `LocallyCompactSpace`, `instLocallyCompactPairOfLocallyCompactSpace`, `Pi.locallyCompactSpace`, and `unitInterval`.
- `ShadowBench/Source.lean` already imports `ShadowBench.Source.Main`.
- Proof handoff should wait for independent statement/source review of `line-17`.

## Formalization Rules

```text
open scoped unitInterval Topology
open Homeomorph

Formalize in Lean the Definition (setoid) from Text.
The definition must be named `setoid`.
```
