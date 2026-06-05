# Formalization Blueprint: `geometry/L2/geo_diff_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the local integral-curve definitions needed by the source statement and the source lemma `isMIntegralCurveAt_iff'` as a `by sorry` proof obligation for the prover queue.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target module is covered by project-level verification.

No file split is currently useful: the source has one theorem-like block and two small supporting definitions.

## Import Plan

```lean
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
```

This is the direct import used by `ShadowBench/Source/Main.lean`, matching the allowed import block from `docs/instructions.md`.

## Suggested Search Modules

- `Mathlib.Geometry.Manifold.IntegralCurve.Basic`: contains Mathlib's analogous definitions `IsMIntegralCurveOn`, `IsMIntegralCurveAt` and related lemmas (`isMIntegralCurveAt_iff`, Mathlib's ball-neighborhood theorem `isMIntegralCurveAt_iff'`). It is intentionally not a direct import for this draft because it already declares the required name `isMIntegralCurveAt_iff'`.
- Search used during planning: `lean_search` for `isMIntegralCurveAt`, `integral curve vector field manifold`, `IsMIntegralCurveOn.isMIntegralCurveAt`, and `IsMIntegralCurveAt.isMIntegralCurveOn`.

## Required Names

- `isMIntegralCurveAt_iff'`

## Supporting Definitions

### `IsMIntegralCurveOn`

- Source role: formalizes “`Γ` is an integral curve of `v` on `U`.”
- Lean declaration: `def IsMIntegralCurveOn (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (U : Set ℝ) : Prop`.
- Definition choice: follows the Mathlib definition in `Mathlib.Geometry.Manifold.IntegralCurve.Basic`: for each `t ∈ U`, the manifold derivative of `γ` within `U` is the continuous linear map sending a scalar to that scalar times `v (γ t)`.
- Construction status: implemented directly, no proof gap.

### `IsMIntegralCurveAt`

- Source role: formalizes “`Γ` is an integral curve of `v` at `t₀`.”
- Lean declaration: `def IsMIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop`.
- Definition choice: follows the Mathlib definition in `Mathlib.Geometry.Manifold.IntegralCurve.Basic`: the defining manifold derivative relation holds eventually in the neighborhood filter `𝓝 t₀`.
- Construction status: implemented directly, no proof gap.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, label `line-17`, lines 17--20.
- Source kind/title: lemma `isMIntegralCurveAt_iff'`.
- Source statement: “Let `M` be a manifold and `v` be a vector field on `M`. Then `Γ : ℝ → M` is an integral curve of `v` at `t₀` if and only if there exists an open neighborhood `U` of `t₀` such that `Γ` is an integral curve of `v` on `U`.”
- Source statement (verbatim from manifest): Let $M$ be a manifold and $v$ be a vector field on $M$. Then $\Gamma : ℝ → M$ is an integral curve of $v$ at $t_o$ if and only if there exists an open neighborhood $U$ of $t_o$ such that $\Gamma$ is an integral curve of $v$ on $U$.
- Planned Lean declarations: theorem `isMIntegralCurveAt_iff'`.
- Skeleton candidate used: skeleton files 1--4 were read; they supplied only the required name and broad iff shape. Their proposed statement uses non-manifold `deriv` and a non-existent `[Manifold ℝ M]` class, so the reviewed Lean statement instead uses manifold derivatives and tangent-space-valued vector fields.
- Dependencies: local definitions `IsMIntegralCurveAt`, `IsMIntegralCurveOn`; `Set.IsOpen`; neighborhood filter notation `𝓝`; `HasMFDerivAt` / `HasMFDerivWithinAt`; `TangentSpace`; continuous linear maps over `ℝ`.
- Formal statement review:
  The Lean theorem states
  `IsMIntegralCurveAt Γ v t₀ ↔ ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ IsMIntegralCurveOn Γ v U`.
  This matches the source iff between the local integral-curve condition at `t₀` and the existence of an open neighborhood on which the same curve is an integral curve of the same vector field.
- Source qualifiers:
  - Mathematical object class: `M` is a manifold; in Lean this is represented by a model with corners `I`, a topology, a charted-space structure, and `[IsManifold I 1 M]`.
  - Quantifier order: after the manifold/model data, the vector field `v`, curve `Γ`, and distinguished time `t₀` are universally quantified.
  - Parameter domain: the time parameter is real, `t₀ : ℝ`, and neighborhoods are subsets of `ℝ`.
  - Output codomain: the curve has codomain `M`, `Γ : ℝ → M`.
  - Vector field representation: `v : (x : M) → TangentSpace I x`, a dependent section of the tangent spaces over `M`.
  - Equality/condition: an iff between `IsMIntegralCurveAt Γ v t₀` and existence of `U : Set ℝ` with `IsOpen U`, `t₀ ∈ U`, and `IsMIntegralCurveOn Γ v U`.
  - Side conditions: `U` is open and contains `t₀`; the integral-curve predicates use manifold derivatives and tangent spaces.
  - Follow-on claims: none in the source statement.
- Lean coverage:
  Full coverage. The theorem parameters cover the manifold/model data, vector field, curve, and time. The left side covers “integral curve at `t₀`”; the right side covers “there exists an open neighborhood `U` of `t₀`” by `IsOpen U ∧ t₀ ∈ U` and “integral curve on `U`” by `IsMIntegralCurveOn Γ v U`. The local definitions give the representation bridge from the source integral-curve terminology to Mathlib-style manifold derivatives.
- Scope changes: none to the mathematical content. The Lean statement makes explicit the standard Mathlib representation of a differentiable manifold and of vector fields as tangent-space-valued dependent functions.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: `docs/source.tex` contains no proof environment or proof text for this lemma; the manifest records an empty proof field.
- Source proof / prover notes: unfold `IsMIntegralCurveAt` as an eventual property in `𝓝 t₀`. Forward, use `Filter.eventually_iff_exists_mem` to obtain a neighborhood set where the derivative relation holds; use `mem_nhds_iff` to choose an open set `U` containing `t₀` inside that neighborhood; then restrict point derivatives to within-`U` derivatives for `IsMIntegralCurveOn`. Reverse, use `hU_open.mem_nhds hU_mem` to make the open neighborhood eventual at `t₀`; for each eventual `t ∈ U`, convert the within-`U` derivative supplied by `IsMIntegralCurveOn` to a point derivative using `.hasMFDerivAt` and the fact that `U` is a neighborhood of each of its points.

## Formalization Rules from Instructions

```text
open scoped Manifold Topology
open Set

Formalize in Lean the Lemma (isMIntegralCurveAt_iff') from Text.
The lemma must be named `isMIntegralCurveAt_iff'`.
```

## Review Gate

- Statement/source verification: required before proof handoff.
- Proof-ready checklist item: intentionally not checked by this planner draft.
