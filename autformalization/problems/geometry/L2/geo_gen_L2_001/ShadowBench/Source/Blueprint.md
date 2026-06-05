# Formalization Blueprint: `geometry/L2/geo_gen_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file draft containing the source-local integral-curve predicate bridge and the source lemma skeleton.
- `ShadowBench/Source.lean`: root source aggregator; imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: project root; imports `ShadowBench.Source` so plain project builds cover the generated target module.

## Import Plan

Direct imports for `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
```

The direct import plan matches the current target Lean file. Imports remain first in the generated Lean file.

## Suggested Search Modules

These are proof-search and statement-review hints only; they are not direct imports in the draft.

- `Mathlib.Geometry.Manifold.IntegralCurve.Basic`: contains Mathlib's `IsMIntegralCurveAt`, `IsMIntegralCurveOn`, `isMIntegralCurveAt_iff`, and a theorem named `isMIntegralCurveAt_iff'`. It shaped the source-local bridge predicates, but importing it directly would reserve the required global theorem name `isMIntegralCurveAt_iff'` before the target file can declare the source lemma.

## Required Names

- `isMIntegralCurveAt_iff'`

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

All four candidate skeletons propose the required theorem name, but their displayed statement uses `DifferentiableAt` and `deriv` for a curve into an arbitrary manifold-like type. That representation is not source-faithful for a general manifold in Mathlib. The final statement instead uses manifold derivatives and dependent tangent spaces, matching the Mathlib integral-curve definitions found by local/Mathlib search.

## Source Statement Inventory

### line-17

- Title: lemma `isMIntegralCurveAt_iff'`
- Planned Lean declarations: `isMIntegralCurveAt_iff'`
- Support declarations:
  - `ShadowBench.Source.IsMIntegralCurveAt`
  - `ShadowBench.Source.IsMIntegralCurveOn`
- Source locator: `docs/source.tex`, lines 17-20
- Source statement: “Let $M$ be a manifold and $v$ be a vector field on $M$. Then $\Gamma : ℝ → M$ is an integral curve of $v$ at $t_o$ if and only if there exists an open neighborhood $U$ of $t_o$ such that $\Gamma$ is an integral curve of $v$ on $U$."
- Complete source proof text: no proof is supplied in the source document.
- Skeleton candidate used: no skeleton was adopted verbatim. Skeletons 1-4 were used only as naming/source-location hints. Mathlib search for `IsMIntegralCurveAt`, `IsMIntegralCurveOn`, and `isMIntegralCurveAt_iff` supplied the source-faithful manifold-derivative representation.
- Dependencies:
  - Direct import: `Mathlib.Geometry.Manifold.MFDeriv.Tangent`
  - Manifold data: `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]`, `{H : Type*} [TopologicalSpace H]`, `{I : ModelWithCorners ℝ E H}`, `{M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]`
  - Vector field: `v : (x : M) → TangentSpace I x`
  - Curve/time: `Γ : ℝ → M`, `t₀ : ℝ`
  - Source-local predicate bridge: `ShadowBench.Source.IsMIntegralCurveAt Γ v t₀` is the neighborhood-filter version of the integral-curve-at condition; `ShadowBench.Source.IsMIntegralCurveOn Γ v U` is the within-set manifold-derivative condition.
- Formal statement review:
  - Source “manifold” is represented by standard Mathlib model-with-corners, charted-space, and `IsManifold I 1 M` assumptions over `ℝ`.
  - Source “vector field on `M`” is represented by the dependent function `v : (x : M) → TangentSpace I x`.
  - Source curve `Γ : ℝ → M` and time `t_o` are represented directly as `Γ : ℝ → M` and `t₀ : ℝ`.
  - Source “integral curve at `t_o`” is represented by `ShadowBench.Source.IsMIntegralCurveAt Γ v t₀`, defined as the manifold-derivative equation eventually in `𝓝 t₀`.
  - Source “there exists an open neighborhood `U` of `t_o`” is represented by `∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ ...`.
  - Source “integral curve on `U`” is represented by `ShadowBench.Source.IsMIntegralCurveOn Γ v U`, defined using `HasMFDerivAt[U]` at every `t ∈ U`.
- Source qualifiers:
  - Mathematical object class: real smooth manifold modeled by a model-with-corners `I`; tangent vectors live in `TangentSpace I x`.
  - Quantifier order: model and manifold data, then curve `Γ`, vector field `v`, and time `t₀`.
  - Parameter domains: `Γ : ℝ → M`, `v : (x : M) → TangentSpace I x`, `t₀ : ℝ`, and `U : Set ℝ`.
  - Output codomain: proposition asserting a logical equivalence.
  - Equality/derivative condition: the manifold derivative sends the unit direction in `ℝ` to `v (Γ t)`, encoded as `((1 : ℝ →L[ℝ] ℝ).smulRight <| v (Γ t))`.
  - Side conditions: `U` is open and contains `t₀`.
  - Follow-on claims: none.
- Lean coverage: full for the source statement under the explicit source-local integral-curve bridge predicates. The bridge records the richer manifold/vector-field representation instead of the skeletons' simpler `deriv`-based encoding.
- Scope changes: no intended weakening or strengthening. The only representation choice is to keep source-local predicates in namespace `ShadowBench.Source` so the target file can declare the required global theorem name without colliding with Mathlib's existing theorem of the same name.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: the source has no proof. A later proof should unfold `ShadowBench.Source.IsMIntegralCurveAt` and `ShadowBench.Source.IsMIntegralCurveOn`, then use `Filter.eventually_iff_exists_mem` and `mem_nhds_iff`. The forward direction extracts a neighborhood from the eventual condition and replaces it by an open subset containing `t₀`; the backward direction turns an open set containing `t₀` into a member of `𝓝 t₀` and obtains the pointwise manifold derivative from the within-set derivative.

## Formalization Rules

```text
open scoped Manifold Topology
open Set

Formalize in Lean the Lemma (isMIntegralCurveAt_iff') from Text.
The lemma must be named `isMIntegralCurveAt_iff'`.
```

## Review Checklist

- [x] Source document and manifest inspected.
- [x] Candidate skeletons compared against the source.
- [x] Mathlib/local search used before drafting.
- [x] Direct imports recorded and aligned with `ShadowBench/Source/Main.lean`.
- [x] Root project module imports the generated target module path.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
