# Formalization Blueprint: `geometry/L2/geo_diff_L2_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Document and Support Files Read

- `docs/source.tex` inspected with `formalization_document_inspect`; source label is `line-17`.
- Preflight manifest read from `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Planner context read from `.epflemma/workflow-state/formalization/docs-source/context.md`.
- Required ShadowBench support files read: `docs/instructions.md`, `docs/skeletons/README.md`, and `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean`.
- The manifest listed no bibliography files, citations, local PDFs, or figures.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: companion representation definitions `IsMIntegralCurveOn` and `IsMIntegralCurveAt`, and source-backed theorem `isMIntegralCurveAt_iff'`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level `lake build` covers the target module.

## Import Plan

```lean
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
```

## Suggested Search Modules

- `Mathlib.Geometry.Manifold.IntegralCurve.Basic`: contains Mathlib's integral-curve definitions and related lemmas, including nearby theorem names. It is intentionally not a direct import in this draft because it already declares a root theorem named `isMIntegralCurveAt_iff'`, which would conflict with the required source declaration name.
- Useful proof-search terms: `Filter.eventually_iff_exists_mem`, `mem_nhds_iff`, `IsOpen.mem_nhds`, `HasMFDerivAt.hasMFDerivWithinAt`, `HasMFDerivWithinAt.hasMFDerivAt`.

## Required Names

- `isMIntegralCurveAt_iff'`

## Search and Skeleton Notes

- Mathlib/local search found `IsMIntegralCurveAt`, `IsMIntegralCurveOn`, `isMIntegralCurveAt_iff`, and a nearby Mathlib theorem named `isMIntegralCurveAt_iff'` in `Mathlib.Geometry.Manifold.IntegralCurve.Basic`.
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` have the required theorem name and open-neighborhood shape, but they encode a manifold as `[Manifold ℝ M]` and use ordinary `deriv` for a manifold-valued curve; that is not the Mathlib manifold-derivative representation used by `MFDeriv.Tangent`.
- `docs/skeletons/Skeleton4.lean` has the same statement-shape issue and additionally has a malformed duplicate trailing `:= by sorry`.
- The final draft keeps the required theorem name, follows the source's local-at/local-on equivalence, and implements lightweight local bridge predicates using the same manifold derivative primitives used by Mathlib.

## Companion Representation Declarations

### `IsMIntegralCurveOn`

- Purpose: Lean predicate for “`Γ` is an integral curve of `v` on `U`”.
- Mathematical content: for every `t ∈ U`, the manifold derivative of `Γ` within `U` sends `1 : ℝ` to the tangent vector `v (Γ t)`.
- Source role: representation bridge for the source phrase “integral curve of `v` on `U`”.
- Construction status: implemented directly from Mathlib manifold derivative primitives; no proof stub.

### `IsMIntegralCurveAt`

- Purpose: Lean predicate for “`Γ` is an integral curve of `v` at `t₀`”.
- Mathematical content: eventually in the neighborhood filter `𝓝 t₀`, the manifold derivative of `Γ` at each time sends `1 : ℝ` to `v (Γ t)`.
- Source role: representation bridge for the source phrase “integral curve of `v` at `t₀`”.
- Construction status: implemented directly from Mathlib manifold derivative primitives; no proof stub.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, lemma lines 17--20.
- Source kind/title: lemma `[isMIntegralCurveAt_iff']`.
- Source statement: Let `M` be a manifold and `v` be a vector field on `M`. Then `Γ : ℝ → M` is an integral curve of `v` at `t_o` if and only if there exists an open neighborhood `U` of `t_o` such that `Γ` is an integral curve of `v` on `U`.
- Complete source proof text: none provided in `docs/source.tex`.
- Planned Lean declarations: `isMIntegralCurveAt_iff'`
- Lean statement:
  ```lean
  theorem isMIntegralCurveAt_iff'
      {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      {v : (x : M) → TangentSpace I x} {Γ : ℝ → M} {t₀ : ℝ} :
      IsMIntegralCurveAt Γ v t₀ ↔
        ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ IsMIntegralCurveOn Γ v U := by sorry
  ```
- Dependencies: direct import `Mathlib.Geometry.Manifold.MFDeriv.Tangent`; companion declarations `IsMIntegralCurveAt` and `IsMIntegralCurveOn`; topology facts about neighborhoods of open sets for the future proof.
- Formal statement review: The Lean theorem keeps the required source name and states exactly the local-at/local-on equivalence from the source. The right side expands “an open neighborhood `U` of `t_o`” to `U : Set ℝ`, `IsOpen U`, and `t₀ ∈ U`; “`Γ` is an integral curve of `v` on `U`” is represented by `IsMIntegralCurveOn Γ v U`.
- Source qualifiers:
  - Mathematical object class: `M` is represented by a type with `TopologicalSpace M`, `ChartedSpace H M`, a model-with-corners `I : ModelWithCorners ℝ E H`, and theorem-side manifold smoothness `[IsManifold I 1 M]`.
  - Quantifier order / parameter domain: for arbitrary model/manifold data, take a vector field `v : (x : M) → TangentSpace I x`, a curve `Γ : ℝ → M`, and a base time `t₀ : ℝ`.
  - Output codomain: the statement is a proposition, an equivalence between local-at and local-on integral-curve predicates.
  - Equality/image condition: the bridge predicates require the manifold derivative of `Γ` to be the continuous linear map sending scalar input to the tangent vector `v (Γ t)`.
  - Side conditions: the right-hand set `U` is explicitly open and contains `t₀`.
  - Follow-on claims: none.
- Lean coverage: source-equivalent under the standard Mathlib representation of differentiable manifolds and tangent-vector-valued vector fields; the source's “open neighborhood” is encoded directly as `IsOpen U ∧ t₀ ∈ U`.
- Scope changes: Lean makes explicit the model vector space `E`, model space `H`, model-with-corners `I`, charted-space structure, and `C^1` manifold typeclass used to interpret “manifold” for manifold derivatives. If the source intended arbitrary charted spaces without a manifold compatibility condition, this Lean statement is more specialized; otherwise there is no mathematical weakening or strengthening.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: The source gives no proof. A proof should unfold `IsMIntegralCurveAt` and `IsMIntegralCurveOn`. For the forward direction, use `Filter.eventually_iff_exists_mem` and refine the neighborhood set to an open set using `mem_nhds_iff`; within that open set convert `HasMFDerivAt` to `HasMFDerivWithinAt`. For the reverse direction, use `IsOpen.mem_nhds` from `IsOpen U` and `t₀ ∈ U`, then convert the within-`U` derivative back to an at-derivative on the neighborhood.

## Formal Statement Review Summary

- `line-17` is represented by the required theorem `isMIntegralCurveAt_iff'`.
- The draft preserves the curve domain `ℝ`, codomain `M`, vector field target `TangentSpace I x`, base time `t₀`, and the existence of an open neighborhood carrying the integral-curve-on condition.
- The draft deliberately leaves the theorem proof as `by sorry` for a later `/prove` workflow, as required by the document-formalization contract.

## Verification Plan and Handoff

- Draft readiness checks: `lean_inspect ShadowBench/Source/Main.lean`, then project-level `lean_verify(mode=project)`.
- Independent statement/source review must approve or correct `line-17` before proof handoff.
- Suggested next proof command after review approval: `/prove ShadowBench/Source/Main.lean isMIntegralCurveAt_iff'`

## Proof-Ready Checklist

- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.
