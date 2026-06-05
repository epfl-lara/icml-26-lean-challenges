# Formalization Blueprint: `geometry/L3/geo_gen_L3_004`

- Source document: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Planner status: independent statement/source review checked the source-backed Lean statement in this pass; the approval stamp remains to be recorded by the workflow runner after a reviewer `PASS`; the theorem proof remains intentionally deferred to the prover workflow.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: direct Mathlib import, the `SmoothVectorFields` representation bridge, and the source-backed theorem skeleton `smoothVectorField_infinite_dimensional`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the project default target covers the generated source module.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

These are proof-search hints only, not direct imports unless the prover later needs a narrower import set.

- `Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection`
- `Mathlib.Geometry.Manifold.VectorBundle.Tangent`
- `Mathlib.Geometry.Manifold.PartitionOfUnity`
- `Mathlib.Analysis.SpecialFunctions.SmoothTransition`
- Search terms used during drafting: `ContMDiffSection`, `TangentSpace`, `smooth vector fields`, `FiniteDimensional`.

## Required Names

- `smoothVectorField_infinite_dimensional`

## Definitions and Representation Bridges

### `SmoothVectorFields`

- Planned Lean declaration: `abbrev SmoothVectorFields`
- Purpose: represent the source notation `𝔛(M)` as Mathlib's type of infinitely differentiable sections of the tangent bundle.
- Lean shape: `ContMDiffSection I E ∞ (TangentSpace I : M → Type _)`.
- Source pointer: the phrase “`𝔛(M)`, the space of smooth vector fields on `M`” in `docs/source.tex`, theorem `line-17`.
- Dependencies: `ModelWithCorners`, `IsManifold`, `TangentSpace`, `ContMDiffSection`.
- Construction status: implemented as an abbreviation; no construction proof gap or `sorry` is introduced.
- Representation note: Mathlib parameterizes manifolds by a model with corners `I : ModelWithCorners ℝ E H`; this explicitly records the source's “with or without boundary” representation instead of using the invalid candidate names `Manifold`, `SmoothSections`, or `T`.

## Source Statement Inventory

- `line-17`: mapped to Lean declaration `smoothVectorField_infinite_dimensional`.
- Source inventory entry `line-17`: mapped to Lean declaration `smoothVectorField_infinite_dimensional`.

### line-17

Source inventory entry: `line-17`.

#### Theorem `smoothVectorField_infinite_dimensional`

- Source kind: theorem.
- Source locator: `docs/source.tex`, theorem block lines 17-19; proof environment lines 21-31, with proof text on lines 22-30.
- Planned Lean declarations: `smoothVectorField_infinite_dimensional`.
- Skeleton candidate used: Skeletons 1-3 supplied the expected theorem name and the intended idea “positive tangent dimension implies not finite-dimensional vector fields”; their raw statement was not copied because `[Manifold ℝ M]`, `SmoothSections`, and `T M` do not elaborate in this Mathlib project. Skeleton4 is malformed and was not used.
- Dependencies: `SmoothVectorFields`, `ContMDiffSection.instModule`, `TangentSpace`, `IsManifold`, `ModelWithCorners`, `T2Space`, `FiniteDimensional`, `Module.finrank`.
- Formal statement review: the reviewed Lean statement makes the source hypotheses explicit: a Hausdorff, nonempty, infinitely smooth real charted manifold represented by a Mathlib model with corners, modeled by a finite-dimensional real vector space of positive `Module.finrank`, and the conclusion that the smooth tangent-bundle section space is not `FiniteDimensional` over `ℝ`. The `SmoothVectorFields` abbreviation records the bridge from the source notation `𝔛(M)` to Mathlib's `ContMDiffSection`.
- Formal Lean statement under verifier pass:

```lean
theorem smoothVectorField_infinite_dimensional
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [Nonempty M] [FiniteDimensional ℝ E]
    (h_pos : 0 < Module.finrank ℝ E) :
    ¬ FiniteDimensional ℝ (SmoothVectorFields I M) := by
  sorry
```

- Source qualifiers:
  - Mathematical object class: a smooth real manifold with or without boundary; Lean encodes this as a charted space `M` with model-with-corners `I : ModelWithCorners ℝ E H`, smoothness `[IsManifold I ∞ M]`, and Hausdorff topology `[T2Space M]` matching the source proof's use of Hausdorffness.
  - Quantifier order: the Lean statement quantifies over the model vector space `E`, model space `H`, manifold carrier `M`, the model with corners `I`, then the topological/charted/smooth/Hausdorff/nonempty/finite-dimensional instances, followed by the positive-dimension hypothesis.
  - Parameter domain: `E` is a real normed vector space with `[FiniteDimensional ℝ E]`; `H` is the model topological space for possible boundary; `M` is a Hausdorff charted topological space over `H`.
  - Output codomain: a proposition over the real vector space of smooth tangent-bundle sections.
  - Equality/image conditions: none in the source theorem.
  - Side conditions: nonempty `M`; positive dimension made explicit as `0 < Module.finrank ℝ E`; Hausdorffness made explicit as `[T2Space M]`; smoothness is infinite differentiability via `[IsManifold I ∞ M]` and `∞`-smooth sections.
  - Follow-on claim: “infinite-dimensional” is represented as `¬ FiniteDimensional ℝ (SmoothVectorFields I M)`.
- Lean coverage: exact for the source claim under Mathlib's standard explicit parameters for finite-dimensional real smooth manifolds with or without boundary: `𝔛(M)` is represented by the companion abbreviation `SmoothVectorFields I M`, and “infinite-dimensional” is the negation of `FiniteDimensional` over `ℝ`.
- Scope changes: no intended weakening. The finite-dimensional model-space assumption and Hausdorff assumption are made explicit because the source phrase “positive-dimensional smooth manifold” and the proof's separated-neighborhood step use the ordinary finite-dimensional Hausdorff manifold convention. Mathlib's general `ModelWithCorners` parameter is an intentional representation generality that also covers corner-style models; the source's with/without-boundary cases are included, and the structured object `𝔛(M)` is bridged by `SmoothVectorFields`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Statement/source verification notes: independent review compared `docs/source.tex`, the complete proof text, the Lean declaration, and the nearby Lean doc comment. The review corrected the missing Hausdorff side condition by adding `[T2Space M]` to the Lean theorem and updating the doc comment and coverage fields; the workflow runner should record the approval stamp after this verifier pass.
- Source proof / prover notes: use the complete source proof below. The prover should argue by contradiction from finite-dimensionality, choose `k + 1` separated points in a positive-dimensional chart, build bump-supported multiples of a nonzero local coordinate vector field, and evaluate a linear relation at the chosen points to contradict dimension `k`.
- Proof obligation status: theorem proof intentionally deferred with `by sorry` for the later `/prove` workflow.

#### Complete source proof text

Suppose `𝔛(M)` is finite-dimensional with dimension `k`. Since `dim M ≥ 1`, we can choose `k+1` distinct points `x₁, …, xₖ₊₁` in a coordinate chart `U ⊆ M`. Because `M` is Hausdorff, there exist pairwise disjoint open neighborhoods `U₁, …, Uₖ₊₁ ⊆ U` for these points.

For each `i`, let `fᵢ ∈ C^∞(M)` be a smooth bump function supported on `Uᵢ` such that `fᵢ(xᵢ) = 1`. Let `V = ∂/∂x¹` be a local coordinate vector field on `U`, and define global vector fields `Xᵢ = fᵢ V` (extended by `0` outside `U`). Since the `Xᵢ` have disjoint supports, they are linearly independent: `∑ cᵢ Xᵢ = 0` implies `cⱼ Xⱼ(xⱼ) = cⱼ V|_{xⱼ} = 0`, so each `cⱼ = 0`.

This contradicts the assumption `dim 𝔛(M) = k`. Therefore, `𝔛(M)` is infinite-dimensional.

#### Prover notes

- Use contradiction from `[FiniteDimensional ℝ (SmoothVectorFields I M)]`; let `k = Module.finrank ℝ (SmoothVectorFields I M)` or use a basis/cardinality argument.
- Use `h_pos` and a chart to obtain a nonzero local coordinate direction; the proof needs a local coordinate vector field analogous to `∂/∂x¹`.
- Choose `k + 1` distinct points in a coordinate chart and separate them by disjoint open neighborhoods using Hausdorffness of manifolds.
- Produce smooth bump functions supported in the separated neighborhoods. Relevant search hints include smooth transition functions, partitions of unity, and `ContMDiffOn.smul_section_of_tsupport`.
- Multiply the local coordinate vector field by each bump and extend by zero to global smooth tangent sections. Evaluate at the chosen points to prove linear independence, contradicting finite-dimensionality.

## Drafting Notes

- Source document and preflight manifest were read.
- Candidate skeletons were compared against the source and current Mathlib names.
- Local and Mathlib searches were performed before drafting declarations.
- Root project module already imports the generated target module path.
- No theorem, lemma, or example proof has been attempted in this formalization phase.
- No definition, structure, class, or instance construction gap remains: `SmoothVectorFields` is an abbreviation.

## Handoff Gate

- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.

After the verifier pass is recorded, suggested proof command:

```text
/prove ShadowBench/Source/Main.lean smoothVectorField_infinite_dimensional
```
