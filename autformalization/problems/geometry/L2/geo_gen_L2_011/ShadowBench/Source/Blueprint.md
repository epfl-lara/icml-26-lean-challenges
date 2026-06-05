# Formalization Blueprint: `geometry/L2/geo_gen_L2_011`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem skeleton `isInteriorPoint_of_bijective_mfderiv`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the generated target is covered by the project root.
- `ShadowBench.lean`: imports `ShadowBench.Source` for the default Lake target.

## Import Plan

```lean
import Mathlib
import Aesop
```

## Suggested Search Modules

These modules were identified from Mathlib search as relevant proof-search locations, but they are not direct imports beyond `Mathlib` in the generated file:

- `Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary`
- `Mathlib.Geometry.Manifold.MFDeriv.Defs`
- `Mathlib.Geometry.Manifold.MFDeriv.Basic`
- `Mathlib.Geometry.Manifold.Instances.Real`
- `Mathlib.Geometry.Manifold.Notation`

## Required Names

- `isInteriorPoint_of_bijective_mfderiv`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, lines 17--19.
- Source statement: "Suppose $M$ is a smooth manifold (without boundary), $N$ is a smooth manifold with boundary, and $F: M \to N$ is smooth. Show that if $p \in M$ is a point such that $dF_p$ is nonsingular, then $F(p) \in \operatorname{Int} N$."
- Planned Lean declarations: `isInteriorPoint_of_bijective_mfderiv`.
- Skeleton candidate used: Skeletons 1--3 supplied the required name and the broad hypothesis pattern, but their statement was corrected for Mathlib and source fidelity. In particular, they used invalid/nonstandard classes (`Manifold`, `ManifoldWithBoundary`), used `fderiv` instead of the manifold derivative `mfderiv`, and concluded the topological fact `F p ∈ interior (Set.univ : Set N)`, which is not the source's manifold-interior claim. Skeleton4 was rejected as malformed because it repeats `:= by sorry`.
- Dependencies: `ModelWithCorners`, `IsManifold`, `ContMDiff`, `mfderiv`, `ModelWithCorners.interior`, `modelWithCornersSelf` notation `𝓡 m`, Euclidean half-space notation `𝓡∂ n`, and `Function.Bijective` for nonsingularity.
- Complete source proof text: no proof is present in `docs/source.tex`.
- Formal statement review: The Lean statement quantifies source and target dimensions `m n : ℕ`, with `[NeZero n]` for Mathlib's positive-dimensional Euclidean half-space model, a source manifold `M` modeled on the standard boundaryless real model `𝓡 m`, and a target manifold `N` modeled on the real half-space model `𝓡∂ n`. It assumes both manifolds are smooth via `[IsManifold ... ⊤ ...]`, assumes `F : M → N` is smooth via `ContMDiff (𝓡 m) (𝓡∂ n) ⊤ F`, takes a point `p : M`, assumes nonsingularity as `Function.Bijective (mfderiv (𝓡 m) (𝓡∂ n) F p)`, and concludes `F p ∈ (𝓡∂ n).interior N`, Mathlib's manifold interior of `N` with respect to the half-space model.
- Source qualifiers: mathematical object class is smooth manifolds with `M` without boundary and `N` with boundary; quantifier order is manifold/model data, map `F : M → N`, smoothness hypothesis, point `p : M`, nonsingular differential hypothesis at `p`, then the interior conclusion; parameter domain is `F : M → N` and `p : M`; output/codomain is `F p : N`; there is no equality or image condition beyond evaluating `F` at `p`; side condition is nonsingularity of `dF_p`; follow-on claim/conclusion is exactly `F(p) ∈ Int N`.
- Lean coverage: boundaryless source is covered by `[ChartedSpace (EuclideanSpace ℝ (Fin m)) M]` and `[IsManifold (𝓡 m) ⊤ M]`; target with boundary is covered by `[ChartedSpace (EuclideanHalfSpace n) N]`, `[IsManifold (𝓡∂ n) ⊤ N]`, and `[NeZero n]`; smoothness is `hF : ContMDiff (𝓡 m) (𝓡∂ n) ⊤ F`; nonsingularity is `hp : Function.Bijective (mfderiv (𝓡 m) (𝓡∂ n) F p)`; the output/codomain and evaluation are the term `F p : N`; the interior conclusion is `F p ∈ (𝓡∂ n).interior N`.
- Scope changes: The theorem is formalized in Mathlib's standard finite-dimensional real models `𝓡 m` and `𝓡∂ n`, making explicit the conventional finite-dimensional real-manifold reading of the source. The target half-space model requires `[NeZero n]`, so zero-dimensional target-with-boundary cases are recorded as an explicit representation scope restriction. The Lean statement does not add a same-dimension hypothesis; dimensional compatibility is expressed only through bijectivity of `mfderiv`. The conclusion uses Mathlib's manifold interior `(𝓡∂ n).interior N` rather than the topological interior of `Set.univ`. No Hausdorff or second-countability assumptions are included, which is a harmless generalization for this local statement under Mathlib's manifold API.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no source proof is provided. A prover should work in local charts around `p` and `F p`; if `F p` were a boundary point of the half-space model, then in target coordinates the boundary coordinate is nonnegative and vanishes at the image point. Composing this boundary coordinate with the coordinate expression of `F` gives a smooth real-valued function on a boundaryless/open chart with a local minimum at the source point, so its derivative is zero. This forces the first coordinate functional to vanish on the image of `mfderiv (𝓡 m) (𝓡∂ n) F p`, contradicting the bijectivity of that derivative. Relevant Mathlib notions include `ModelWithCorners.IsInteriorPoint`, `ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint`, `mfderiv`, and the half-space range/interior lemmas in `Mathlib.Geometry.Manifold.Instances.Real`.

## Formalization Rules From Instructions

```text
open scoped Manifold
open Set ContDiff

Formalize in Lean the Theorem (isInteriorPoint_of_bijective_mfderiv) from Text.
The theorem must be named `isInteriorPoint_of_bijective_mfderiv`.
```

## Proof-Ready Checklist

- [x] Source document inspected.
- [x] Companion instructions and skeletons read.
- [x] Local/Mathlib search performed before finalizing declaration shape.
- [x] Blueprint source inventory includes `line-17` with statement coverage and proof notes.
- [x] Target module is imported by the project root import chain.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
