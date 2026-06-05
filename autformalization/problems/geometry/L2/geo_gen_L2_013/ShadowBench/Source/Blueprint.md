# Formalization Blueprint: `geometry/L2/geo_gen_L2_013`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Source locator: docs/source.tex, theorem environment, lines 17--19.
- Source statement: Let gamma : R -> R^2 be the map gamma(t) = (t^3, 0). Show that gamma is a smooth map and a topological embedding, but it is not a smooth embedding.
- Planned Lean declarations: `gamma`, `gamma_smooth`, `gamma_is_embedding`, `gamma_mfderiv_zero`, `gamma_not_smooth_embedding`.
- Lean statements: `gamma : ℝ → ℝ × ℝ`; `gamma_smooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ⊤ gamma`; `gamma_is_embedding : Topology.IsEmbedding gamma`; `gamma_mfderiv_zero : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) gamma 0 = 0`; `gamma_not_smooth_embedding : ¬ Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ⊤ gamma`.
- Skeleton candidate used: Skeleton1.lean, Skeleton2.lean, and Skeleton3.lean all propose the required names and the split into smoothness, topological embedding, zero derivative, and non-smooth-embedding claims; their definition of gamma was adopted. The statement shapes were corrected for current Mathlib and source fidelity: topological embedding is `Topology.IsEmbedding`, the derivative helper uses `mfderiv`, and smooth embedding is `Manifold.IsSmoothEmbedding` with explicit standard Euclidean model-with-corners parameters. Skeleton4.lean is malformed at the end and was not copied.
- Dependencies: `gamma_smooth` depends on `gamma` and smoothness of polynomial and constant coordinate functions. `gamma_is_embedding` depends on `gamma`, injectivity of real cubing, continuity of gamma, and the induced/subspace-topology characterization of `Topology.IsEmbedding`. `gamma_mfderiv_zero` depends on `gamma` and the derivative computation for t -> t^3 at 0 together with the constant second coordinate. `gamma_not_smooth_embedding` depends on `gamma_mfderiv_zero` and the fact that a smooth embedding is an immersion, hence has injective manifold derivative at every point.
- Formal statement review: The Lean draft preserves the domain R, the codomain as a two-real-coordinate space, the defining formula gamma(t) = (t^3, 0), the smoothness claim, the topological-embedding claim, and the non-smooth-embedding claim. The final theorem name `gamma_not_smooth_embedding` states the negative smooth-embedding part, while companion theorems state the other two source claims required by the split in docs/instructions.md.
- Source qualifiers: mathematical object class = a map of smooth Euclidean manifolds from R to R^2; quantifier order = the theorem concerns the single explicitly defined map gamma and has no extra parameters; parameter domain = all real t; output codomain = real two-space R^2; equality/image condition = gamma(t) = (t^3, 0); side conditions = none; follow-on claims = smoothness, topological embedding, and not a smooth embedding; instruction-requested auxiliary claim = the manifold derivative at 0 is zero.
- Lean coverage: `gamma` covers the source map using the product representation R x R for R^2; `gamma_smooth` covers smoothness as manifold smoothness for the standard smooth structures; `gamma_is_embedding` covers the topological embedding claim using Mathlib's `Topology.IsEmbedding`; `gamma_mfderiv_zero` records the derivative obstruction; `gamma_not_smooth_embedding` covers the non-smooth-embedding claim using Mathlib's `Manifold.IsSmoothEmbedding` with explicit Euclidean models.
- Scope changes: none
- Scope changes detail: no weakening or strengthening intended. Representation bridge: R^2 is represented as R x R rather than EuclideanSpace R (Fin 2), matching the source formula (t^3, 0) directly. Declaration split: the single source theorem is split into four theorem declarations plus the definition gamma as required by docs/instructions.md. No source side condition is omitted.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof: no proof is supplied in docs/source.tex; the manifest records an empty proof field for this theorem block.
- Prover notes: For smoothness, prove each coordinate is smooth and combine them as a product-valued ContMDiff map. For the topological embedding, recover t^3 by first projection, use strict monotonicity/injectivity of cubing on R, and prove the induced topology on the image. For the derivative helper, compute the derivative of t -> t^3 at 0 as 0 and pair it with the zero derivative of the constant coordinate. For the final negative claim, use the immersion field of Manifold.IsSmoothEmbedding to get injectivity of the tangent map at 0, then contradict it with `gamma_mfderiv_zero` and nontriviality of the tangent space of R at 0.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single generated formalization file containing the definition `gamma`, the four theorem skeletons, and source-aware prover notes in doc comments.
- `ShadowBench/Source.lean`: source aggregator imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: project root imports `ShadowBench.Source`, so plain project builds cover the generated target module.

No split into additional files is currently useful because the source contains one theorem and the generated formalization is small.

## Import Plan

```lean
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding
```

These are the direct imports used by `ShadowBench/Source/Main.lean` and match its import block.

## Suggested Search Modules

These are proof-time search hints only, not current direct imports:

- `Mathlib.Topology.Defs.Induced` for `Topology.IsEmbedding`.
- `Mathlib.Geometry.Manifold.MFDeriv.Defs` and `Mathlib.Geometry.Manifold.MFDeriv.Basic` for `mfderiv`.
- `Mathlib.Geometry.Manifold.ContMDiff.Constructions` for product-valued smooth maps.

## Search Log

- `formalization_document_inspect` found one theorem block, source inventory label `line-17`, titled `gamma_not_smooth_embedding`, with no proof text.
- Local instructions and all four candidate skeletons were read. Skeletons 1--3 shaped the required split and names; Skeleton4 was rejected as malformed.
- Mathlib search confirmed `Topology.IsEmbedding`, `Manifold.IsSmoothEmbedding`, `ContMDiff`, and `mfderiv` as the relevant declarations for the target statements.

## Handoff Checklist

- [x] Source document inspected with `formalization_document_inspect`.
- [x] Companion instructions and candidate skeletons read and compared against the source.
- [x] Direct Lean import plan recorded and aligned with the target file.
- [x] Source inventory entry `line-17` mapped to `gamma`, `gamma_smooth`, `gamma_is_embedding`, `gamma_mfderiv_zero`, and `gamma_not_smooth_embedding`.
- [x] Compact source proof/prover notes included for the source theorem declarations in Lean.
- [x] Representation bridge for R^2 recorded as the implemented product codomain R x R.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
