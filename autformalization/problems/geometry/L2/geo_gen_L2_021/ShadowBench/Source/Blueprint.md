# Formalization Blueprint: `geometry/L2/geo_gen_L2_021`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`.
- Source label: `line-17`.
- Source kind: theorem.
- Source title: `global_integralCurve_unique_fundamental_period`.
- Source locator: `line-17` (`docs/source.tex:17-19`).
- Source statement: Suppose $M$ is a smooth manifold, $X \in \mathfrak{X}(M)$, and $\gamma: \mathbb{R} \to M$ is a global integral curve of $X$. We say $\gamma$ is periodic if there is a number $T > 0$ such that $\gamma(t + T) = \gamma(t)$ for all $t \in \mathbb{R}$. Show that if $\gamma$ is periodic and nonconstant, then there exists a unique positive number $T$ (called the period of $\gamma$) such that $\gamma(t) = \gamma(t')$ if and only if $t - t' = kT$ for some $k \in \mathbb{Z}$.
- Complete source proof text: none provided in the source document.
- Planned Lean declarations: `global_integralCurve_unique_fundamental_period`.
- Generated declarations: `global_integralCurve_unique_fundamental_period`.
- Skeleton candidate used: Skeletons 1--3 supplied the intended semantic shape and required name, but their concrete identifiers (`SmoothManifold ℝ M`, `VectorField`, `IsGlobalIntegralCurve`) are not the Mathlib names available in this project. Skeleton4 is the same candidate plus an extra malformed `:= by sorry`, so it was not copied. The final Lean statement uses Mathlib's manifold integral-curve API directly.
- Dependencies: `IsMIntegralCurve`, `TangentSpace`, `TangentBundle`, `CMDiff`, `BoundarylessManifold`, `T2Space`, `SecondCountableTopology`, `FiniteDimensional`, real/int arithmetic, and later proof facts such as `IsMIntegralCurve.periodic_of_eq`, `IsMIntegralCurve.continuous`, and the additive-subgroup cyclic/dense dichotomy for subgroups of `ℝ`.
- Source qualifiers:
  - Mathematical object class: smooth finite-dimensional real manifold without boundary, represented by a model-with-corners charted space.
  - Vector field: $X \in \mathfrak{X}(M)$, represented by a dependent section `X : (x : M) → TangentSpace I x` plus smoothness hypothesis `hX_smooth : CMDiff ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M))`.
  - Curve domain/codomain: `γ : ℝ → M`.
  - Global integral curve side condition: `hγ_global : IsMIntegralCurve γ X`.
  - Periodicity side condition: `∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, γ (t + T) = γ t`.
  - Nonconstant side condition: `¬ ∃ x : M, ∀ t : ℝ, γ t = x`.
  - Output: unique positive real `T`.
  - Equality/image condition: for all `t t' : ℝ`, `γ t = γ t' ↔ ∃ k : ℤ, t - t' = (k : ℝ) * T`.
- Lean coverage: intended exact coverage modulo Mathlib representation bridges for smooth manifolds and smooth vector fields. The theorem includes the source periodicity definition as an explicit hypothesis and the source self-intersection characterization as an explicit conclusion.
- Scope changes: no intended mathematical weakening. The Lean statement spells out standard manifold-side assumptions needed by Mathlib (`T2Space`, `SecondCountableTopology`, `FiniteDimensional ℝ E`, and `BoundarylessManifold I M`) instead of relying on the informal phrase "smooth manifold". The model-with-corners parameters `{E, H, I}` are representation data not present in the prose.
- Formal statement review: drafted directly from `docs/source.tex` after checking the candidate skeletons and Mathlib search results. The final statement avoids the non-existent skeleton identifiers and uses `IsMIntegralCurve` from `Mathlib.Geometry.Manifold.IntegralCurve.Basic`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: The source gives no proof. A later prover should consider the additive subgroup of periods `{s : ℝ | ∀ t, γ (t + s) = γ t}`. Periodicity gives a nonzero positive element. Integral-curve uniqueness implies any self-intersection `γ t = γ t'` makes `t - t'` a period (see `IsMIntegralCurve.periodic_of_eq`). If the period subgroup were dense, continuity of the integral curve would force `γ` to be constant, contradicting the nonconstant hypothesis. Therefore the period subgroup should be cyclic with a least positive generator `T`; this generator gives the stated iff and its uniqueness.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

These are proof-search hints only and are intentionally not direct imports in the generated Lean file:

- `Mathlib.Geometry.Manifold.IntegralCurve.Basic`
- `Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique`
- `Mathlib.Algebra.Ring.Periodic`
- `Mathlib.Topology.Algebra.Order.Archimedean`

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem statement with a `by sorry` proof placeholder.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

## Required Names

- `global_integralCurve_unique_fundamental_period`

## Formalization Rules from Instructions

```text
open scoped Manifold ContDiff

Formalize in Lean the Theorem (global_integralCurve_unique_fundamental_period) from Text.
The theorem must be named `global_integralCurve_unique_fundamental_period`.
```

## Handoff Checklist

- [x] Source document inspected.
- [x] Companion instructions and skeletons read.
- [x] Local/Mathlib search performed before drafting.
- [x] Blueprint source inventory entry for `line-17` created.
- [x] Direct import plan aligned with `ShadowBench/Source/Main.lean`.
- [x] Root project module imports the generated target through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
