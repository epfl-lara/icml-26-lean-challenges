# Formalization Blueprint: `geometry/L2/geo_gen_L2_012`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the full source-backed formalization draft.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the root project target covers the generated target module.

## Import Plan

```lean
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.NumberTheory.Real.Irrational
```

## Suggested Search Modules

- `Mathlib.Analysis.Complex.Trigonometric`: search facts such as `Complex.norm_exp` for norm-one complex exponentials with purely imaginary exponent.
- `Mathlib.Analysis.Calculus.ContDiff.*`: search `ContDiff` closure facts for products, scalar multiplication, and complex exponential.
- `Mathlib.Analysis.Calculus.FDeriv.*`: search derivative formulas for `Complex.exp` composed with real-linear maps and product maps.
- `Mathlib.NumberTheory.Real.Irrational`: search facts such as `Irrational.ne_zero`; the source hypothesis is retained although the local immersion proof should not need irrationality.

## Required Names

- `gamma_is_smooth_immersion`

## Source Inventory

- Source inventory entry `line-17`
- source inventory entry `line-17`
- Source inventory entry: `line-17`
- Source inventory entry: line-17
- inventory_label: line-17
- source_label: line-17
- `line-17`: source theorem `gamma_is_smooth_immersion`, formalized by Lean theorem `gamma_is_smooth_immersion`; full entry is in the statement inventory below.

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are identical. They suggest defining a torus, defining `gamma`, and proving `gamma_is_smooth_immersion`, but they use construction `sorry`s inside `gamma` and undefined/nonstandard predicates `IsSmooth` and `IsImmersion`.
- `docs/skeletons/Skeleton4.lean` repeats the same idea and is syntactically malformed by an extra `:= by sorry`.
- Adopted from the skeletons: the expected theorem name, the parameters `(α : ℝ) (hα : Irrational α)`, and the coordinate formula for `gamma`.
- Replaced from the skeletons: the torus is a concrete subset of `ℂ × ℂ`; `gamma` is an ambient-coordinate map with no construction `sorry`; the smooth-immersion claim is represented by the same-file predicate `SmoothImmersionInto`.

## Source Statement Inventory

- `line-17`: theorem `[gamma_is_smooth_immersion]` in `docs/source.tex`, lines 17--21, Lean declaration `gamma_is_smooth_immersion` in `ShadowBench/Source/Main.lean`.

### line-17

- Source label: `line-17`.
- Source title/name: `gamma_is_smooth_immersion`.
- Planned Lean declaration: `gamma_is_smooth_immersion` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem block lines 17-21, label `line-17`, title `gamma_is_smooth_immersion`.
- Source statement: Let `𝕋² = S¹ × S¹ ⊆ ℂ²` denote the torus, and let `α` be any irrational number. The map `γ : ℝ → 𝕋²` given by `γ(t) = (e^{2π i t}, e^{2π i α t})` is a smooth immersion.
- Complete source proof text: no proof is supplied in `docs/source.tex`; the source contains only the theorem statement, so no source proof text is available to attach.
- Planned Lean declarations:
  - `complexUnitCircle : Set ℂ`
  - `complexTwoTorus : Set (ℂ × ℂ)`
  - `SmoothImmersionInto : Set (ℂ × ℂ) → (ℝ → ℂ × ℂ) → Prop`
  - `gamma : ℝ → ℝ → ℂ × ℂ`
  - `gamma_is_smooth_immersion (α : ℝ) (hα : Irrational α) : SmoothImmersionInto complexTwoTorus (gamma α)`
- Dependencies:
  - Definitions: `complexUnitCircle`, `complexTwoTorus`, `SmoothImmersionInto`, `gamma`.
  - Imported notions: `Irrational`, `Set.MapsTo`, `ContDiff`, `fderiv`, `Function.Injective`, `Complex.exp`, `Real.pi`, `Complex.I`.
  - Anticipated proof facts: norm of complex exponential, smoothness of complex exponential and algebraic operations, derivative of the first coordinate of `gamma` is nonzero.
- Formal statement review:
  - The Lean theorem preserves the source quantifier order as `(α : ℝ) (hα : Irrational α)` followed by the smooth-immersion conclusion.
  - The formula is represented by the definition `gamma`, so for every `t : ℝ`, `gamma α t` is definitionally `(Complex.exp (2 * Real.pi * Complex.I * t), Complex.exp (2 * Real.pi * Complex.I * α * t))`, matching the two displayed source coordinates up to standard real-to-complex coercions and associativity of multiplication.
  - The target torus is represented by `complexTwoTorus`, the subset of `ℂ × ℂ` whose two coordinates lie in `complexUnitCircle`.
  - `SmoothImmersionInto` is the explicit bridge from the source phrase “map `ℝ → 𝕋²` is a smooth immersion” to an ambient-coordinate Lean statement: it expands to `Set.MapsTo f Set.univ s`, `ContDiff ℝ ⊤ f`, and injectivity of the Fréchet derivative at every real parameter.
- Source qualifiers:
  - Mathematical object class: `𝕋² = S¹ × S¹` as the product torus sitting inside complex two-space `ℂ²`.
  - Quantifier order: first choose a real parameter `α`, then assume the side condition that `α` is irrational.
  - Parameter domain and side condition: `α : ℝ` and `Irrational α`; no other side conditions are stated.
  - Domain: real line `ℝ`.
  - Output codomain: the torus `𝕋²`.
  - Equality/image condition: for every real `t`, the two coordinates are `e^{2π i t}` and `e^{2π i α t}`, and hence the image is asserted to lie in `𝕋²`.
  - Smoothness claim: the map is smooth/infinitely differentiable in the real sense.
  - Immersion claim: the differential is injective at every point of the source.
  - Follow-on claims: none beyond smoothness and immersion.
- Lean coverage:
  - `complexUnitCircle` and `complexTwoTorus` cover the source object `S¹ × S¹ ⊆ ℂ²`, using `ℂ × ℂ` as the concrete complex two-space representation.
  - `gamma` covers the displayed coordinate formula exactly, modulo Lean's coercions from `ℝ` to `ℂ` in products with `Complex.I`.
  - `SmoothImmersionInto complexTwoTorus (gamma α)` covers the codomain/image condition through `Set.MapsTo`, rather than by changing the type of `gamma` to a bundled subtype-valued map.
  - The same predicate covers smoothness by `ContDiff ℝ ⊤` of the ambient-coordinate map and immersion by `Function.Injective (fderiv ℝ (gamma α) t)` for every `t`.
  - The Lean theorem retains the irrationality hypothesis `hα : Irrational α`, even though the expected proof of the local smooth-immersion property does not need it.
  - Coverage is intentionally ambient-coordinate, not exact bundled-manifold coverage; the representation changes are recorded below.
- Scope changes:
  - The source writes `ℂ²`; Lean uses the product type `ℂ × ℂ` as the concrete model of complex two-space.
  - The source writes `S¹`; Lean uses the norm-one subset `complexUnitCircle = {z : ℂ | ‖z‖ = 1}`.
  - The Lean draft does not construct a bundled manifold-valued map `ℝ → 𝕋²`; instead it uses an ambient-coordinate map `ℝ → ℂ × ℂ` plus a `Set.MapsTo` condition into the torus subset.
  - The Lean draft uses an explicit ambient derivative-injectivity predicate for immersion, rather than Mathlib's chart-based `Manifold.IsImmersion` for a bundled torus manifold. This is intentional partial coverage of the submanifold-codomain wording, accepted for this draft because the bridge predicate records image, smoothness, and pointwise injective derivative clauses explicitly.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes:
  - Source proof: none supplied.
  - Proof sketch: each coordinate is the complex exponential of a real-linear function, hence smooth; the exponents are purely imaginary, so `Complex.norm_exp` gives norm one for both coordinates; the first derivative component is `2π i * exp(2π i t)`, which is never zero, so the Fréchet derivative from the one-dimensional domain is injective.
  - Prover notes: unfold `SmoothImmersionInto`, `complexTwoTorus`, and `gamma`; use norm-exponential facts for the image condition, `ContDiff` closure facts for smoothness, and derivative formulas plus nonzero constants/exponential to prove injectivity. The hypothesis `hα` may remain unused unless a chosen proof uses an irrationality lemma.

## Proof-Ready Checklist

- [ ] Source document, instructions, skeletons, manifest, and current blueprint were read.
- [ ] Local project/Mathlib search was performed before finalizing names and definitions.
- [ ] Blueprint contains a source inventory entry for `line-17` with statement-fidelity notes.
- [ ] Generated Lean file begins with imports before comments/declarations.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue may start after the independent review and handoff verification.
