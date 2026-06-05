# Formalization Blueprint: `analysis/L2/ana_gen_L2_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main` so the generated target is covered by the root `ShadowBench` library build.
- `ShadowBench/Source/Main.lean` contains the single source-backed theorem declaration `saddle_sections_hasFDerivAt_eq_zero`.
- No file split is useful for this one-theorem source document.

## Import Plan

```lean
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
```

## Suggested Search Modules

- `Mathlib.Analysis.Calculus.LocalExtr.Basic`: Fermat-type lemmas such as `IsLocalMin.hasFDerivAt_eq_zero` and `IsLocalMax.hasFDerivAt_eq_zero`.
- Candidate statement hints came from `docs/skeletons/Skeleton4.lean`; `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` were rejected because they conclude the full derivative of `f` on the product from only section differentiability and also encode the saddle inequality incorrectly.

## Required Names

- `saddle_sections_hasFDerivAt_eq_zero`

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source title: theorem `saddle_sections_hasFDerivAt_eq_zero`.
- Planned Lean declaration: `saddle_sections_hasFDerivAt_eq_zero`
- Source locator: `line-17` (`docs/source.tex`, theorem lines 17-23; proof lines 23-43).
- Skeleton candidate used: shaped by `docs/skeletons/Skeleton4.lean`, with the domain specialized back to the source finite-dimensional spaces `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`. `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` were rejected because their saddle inequality fixes the wrong coordinate in the first inequality and they conclude a full product derivative from only section differentiability.
- Dependencies: `HasFDerivAt`; `ContinuousLinearMap` zero; local extremum/Fermat lemmas `IsLocalMin.hasFDerivAt_eq_zero` and `IsLocalMax.hasFDerivAt_eq_zero` from `Mathlib.Analysis.Calculus.LocalExtr.Basic`.
- Source qualifiers:
  - Object class: a scalar-valued function on a product of finite-dimensional real Euclidean spaces, written in the source as `f : ℝ^n × ℝ^m → ℝ`.
  - Lean domain representation: `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)` is the standard Lean model of `ℝ^n × ℝ^m`; this is a representation choice, not a mathematical weakening.
  - Quantifier order: finite dimensions `n m`, function `f`, saddle point coordinates `x̃ z̃`, the global saddle inequality for all `x z`, then differentiability data for the two coordinate sections.
  - Parameter domains: `x̃ x : EuclideanSpace ℝ (Fin n)` and `z̃ z : EuclideanSpace ℝ (Fin m)`.
  - Output codomain: `ℝ`.
  - Inequality/equality condition: the displayed saddle chain is represented as the conjunction `f (x̃, z) ≤ f (x̃, z̃)` and `f (x̃, z̃) ≤ f (x, z̃)` for every `x z`; there is no separate image condition in the source.
  - Side conditions: the `x`-section `fun x => f (x, z̃)` is differentiable at `x̃`, and the `z`-section `fun z => f (x̃, z)` is differentiable at `z̃`.
  - Follow-on claim/conclusion: the source writes `∇ f(x̃, z̃) = 0`; the proof immediately spells this out as the two partial/section gradients `∇ₓ f(x̃, z̃) = 0` and `∇_z f(x̃, z̃) = 0`.
- Formal statement review:
  - The Lean theorem uses named Fréchet derivatives `fx'` and `fz'` for the two sections via `HasFDerivAt`; this is a precise form of the source differentiability hypotheses and lets the theorem state that the actual section derivative maps vanish.
  - The saddle condition in Lean matches the source quantification over all `x` and `z` and uses the correct fixed coordinates: the first inequality varies `z` at `x̃`, and the second varies `x` at `z̃`.
  - The Lean conclusion `fx' = 0 ∧ fz' = 0` formalizes the proof-supported partial-gradient/section-derivative reading of the source conclusion.
  - The theorem deliberately does not assert `fderiv ℝ f (x̃, z̃) = 0` for the full product map, because the source hypotheses only assume separate differentiability and do not include full differentiability of `f` at `(x̃, z̃)`. If the intended source meaning is a full Fréchet gradient, a separate stronger theorem would need an additional full-differentiability hypothesis and a bridge from product derivative to the two section derivatives.
- Lean coverage: reviewed partial-gradient coverage of the source theorem. It covers the finite-dimensional Euclidean object class, parameter domains, scalar codomain, global saddle inequalities, section differentiability assumptions, and the two component vanishing conclusions derived in the source proof; it is not claimed as exact coverage of a full product-gradient statement.
- Scope changes: the source notation `∇ f(x̃, z̃) = 0` is interpreted as vanishing of both section/partial derivatives. Full Fréchet derivative vanishing for `f : (ℝ^n × ℝ^m) → ℝ` is intentionally omitted because it is not justified by the stated hypotheses. No other quantifier, domain, codomain, or saddle-inequality change is made.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  > First, consider the function of `x` defined by `g(x) = f(x, z̃)`, where `z̃` is fixed. From the second inequality of the saddle-point property, `g(x̃) = f(x̃, z̃) ≤ f(x, z̃) = g(x)` for all `x`. This implies that `x̃` is a global minimizer of `g`. Since `g` is differentiable at `x̃`, a necessary condition for a minimizer is that its gradient must vanish. Therefore `∇ₓ f(x̃, z̃) = ∇g(x̃) = 0`.
  > Next, consider the function of `z` defined by `h(z) = f(x̃, z)`, where `x̃` is fixed. From the first inequality of the saddle-point property, `h(z) = f(x̃, z) ≤ f(x̃, z̃) = h(z̃)` for all `z`. This implies that `z̃` is a global maximizer of `h`. Since `h` is differentiable at `z̃`, its gradient at the maximizer must be zero: `∇_z f(x̃, z̃) = ∇h(z̃) = 0`.
- Prover notes:
  - Define `g := fun x => f (x, z̃)` and derive a global minimum at `x̃` from `h_saddle x z̃`. Convert this to an `IsLocalMin` fact, then apply `IsLocalMin.hasFDerivAt_eq_zero hf_x`.
  - Define `h := fun z => f (x̃, z)` and derive a global maximum at `z̃` from `h_saddle x̃ z`. Convert this to an `IsLocalMax` fact, then apply `IsLocalMax.hasFDerivAt_eq_zero hf_z`.
  - The first and second projections of `h_saddle x z` are used separately; no differentiability of the full product map is available.
