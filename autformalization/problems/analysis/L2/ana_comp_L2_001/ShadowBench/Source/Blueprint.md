# Formalization Blueprint: `analysis/L2/ana_comp_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one source theorem declaration, with the mandated name `integral_boundary_rect_of_hasFDerivAt_real_off_countable` and a `by sorry` proof placeholder for the later `/prove` workflow.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the target module is covered by the root library.
- `ShadowBench.lean`: imports `ShadowBench.Source` so project-level verification covers the generated target module.

No split into auxiliary files is planned: the source contains a single theorem, and one generated Lean file preserves the source context clearly.

## Import Plan

Direct Lean imports for `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.CauchyIntegral
```

Rationale: `Mathlib.Analysis.Complex.CauchyIntegral` is the direct Mathlib module containing the matching Green theorem on complex rectangles, the rectangle notation `×ℂ`, and the interval-integral infrastructure used in the statement. `Mathlib.LinearAlgebra.Complex.FiniteDimensional` is imported directly so the project-local Lean options can synthesize the standard Lebesgue `MeasureSpace ℂ` instance used by `IntegrableOn`. These direct imports replace the initial broad scaffold import list from `docs/instructions.md`.

## Suggested Search Modules

These are search/proof hints only, not direct imports in the Lean draft unless a later proof run proves they are needed:

- `Mathlib.MeasureTheory.Integral.DivergenceTheorem`
- `Mathlib.Analysis.Complex.ReImTopology`
- `Mathlib.MeasureTheory.Integral.CircleIntegral`
- `Mathlib.Analysis.Analytic.Uniqueness`

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose a statement using `fderiv ℝ f` and only a real normed-space structure. They are useful hints for the boundary and area integral shape, but the complex scalar term `Complex.I • ...` is not meaningful for a merely real normed vector space.
- `docs/skeletons/Skeleton4.lean` is the adopted shape. It introduces an explicit real Fréchet derivative field `f' : ℂ → ℂ →L[ℝ] E`, assumes `HasFDerivAt f (f' ζ) ζ` off a countable set, and uses `I • f' ζ 1 - f' ζ I` for the partial-derivative expression. The final draft modifies Skeleton4 by using an existential countable exceptional set to match the source quantifier.

## Required Names

- `integral_boundary_rect_of_hasFDerivAt_real_off_countable`

## Source Statement Inventory

### line-17

- Source title: theorem `integral_boundary_rect_of_hasFDerivAt_real_off_countable`.
- Source locator: `docs/source.tex`, theorem block lines 17-69; proof lines 69-109.
- Planned Lean declarations: `integral_boundary_rect_of_hasFDerivAt_real_off_countable` in `ShadowBench/Source/Main.lean`.
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean`, adjusted to keep the source's existential countable exceptional set.
- Dependencies: `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable` from `Mathlib.Analysis.Complex.CauchyIntegral`; rectangle notation `[[z.re, w.re]] ×ℂ [[z.im, w.im]]`; the open rectangle `Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)`; interval integrals over the boundary and iterated interval integrals over the rectangle.
- Formal statement review: The Lean theorem preserves the source hypotheses and conclusion, with two explicit bridges. First, the value space is strengthened to a complex normed space so multiplication by `i` is meaningful. Second, the partial derivative notation is represented by an explicit real Fréchet derivative map. The countable exceptional set remains existential, matching the source quantifier.
- Source qualifiers:
  - Mathematical object class: source says `E` is a real normed vector space and `f : ℂ → E`; the displayed formula also multiplies `E`-valued terms by `i`.
  - Quantifier order: choose the value space, then `f`, corners `z*`, `w*`, assumptions on continuity, an existential countable exceptional set, differentiability off that set, integrability, and finally the boundary/area identity.
  - Parameter domain: `f` is defined on all of `ℂ`; the assumptions restrict to the closed rectangle and its interior.
  - Output codomain: `E`-valued Bochner/interval integrals.
  - Equality condition: oriented bottom edge minus top edge plus `i` times right edge minus `i` times left edge equals the iterated integral over real coordinates.
  - Side conditions: continuity on the closed rectangle, real differentiability off a countable subset of the open rectangle, and integrability of `i ∂f/∂x - ∂f/∂y` on the closed rectangle.
  - Follow-on claims: no corollaries or additional source claims are attached.
- Lean coverage:
  - The closed rectangle is represented by Mathlib's unordered complex rectangle `[[z.re, w.re]] ×ℂ [[z.im, w.im]]`, covering the source closed rectangle even when endpoint order is not assumed.
  - The open rectangle/interior is represented by `Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)`, the Mathlib interior form for the unordered rectangle.
  - The exceptional set is existential in the Lean theorem: `∃ S : Set ℂ, S.Countable ∧ ...`, matching the source's existence statement.
  - Real differentiability with partial derivatives is represented by `HasFDerivAt f (f' ζ) ζ`, where `f' ζ 1` is the derivative in the real direction and `f' ζ Complex.I` is the derivative in the imaginary direction.
  - Integrability is represented by `IntegrableOn (fun ζ : ℂ => Complex.I • f' ζ 1 - f' ζ Complex.I) ...`.
  - The boundary and area equality uses Mathlib interval-integral notation and exactly the four oriented boundary terms from the source, with `Complex.I •` for multiplication by `i` on the value space.
  - Coverage is exact after the recorded clarification that the value space must carry a complex scalar action; the original displayed formula is ill-typed if the value space has only real scalar multiplication.
- Scope changes:
  - The source calls `E` a real normed vector space, but the terms `i` times an `E`-valued derivative/integral require a complex scalar multiplication. The Lean statement therefore assumes `[NormedSpace ℂ E]`, which supplies the needed complex scalar action and the underlying real differentiability notion used by `HasFDerivAt`.
  - The derivative data is made explicit as `f' : ℂ → ℂ →L[ℝ] E` so that the partial derivatives appearing in the integrability condition and right-hand side have a stable Lean representation. This records the source's unnamed partial derivatives as applications of a real Fréchet derivative.
  - The rectangle uses Mathlib unordered intervals `[[a,b]]` and min/max open intervals. This is a representation bridge for the source's closed rectangle notation and avoids adding an endpoint-order assumption.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Source proof lines 69-109 identify `ℂ` with `ℝ × ℝ` via `(x,y) ↦ x + i y`, set `F(x,y) = f(x+iy)`, pull the countable exceptional set back to the real rectangle, use the chain rule to identify the two partial derivatives, compute the Green expression, and apply Green's theorem on rectangles for functions differentiable outside a countable set. In Lean, `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable` already implements this proof by transporting through `ℝ × ℝ ≃L[ℝ] ℂ` and applying `integral2_divergence_prod_of_hasFDerivAt_off_countable`. For the drafted existential version, destruct `hdiff` as `rcases hdiff with ⟨S, hS_count, hS_diff⟩` and apply the Mathlib theorem to `f`, `f'`, `z`, `w`, `S`, `hS_count`, `hcont`, `hS_diff`, and `hint`.

  Complete source proof text:

  ```text
  We identify $\mathbb{C}$ with $\mathbb{R}^2$ via the linear isomorphism
  \[
  (x,y) \longmapsto x + i y.
  \]
  Define $F : \mathbb{R}^2 \to E$ by $F(x,y) := f(x+iy)$.

  By continuity of $f$ on $R$, the function $F$ is continuous on
  $[\Re(z^{\ast}),\Re(w^{\ast})] \times [\Im(z^{\ast}),\Im(w^{\ast})]$.
  The exceptional set $S$ pulls back to a countable subset of $\mathbb{R}^2$.

  For every $(x,y)$ in the interior of the rectangle outside this exceptional set,
  the chain rule shows that $F$ is differentiable with
  \[
  \frac{\partial F}{\partial x}(x,y)
  =
  \frac{\partial f}{\partial x}(x+iy),
  \qquad
  \frac{\partial F}{\partial y}(x,y)
  =
  \frac{\partial f}{\partial y}(x+iy).
  \]

  A direct computation shows that the Green-type expression becomes
  \[
  -\,i\,\frac{\partial F}{\partial x}(x,y)
  +
  \frac{\partial F}{\partial y}(x,y)
  =
  -\left(
  i\,\frac{\partial f}{\partial x}(x+iy)
  -
  \frac{\partial f}{\partial y}(x+iy)
  \right).
  \]

  Applying Green's theorem on rectangles (valid for functions differentiable
  outside a countable set) yields the stated identity.
  ```

## Formalization Rules

```text
open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology

Formalize in Lean the Theorem (integral_boundary_rect_of_hasFDerivAt_real_off_countable) from Text.
The theorem must be named `integral_boundary_rect_of_hasFDerivAt_real_off_countable`.
```
