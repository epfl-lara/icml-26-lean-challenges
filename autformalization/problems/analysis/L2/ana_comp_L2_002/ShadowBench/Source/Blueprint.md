# Formalization Blueprint: `analysis/L2/ana_comp_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem declaration `norm_cos_eq`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the generated target module is included under the project source tree.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the Lake library target `ShadowBench` covers the generated target module.

## Import Plan

```lean
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Ring.Basic
```

## Suggested Search Modules

- `Mathlib.Analysis.Complex.Trigonometric` for `Complex.cos_add_mul_I`, `Complex.cos_eq`, real trigonometric and hyperbolic functions.
- `Mathlib.Analysis.Complex.Norm` / `Mathlib.Data.Complex.Basic` for complex norm and squared-norm identities such as `Complex.sq_norm` and `Complex.normSq`.
- Algebraic simplification around `Real.cosh_sq`, `Real.sin_sq_add_cos_sq`, and nonnegativity of square roots may be useful in the prover phase.

## Required Names

- `norm_cos_eq`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose `norm_cos_eq (z : ℂ)` with the right-hand side written using `z.im` and `z.re`. This is mathematically equivalent after choosing the canonical representation `z = z.re + i*z.im`, but it hides the source's explicit real variables `x` and `y`.
- `docs/skeletons/Skeleton4.lean` proposes `norm_cos_eq (z : ℂ) (x y : ℝ) (hz : z = x + Complex.I * y)` with the same right-hand side as the source. This candidate is adopted because it records the implicit source convention that `z = x + i y`, while preserving the source variables `z`, `x`, and `y`.

## Source Statement Inventory

### line-17

- Source title: theorem `norm_cos_eq`.
- Planned Lean declarations: `norm_cos_eq` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem block lines 17--19; proof lines 19--31.
- Source statement: `Show that $|\cos z| = \sqrt{\sinh^2 y + \cos^2 x}$.`
- Lean statement:

```lean
theorem norm_cos_eq (z : ℂ) (x y : ℝ) (hz : z = x + Complex.I * y) :
    ‖Complex.cos z‖ = Real.sqrt (Real.sinh y ^ 2 + Real.cos x ^ 2)
```

- Dependencies: direct imports listed in `## Import Plan`; likely proof facts include `Complex.cos_add_mul_I`, the norm of a complex number from real and imaginary parts, `Real.cosh_sq`, and `Real.sin_sq_add_cos_sq`.
- Formal statement review: the source theorem leaves the relationship between `z`, `x`, and `y` implicit, while the proof immediately uses `z = x + i y`. The Lean theorem makes this convention explicit through the hypothesis `hz : z = x + Complex.I * y`. The left side uses Lean's norm notation `‖Complex.cos z‖` as the complex modulus corresponding to source notation `|\cos z|`. The right side preserves the source expression `sqrt(sinh^2 y + cos^2 x)`.
- Source qualifiers:
  - Mathematical object class: `z` is a complex number and `x`, `y` are real coordinates.
  - Quantifier order: `z`, then `x`, then `y`, followed by the representation hypothesis.
  - Parameter domain: `z : ℂ`, `x y : ℝ`.
  - Output codomain: both sides are real-valued nonnegative magnitudes.
  - Equality condition: equality of the complex modulus of `cos z` with the stated real square root.
  - Side condition: the implicit source representation `z = x + i y`, made explicit as `hz`.
  - Follow-on claims: none.
- Lean coverage: full coverage of the source theorem under the standard interpretation that `z = x + i y`; the representation bridge is included as the explicit hypothesis `hz` rather than silently replacing `x` and `y` by `z.re` and `z.im`.
- Scope changes: the Lean statement adds the explicit hypothesis `hz` because the LaTeX statement has free variables but the source proof relies on the representation `z = x + i y`. No mathematical conclusion is changed beyond making this implicit assumption explicit.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
\[
\begin{aligned}
|\cos z| &= |\cos x \cosh y - i \sin x \sinh y| \\
&= \sqrt{\cos^2 x \cosh^2 y + \sin^2 x \sinh^2 y} \\
&= \sqrt{\cos^2 x (1 + \sinh^2 y) + \sin^2 x \sinh^2 y} \\
&= \sqrt{\cos^2 x + \sinh^2 y (\cos^2 x + \sin^2 x)} \\
&= \sqrt{\cos^2 x + \sinh^2 y}
\end{aligned}
\]
```

- Source proof / prover notes: rewrite `z` using `hz`, then apply the complex cosine formula for `x + i*y`: `cos (x + i*y) = cos x * cosh y - i * sin x * sinh y`. Compute the squared norm of this complex number as `cos^2 x * cosh^2 y + sin^2 x * sinh^2 y`; use `cosh^2 y = 1 + sinh^2 y` and `cos^2 x + sin^2 x = 1` to simplify to `sinh^2 y + cos^2 x`, then take the nonnegative square root.

## Formalization Rules

```text
/-
Formalize in Lean the Theorem (norm_cos_eq) from Text.

The theorem must be named `norm_cos_eq`.
   Matched text (candidate 0, theorem, label=norm_cos_eq): \begin{theorem}[norm_cos_eq] Show that $|\cos z| = \sqrt{\sinh^2 y + \cos^2 x}$.
                                                           \end{theorem}
-/
```
