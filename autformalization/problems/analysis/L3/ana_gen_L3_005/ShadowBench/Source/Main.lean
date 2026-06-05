import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open MeasureTheory Real Complex Set NNReal Filter Topology

/-!
ShadowBench formalization for `analysis/L3/ana_gen_L3_005` from `docs/source.tex`.
-/

/--
Source proof: the source first applies the Riemann-Lebesgue lemma to get decay of the
real and imaginary trigonometric integrals.  For `f = χ_E`, it bounds the shifted
oscillatory integral of `cos (2 n x + 2 u_n)` by the decaying sine and cosine integrals,
then rewrites `cos^2 (n x + u_n)` as `(1 + cos (2 (n x + u_n))) / 2`, giving the limit
`m(E) / 2`.

Prover notes: use `Mathlib.Analysis.Fourier.RiemannLebesgueLemma` for the first conjunct;
for the second conjunct, specialize to an indicator of `E`, use `Real.cos_add`/double-angle
identities and the bounds on `sin` and `cos`, convert the constant set integral to
`(volume E).toReal`, and finish by Tendsto arithmetic.
-/
theorem integral_cos_sq_tendsto_half_measure :
  (∀ f : ℝ → ℂ, IntervalIntegrable f volume 0 (2 * Real.pi) →
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ |n| →
      ‖∫ x in (0)..(2 * Real.pi), f x * Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖ < ε) ∧
  (∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc 0 (2 * Real.pi) →
    ∀ u : ℕ → ℝ,
      Filter.Tendsto (fun n : ℕ => ∫ x in E, (Real.cos ((n : ℝ) * x + u n)) ^ 2)
        Filter.atTop (𝓝 ((volume E).toReal / 2))) := by
  sorry
