import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.CauchyIntegral

open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology

/--
Source theorem `line-17` (`docs/source.tex`,
`integral_boundary_rect_of_hasFDerivAt_real_off_countable`).

Source proof: identify `ℂ` with `ℝ × ℝ` by `(x, y) ↦ x + y * I`, pull the
countable exceptional set back to the real rectangle, and apply Green's theorem
for rectangles to the function `F (x, y) = f (x + y * I)`.

Prover notes: this is the existential-source version of
`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`.  Destructure
`hdiff` to obtain the exceptional set and apply the Mathlib theorem with the
continuity and integrability hypotheses.
-/
theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ)
    (hcont : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hdiff : ∃ S : Set ℂ, S.Countable ∧
      ∀ ζ ∈ ((Ioo (min z.re w.re) (max z.re w.re) ×ℂ
          Ioo (min z.im w.im) (max z.im w.im)) \ S),
        HasFDerivAt f (f' ζ) ζ)
    (hint : IntegrableOn (fun ζ : ℂ => Complex.I • f' ζ 1 - f' ζ Complex.I)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im,
        Complex.I • f' (x + y * Complex.I) 1 - f' (x + y * Complex.I) Complex.I := by
  rcases hdiff with ⟨S, hS_count, hS_diff⟩
  exact Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable f f' z w S hS_count
    hcont hS_diff hint
