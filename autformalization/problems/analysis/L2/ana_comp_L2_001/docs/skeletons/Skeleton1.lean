import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology

theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable 
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  (f : ℂ → E) 
  (z_star w_star : ℂ) :
  let R : Set ℂ := {z | z.re ∈ Set.Icc z_star.re w_star.re ∧ z.im ∈ Set.Icc z_star.im w_star.im}
  -- Condition 1: f is continuous on the closed rectangle R
  ContinuousOn f R →
  -- Condition 2: There exists a countable set S such that f is real differentiable on int(R) \ S
  (∃ S : Set ℂ, Set.Countable S ∧ 
    ∀ z ∈ interior R \ S, DifferentiableAt ℝ f z) →
  -- Condition 3: The function (z ↦ i * ∂f/∂x(z) - ∂f/∂y(z)) is integrable on R
  MeasureTheory.IntegrableOn (fun z => 
    Complex.I • (fderiv ℝ f z 1) - fderiv ℝ f z Complex.I) R →
  -- The main equality
  (∫ x in z_star.re..w_star.re, f (x + Complex.I * z_star.im)) -
  (∫ x in z_star.re..w_star.re, f (x + Complex.I * w_star.im)) +
  Complex.I • (∫ y in z_star.im..w_star.im, f (w_star.re + Complex.I * y)) -
  Complex.I • (∫ y in z_star.im..w_star.im, f (z_star.re + Complex.I * y)) =
  ∫ x in z_star.re..w_star.re, ∫ y in z_star.im..w_star.im,
    (Complex.I • (fderiv ℝ f (x + Complex.I * y) 1) - 
     fderiv ℝ f (x + Complex.I * y) Complex.I) := by sorry
