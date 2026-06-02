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
open Complex

def rect (z w : ℂ) : Set ℂ := {ζ | ζ.re ∈ [[z.re, w.re]] ∧ ζ.im ∈ [[z.im, w.im]]}

theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ)
    (hf : ContinuousOn f (rect z w))
    (S : Set ℂ) (hS : S.Countable)
    (hd : ∀ ζ ∈ interior (rect z w) \ S, HasFDerivAt f (f' ζ) ζ)
    (hfi : IntegrableOn (fun ζ ↦ I • f' ζ 1 - f' ζ I) (rect z w)) :
    (∫ x in z.re..w.re, f (x + z.im * I)) -
    (∫ x in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y in z.im..w.im, f (w.re + y * I)) -
    I • (∫ y in z.im..w.im, f (z.re + y * I)) =
    ∫ x in z.re..w.re, ∫ y in z.im..w.im,
      I • f' (x + y * I) 1 - f' (x + y * I) I := by sorry
