import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory

theorem ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} {F : ℝ → E} {F' : ℝ → E}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hF' : ∀ x ∈ Ioo a b, HasDerivAt F (F' x) x) (hF'int : IntervalIntegrable F' volume a b) :
    AbsolutelyContinuousOn F (Icc a b) ∧ F b - F a = ∫ x in a..b, F' x := by sorry
