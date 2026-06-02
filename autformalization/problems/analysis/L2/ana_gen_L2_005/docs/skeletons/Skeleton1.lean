import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory

theorem ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv (a b : ℝ) (hab : a < b) (F : ℝ → ℝ) 
  (hcont : ContinuousOn F (Set.Icc a b))
  (hdiff : DifferentiableOn ℝ F (Set.Ioo a b))
  (hintegr : IntervalIntegrable (deriv F) volume a b) :
  AbsolutelyContinuousOn F (Set.Icc a b) ∧ 
  F b - F a = ∫ x in a..b, deriv F x := by sorry
