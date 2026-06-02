import Mathlib

open Set MeasureTheory

theorem intervalIntegrable_g_and_integral_g_eq_integral (b : ℝ) (f : ℝ → ℝ) 
  (hb : 0 < b)
  (hf : IntervalIntegrable f volume 0 b) :
  let g := fun x => if x = 0 then 0 else ∫ t in x..b, f t / t
  IntervalIntegrable g volume 0 b ∧ 
  ∫ x in (0)..(b), g x = ∫ t in (0)..(b), f t := by sorry
