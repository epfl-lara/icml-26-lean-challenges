import Mathlib

open Set MeasureTheory

theorem intervalIntegrable_g_and_integral_g_eq_integral 
    {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : IntervalIntegrable f volume 0 b) :
    let g := fun x => if 0 < x ∧ x ≤ b then ∫ t in x..b, f t / t else 0
    IntervalIntegrable g volume 0 b ∧ ∫ x in 0..b, g x = ∫ t in 0..b, f t := by sorry
