import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Ring.Basic

theorem norm_cos_eq (z : ℂ) (x y : ℝ) (hz : z = x + Complex.I * y) :
    ‖Complex.cos z‖ = Real.sqrt (Real.sinh y ^ 2 + Real.cos x ^ 2) := by sorry
