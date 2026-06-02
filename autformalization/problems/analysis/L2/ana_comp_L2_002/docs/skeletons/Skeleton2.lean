import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Ring.Basic

theorem norm_cos_eq (z : ℂ) : 
  Complex.abs (Complex.cos z) = Real.sqrt (Real.sinh z.im ^ 2 + Real.cos z.re ^ 2) := by sorry
