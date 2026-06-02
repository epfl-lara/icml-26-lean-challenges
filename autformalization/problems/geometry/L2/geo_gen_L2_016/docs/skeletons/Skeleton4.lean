import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities

open Finset Real

theorem hyperbolic_set_convex (n : ℕ) : 
  let S := {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∏ i, x i ≥ 1}
  Convex ℝ S := by sorry
:= by sorry
