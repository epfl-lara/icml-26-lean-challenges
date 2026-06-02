import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Manifold Set Topology

-- Definition of gamma
def gamma : ℝ → ℝ × ℝ := fun t => (t^3, 0)

-- γ is smooth
theorem gamma_smooth : ContDiff ℝ ⊤ gamma := by sorry

-- γ is a topological embedding
theorem gamma_is_embedding : IsTopologicalEmbedding gamma := by sorry

-- The manifold derivative of γ at 0 is zero
theorem gamma_mfderiv_zero : fderiv ℝ gamma 0 = 0 := by sorry

-- γ is not a smooth embedding
theorem gamma_not_smooth_embedding : ¬IsSmoothEmbedding gamma := by sorry
