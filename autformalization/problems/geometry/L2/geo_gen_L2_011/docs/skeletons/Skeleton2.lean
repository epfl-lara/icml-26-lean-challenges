import Mathlib

set_option maxHeartbeats 0

open scoped Manifold
open Set ContDiff

theorem isInteriorPoint_of_bijective_mfderiv (M N : Type*) [Manifold ℝ M] [ManifoldWithBoundary ℝ N] 
  (F : M → N) (hF : ContDiff ℝ ⊤ F) 
  (p : M) (hp : Function.Bijective (fderiv ℝ F p)) : 
  F p ∈ interior (Set.univ : Set N) := by sorry
