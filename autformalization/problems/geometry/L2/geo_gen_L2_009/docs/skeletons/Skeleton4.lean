import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open scoped Manifold ContDiff

theorem tangentBundleProdDiffeomorph 
  {M N : Type*} [Manifold ℝ M] [Manifold ℝ N] :
  ∃ f : TangentBundle M × TangentBundle N ≃ T (M × N), 
    ContDiff ℝ ⊤ (f) ∧ ContDiff ℝ ⊤ (f.symm) := by sorry
:= by sorry
