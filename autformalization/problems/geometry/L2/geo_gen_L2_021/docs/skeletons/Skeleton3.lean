import Mathlib

open scoped Manifold ContDiff

/-- If γ is a nonconstant periodic global integral curve of a vector field X on a smooth manifold M,
then there exists a unique positive number T (the fundamental period) such that γ(t) = γ(t') if and only if
t - t' = kT for some integer k. -/
theorem global_integralCurve_unique_fundamental_period (M : Type*) [SmoothManifold ℝ M] 
    (X : VectorField ℝ M) 
    (γ : ℝ → M) 
    (h_global : IsGlobalIntegralCurve X γ) -- γ is a global integral curve of X
    (h_periodic : ∃ T > 0, ∀ t : ℝ, γ (t + T) = γ t)
    (h_nonconstant : ¬ ∃ x : M, ∀ t : ℝ, γ t = x) :
    ∃! T : ℝ, T > 0 ∧ 
      (∀ t t' : ℝ, γ t = γ t' ↔ ∃ k : ℤ, t - t' = k * T) := by sorry
