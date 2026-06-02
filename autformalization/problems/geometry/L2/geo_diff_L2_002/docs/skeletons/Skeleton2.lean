import Mathlib.Geometry.Manifold.MFDeriv.Tangent

open scoped Manifold Topology
open Set

/--
A curve Γ is an integral curve of a vector field v at a point t₀ if and only if
there exists an open neighborhood U of t₀ such that Γ is an integral curve of v on U.
-/
theorem isMIntegralCurveAt_iff' (M : Type*) [Manifold ℝ M] (v : M → T M) 
  (Γ : ℝ → M) (t₀ : ℝ) : 
  (DifferentiableAt ℝ Γ t₀ ∧ deriv Γ t₀ = v (Γ t₀)) ↔ 
  ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ ∀ t ∈ U, DifferentiableAt ℝ Γ t ∧ deriv Γ t = v (Γ t) := by sorry
