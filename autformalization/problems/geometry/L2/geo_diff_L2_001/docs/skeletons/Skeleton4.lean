import Mathlib.Geometry.Manifold.MFDeriv.Tangent

open scoped Manifold Topology
open Set

theorem isMIntegralCurveAt_iff' (M : Type*) [Manifold ℝ M] (v : M → TangentBundle ℝ M) 
  (Γ : ℝ → M) (t₀ : ℝ) : 
  (∀ t, HasDerivAt Γ (v (Γ t)) t) ↔ 
  ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ ∀ t ∈ U, HasDerivAt Γ (v (Γ t)) t := by sorry
:= by sorry
