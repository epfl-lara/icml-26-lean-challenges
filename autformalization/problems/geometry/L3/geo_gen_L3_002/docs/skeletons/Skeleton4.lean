import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Sheaf.Basic

open scoped Manifold
open Real

theorem ballRnDiffeomorph (n : ℕ) : 
  let F : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ < 1} → EuclideanSpace ℝ (Fin n) := 
    fun x => x.val / Real.sqrt (1 - ‖x.val‖^2)
  let G : EuclideanSpace ℝ (Fin n) → {x : EuclideanSpace ℝ (Fin n) // ‖x‖ < 1} := 
    fun y => ⟨y / Real.sqrt (1 + ‖y‖^2), by sorry⟩
  ContDiff ℝ ⊤ F ∧ 
  ContDiff ℝ ⊤ (fun y => (G y).val) ∧
  (∀ x, ‖x.val‖ < 1 → F x = y → G y = x) ∧
  (∀ y, G y = x → F x = y) ∧
  ∃ (h : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ < 1} ≃ᵈ EuclideanSpace ℝ (Fin n)), 
    (∀ x, h x = F x) ∧ (∀ y, h.symm y = G y) := by sorry
:= by sorry
