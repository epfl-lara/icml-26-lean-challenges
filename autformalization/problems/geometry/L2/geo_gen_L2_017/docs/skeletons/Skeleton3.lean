import Mathlib.Analysis.InnerProductSpace.PiL2

open Set

theorem convex_partialSum (m n : ℕ) (S₁ S₂ : Set ((Fin m → ℝ) × (Fin n → ℝ))) 
  (h₁ : Convex ℝ S₁) (h₂ : Convex ℝ S₂) :
  let S := {p : (Fin m → ℝ) × (Fin n → ℝ) | ∃ x : Fin m → ℝ, ∃ y₁ y₂ : Fin n → ℝ,
            (x, y₁) ∈ S₁ ∧ (x, y₂) ∈ S₂ ∧ p = (x, y₁ + y₂)}
  Convex ℝ S := by sorry
