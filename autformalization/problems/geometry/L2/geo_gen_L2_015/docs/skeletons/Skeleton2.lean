import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.Cone.Basic

open InnerProductSpace

theorem separatingHyperplanes_is_pointed (n : ℕ) (C D : Set (Fin n → ℝ)) (h_disjoint : Disjoint C D) :
  let S := {p : (Fin n → ℝ) × ℝ | (∀ x ∈ C, ∑ i, p.1 i * x i ≤ p.2) ∧ (∀ x ∈ D, ∑ i, p.1 i * x i ≥ p.2)}
  Convex ℝ S ∧ ∀ (t : ℝ) (p : (Fin n → ℝ) × ℝ), t ≥ 0 → p ∈ S → (fun i => t * p.1 i, t * p.2) ∈ S ∧ (0, 0) ∈ S := by sorry
