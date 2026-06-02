import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Defs

open Set
open scoped ContDiff Manifold

theorem smooth_function_separating_closed_sets (M : Type*) [Manifold ℝ M] (A B : Set M) 
  (hA : IsClosed A) (hB : IsClosed B) (h_disjoint : Disjoint A B) :
  ∃ f : M → ℝ, ContDiff ℝ ⊤ f ∧ 
    (∀ x : M, 0 ≤ f x ∧ f x ≤ 1) ∧
    (f ⁻¹' {0} = A) ∧
    (f ⁻¹' {1} = B) := by sorry
:= by sorry
