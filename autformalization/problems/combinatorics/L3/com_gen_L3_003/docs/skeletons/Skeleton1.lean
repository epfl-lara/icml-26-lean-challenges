import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet

open Set

variable {α : Type*} [DecidableEq α] (M : Matroid α)

theorem contract_closure_eq_contract_delete (C : Set α) (hC : C ⊆ M.groundSet) :
  M / (M.closure C) = (M / C) \ (M.closure C \ C) := by sorry

theorem contract_closure_eq (C X : Set α) :
  (M / C).closure X = M.closure (X ∪ C) \ C := by sorry

theorem contract_spanning_iff (C : Set α) (hC : C ⊆ M.groundSet) (X : Set α) :
  (M / C).IsSpanning X ↔ (M.IsSpanning (X ∪ C) ∧ Disjoint X C) := by sorry
