import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet

open Set

def contract {α : Type*} (M : Matroid α) (C : Set α) : Matroid α := sorry

theorem contract_ground {α : Type*} (M : Matroid α) (C : Set α) :
  (contract M C).groundSet = M.groundSet \ C := by sorry

theorem dual_contract {α : Type*} (M : Matroid α) (X : Set α) :
  (contract M X).dual = M.dual.delete X ∧ (M.delete X).dual = contract M X := by sorry

theorem Coindep.coindep_contract_of_disjoint {α : Type*} (M : Matroid α) (C₁ C₂ : Set α) :
  contract (contract M C₁) C₂ = contract M (C₁ ∪ C₂) := by sorry

theorem contract_empty {α : Type*} (M : Matroid α) :
  contract M ∅ = M := by sorry

theorem contract_eq_contract_iff {α : Type*} (M : Matroid α) (C₁ C₂ : Set α) :
  contract M C₁ = contract M C₂ ↔ C₁ ∩ M.groundSet = C₂ ∩ M.groundSet := by sorry

theorem coindep_contract_iff {α : Type*} (M : Matroid α) (C X : Set α) :
  IsCoindependent (contract M C) X ↔
  IsCoindependent M X ∧ X ∩ C = ∅ := by sorry

theorem contract_isCocircuit_iff {α : Type*} (M : Matroid α) (C K : Set α) :
  IsCocircuit (contract M C) K ↔
  IsCocircuit M K ∧ K ∩ C = ∅ := by sorry

theorem Indep.contract_indep_iff {α : Type*} (M : Matroid α) (C I : Set α) :
  IsIndependent (contract M C) I ↔ IsIndependent M I ∧ I ∩ C = ∅ := by sorry

theorem Indep.contract_isBase_iff {α : Type*} (M : Matroid α) (I B : Set α) :
  IsBase (contract M I) B ↔ IsBase M (B ∪ I) ∧ B ∩ I = ∅ := by sorry

theorem IsNonloop.contractElem_indep_iff {α : Type*} (M : Matroid α) (e : α) (I : Set α)
    (he : IsNonloop M e) :
  IsIndependent (contract M {e}) I ↔ IsIndependent M (I ∪ {e}) := by sorry

theorem IsBasis.contract_eq_contract_delete {α : Type*} (M : Matroid α) (C B I : Set α) :
  IsBasis M B → IsBasis (contract M C) I → I = B \ C := by sorry
