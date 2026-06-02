import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet

open Set

/-- The contraction of C from M, denoted M / C, is defined as (M* \ C)* -/
def contract {α : Type*} (M : Matroid α) (C : Set α) : Matroid α := sorry

/-- The ground set of M/C equals the ground set of M minus C -/
theorem contract_ground {α : Type*} (M : Matroid α) (C : Set α) :
  (contract M C).groundSet = M.groundSet \ C := by sorry

/-- The dual of M/C equals M*\C, and the dual of M\C equals M/C -/
theorem dual_contract {α : Type*} (M : Matroid α) (X : Set α) :
  (contract M X).dual = M.dual.delete X ∧ 
  (M.delete X).dual = contract M X := by sorry

/-- Contraction of disjoint sets can be combined as M/C₁/C₂ = M/(C₁ ∪ C₂) -/
theorem Coindep_coindep_contract_of_disjoint {α : Type*} (M : Matroid α) (C₁ C₂ : Set α) :
  contract (contract M C₁) C₂ = contract M (C₁ ∪ C₂) ∧
  contract (contract M C₁) C₂ = contract (contract M C₂) C₁ := by sorry

/-- Contraction of the empty set leaves the matroid unchanged -/
theorem contract_empty {α : Type*} (M : Matroid α) :
  contract M ∅ = M := by sorry

/-- Two contractions are equal if and only if their respective sets intersect the ground set the same way -/
theorem contract_eq_contract_iff {α : Type*} (M : Matroid α) (C₁ C₂ : Set α) :
  contract M C₁ = contract M C₂ ↔ C₁ ∩ M.groundSet = C₂ ∩ M.groundSet := by sorry

/-- A set X is coindependent in M/C if and only if X is coindependent in M and X ∩ C = ∅ -/
theorem coindep_contract_iff {α : Type*} (M : Matroid α) (C X : Set α) :
  IsCoindependent (contract M C) X ↔ 
  IsCoindependent M X ∧ X ∩ C = ∅ := by sorry

/-- A set K is a cocircuit of M/C if and only if K is a cocircuit of M and K ∩ C = ∅ -/
theorem contract_isCocircuit_iff {α : Type*} (M : Matroid α) (C K : Set α) :
  IsCocircuit (contract M C) K ↔ 
  IsCocircuit M K ∧ K ∩ C = ∅ := by sorry

/-- Let I ⊆ E(M) be independent. A set B is a basis of M/I if and only if B ∪ I is a basis of M and B ∩ I = ∅ -/
theorem Indep_contract_isBase_iff {α : Type*} (M : Matroid α) (I B : Set α) (hI : IsIndependent M I) :
  IsBasis (contract M I) B ↔ 
  IsBasis M (B ∪ I) ∧ B ∩ I = ∅ := by sorry

/-- Let I ⊆ E(M) be independent. For any set J, J is independent in M/I iff J ∩ I = ∅ and J ∪ I is independent in M -/
theorem Indep_contract_indep_iff {α : Type*} (M : Matroid α) (I J : Set α) (hI : IsIndependent M I) : 
  IsIndependent (contract M I) J ↔ 
  J ∩ I = ∅ ∧ IsIndependent M (J ∪ I) := by sorry

/-- Let e be a non-loop element of M. For any set I, I is independent in M/{e} iff e ∉ I and I ∪ {e} is independent in M -/
theorem IsNonloop_contractElem_indep_iff {α : Type*} (M : Matroid α) (e : α) (I : Set α) 
  (he : IsNonloop M e) : 
  IsIndependent (contract M {e}) I ↔ 
  e ∉ I ∧ IsIndependent M (I ∪ {e}) := by sorry

/-- Let X ⊆ E(M) and let I be a basis of X. Then M/X = M/I \ (X \ I) -/
theorem IsBasis_contract_eq_contract_delete {α : Type*} (M : Matroid α) (X I : Set α) 
  (hI : IsBasis M X I) : 
  contract M X = (contract M I).delete (X \ I) := by sorry
