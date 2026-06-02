import Mathlib.Combinatorics.Matroid.Minor.Contract

open Set

-- Definition: N is a minor of M
def IsMinor {α : Type*} (N M : Matroid α) : Prop :=
  ∃ (C D : Set α), C ⊆ M.groundSet ∧ D ⊆ M.groundSet ∧ N = M / C \ D

-- Notation for the minor relation
infix:50 " ≤ₘ " => IsMinor

-- Definition: N is a strict minor of M  
def IsStrictMinor {α : Type*} (N M : Matroid α) : Prop :=
  IsMinor N M ∧ ¬IsMinor M N

-- Notation for the strict minor relation  
infix:50 " <ₘ " => IsStrictMinor

-- Lemma: if N is a minor of M, then there exist disjoint C, D such that N = M/C \ D
theorem IsMinor_exists_eq_contract_delete_disjoint {α : Type*} {N M : Matroid α} 
    (h : N ≤ₘ M) :
  ∃ (C D : Set α), C ⊆ M.groundSet ∧ D ⊆ M.groundSet ∧ Disjoint C D ∧ N = M / C \ D := by sorry

-- Lemma: the minor relation is antisymmetric (part of being a partial order)
theorem IsMinor_antisymm {α : Type*} {N M : Matroid α} (h1 : N ≤ₘ M) (h2 : M ≤ₘ N) : N = M := by sorry

lemma IsMinor.exists_eq_contract_delete_disjoint : True := by sorry
