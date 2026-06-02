import Mathlib.Combinatorics.Matroid.Minor.Contract
open Set

def IsMinor {α : Type*} (N M : Matroid α) : Prop :=
  ∃ (C D : Set α), C ⊆ M.groundSet ∧ D ⊆ M.groundSet ∧ N = M / C \ D

infix:50 " ≤ₘ " => IsMinor

def IsStrictMinor {α : Type*} (N M : Matroid α) : Prop :=
  IsMinor N M ∧ ¬IsMinor M N

infix:50 " <ₘ " => IsStrictMinor

theorem IsMinor.exists_eq_contract_delete_disjoint {α : Type*} {N M : Matroid α}
    (h : N ≤ₘ M) :
  ∃ (C D : Set α), C ⊆ M.groundSet ∧ D ⊆ M.groundSet ∧ Disjoint C D ∧ N = M / C \ D := by sorry

theorem IsMinor_antisymm {α : Type*} {N M : Matroid α} (h1 : N ≤ₘ M) (h2 : M ≤ₘ N) : N = M := by sorry
