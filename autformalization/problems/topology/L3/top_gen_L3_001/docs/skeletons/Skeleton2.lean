import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton

open scoped unitInterval Topology
open Homeomorph

-- Space of generalized N-loops based at x
def GeneralizedLoops (X : Type*) [TopologicalSpace X] (x : X) (N : Type*) [Fintype N] : Type* := sorry

-- Canonical homeomorphism that inserts coordinate t in the i-th position  
def canonicalHomeomorphism (N : Type*) [Fintype N] (i : N) : 
  unitInterval × (Fin (Fintype.card N - 1) → unitInterval) ≃ (Fin (Fintype.card N) → unitInterval) := sorry

-- Definition homotopyTo
def homotopyTo (X : Type*) [TopologicalSpace X] (x : X) (N : Type*) [Fintype N] 
  (i : N) : 
  GeneralizedLoops X x N → 
  (unitInterval → GeneralizedLoops X x (N ⊓ {i})) := sorry

-- Theorem homotopyTo_apply
theorem homotopyTo_apply (X : Type*) [TopologicalSpace X] (x : X) (N : Type*) [Fintype N] 
  (i : N) : 
  ∃ (map : GeneralizedLoops X x N → 
       {f : unitInterval → GeneralizedLoops X x (N ⊓ {i}) // f 0 = f 1}), 
  ∀ p : GeneralizedLoops X x N, 
    map p = ⟨homotopyTo X x N i p, sorry⟩ := by sorry

-- Theorem homotopicTo
theorem homotopicTo (X : Type*) [TopologicalSpace X] (x : X) (N : Type*) [Fintype N] 
  (i : N) (p q : GeneralizedLoops X x N) 
  (h : ∃ H : unitInterval × unitInterval → GeneralizedLoops X x (N ⊓ {i}),
       ∀ t : unitInterval, H (t, 0) = homotopyTo X x N i p t ∧ 
       H (t, 1) = homotopyTo X x N i q t ∧
       ∀ s : unitInterval, H (0, s) = H (1, s)) :
  ∃ K : unitInterval × unitInterval → GeneralizedLoops X x N,
    ∀ t : unitInterval, K (t, 0) = p ∧ 
    K (t, 1) = q ∧
    ∀ s : unitInterval, K (0, s) = K (1, s) := by sorry
