import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

-- Assume we have definitions for the relevant concepts
variable (IsQuasiCompact : {X Y : Type*} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop)
variable (IsDominant : {X Y : Type*} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop)
variable (IsIrreducible : Set → Prop)
variable (IsGenericPoint : {α : Type*} → [TopologicalSpace α] → α → Set α → Prop)

theorem isDominant_iff_forall_genericPoints_mem_fiber (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] 
  (f : X → Y) (hf : IsQuasiCompact f) :
  IsDominant f ↔ 
  ∀ y : Y, (∃ Z : Set Y, IsIrreducible Z ∧ IsGenericPoint y Z) →
  ∃ x : X, (∃ W : Set X, IsIrreducible W ∧ IsGenericPoint x W) ∧ f x = y := by sorry
