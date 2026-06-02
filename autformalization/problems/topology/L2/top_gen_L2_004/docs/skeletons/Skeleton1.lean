import Mathlib.Order.Minimal
import Mathlib.Order.Zorn
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.DiscreteSubset

open Set Topology

-- Assuming IsPreirreducible is defined elsewhere
variable {X : Type*} [TopologicalSpace X]
variable (IsPreirreducible : Set X → Prop)

theorem exists_preirreducible (S : Set X) (hS : IsPreirreducible S) : 
  ∃ T : Set X, IsPreirreducible T ∧ S ⊆ T ∧ 
  (∀ U : Set X, IsPreirreducible U → S ⊆ U → U ⊆ T) := by sorry
