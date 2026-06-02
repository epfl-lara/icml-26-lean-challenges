import Mathlib.Order.Minimal
import Mathlib.Order.Zorn
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.DiscreteSubset

open Set Topology

theorem exists_preirreducible {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreirreducible S) :
    ∃ T : Set X, IsPreirreducible T ∧ S ⊆ T ∧
      ∀ U : Set X, IsPreirreducible U → T ⊆ U → U = T := by
  sorry
