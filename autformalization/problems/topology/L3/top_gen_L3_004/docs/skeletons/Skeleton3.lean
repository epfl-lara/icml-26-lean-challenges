import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

open Topology unitInterval

theorem exists_lift_nhds (E X A : Type*) [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A] 
  (p : E → X) (hp : IsLocalHomeomorph p) 
  (f : unitInterval × A → X) (hf : Continuous f)
  (g : unitInterval × A → E) 
  (a : A) (hg : ContinuousOn g (({0} : Set unitInterval) ×ˢ A ∪ unitInterval ×ˢ {a})) :
  ∃ (N : Set A) (g' : unitInterval × A → E),
    IsOpen N ∧ a ∈ N ∧
    ContinuousOn g' (unitInterval ×ˢ N) ∧
    ∀ (t : unitInterval) (x : A), (t, x) ∈ ({0} : Set unitInterval) ×ˢ A ∪ unitInterval ×ˢ {a} → g' (t, x) = g (t, x) := by sorry
