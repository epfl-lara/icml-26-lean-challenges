import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

open Topology unitInterval

theorem exists_lift_nhds {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    {p : E → X} (hp : IsLocalHomeomorph p) {f : I × A → X} (hf : Continuous f)
    {g : I × A → E} (hg : p ∘ g = f) (a : A)
    (hgc : ContinuousOn g ((({0} : Set I) ×ˢ Set.univ) ∪ (Set.univ ×ˢ {a}))) :
    ∃ N ∈ 𝓝 a, ∃ g' : I × A → E,
      ContinuousOn g' (Set.univ ×ˢ N) ∧
      ∀ x ∈ (({0} : Set I) ×ˢ Set.univ) ∪ (Set.univ ×ˢ {a}), g' x = g x := by
  sorry
