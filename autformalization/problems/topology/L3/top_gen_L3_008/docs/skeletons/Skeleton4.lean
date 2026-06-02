import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic

open Topology unitInterval

theorem existsUnique_continuousMap_lifts_of_range_le 
  (E X A : Type*) [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  (p : E → X) (hp : IsCoveringMap p)
  (hA_path : IsPathConnected A) (hA_loc : IsLocPathConnected A)
  (f : A → X) (hf : Continuous f)
  (a₀ : A) (e₀ : E) (he₀ : p e₀ = f a₀)
  (hfund : ∀ (l : A → ℝ) (hl : IsLoop l a₀), 
           ∃ (m : E → ℝ) (hm : IsLoop m e₀), 
           (f ∘ l) = (p ∘ m)) :
  ∃! F : A → E, Continuous F ∧ F a₀ = e₀ ∧ p ∘ F = f := by sorry
:= by sorry
