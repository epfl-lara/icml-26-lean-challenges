import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic

open Topology

/-- If p : E → X is a covering map, A is path connected and locally path connected,
    f : A → X is continuous, and the induced homomorphism satisfy
    f_*(π₁(A,a₀)) ⊆ p_*(π₁(E,e₀)) ⊆ π₁(X,f(a₀)), then there exists a unique continuous
    map F : A → E such that F(a₀) = e₀ and p ∘ F = f. -/
theorem existsUnique_continuousMap_lifts_of_range_le 
  (E X A : Type*) [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  (p : E → X) (hp : IsCoveringMap p)
  (hA_path_connected : IsPathConnected A)
  (hA_loc_path_connected : IsLocallyPathConnected A)
  (f : A → X) (hf : Continuous f)
  (a₀ : A) (e₀ : E) (he₀ : p e₀ = f a₀)
  (hgroup : (∀ α : LoopAt A a₀, ∃ β : LoopAt E e₀, 
              FundamentalGroup.map f α = FundamentalGroup.map p β) ∧
            (∀ β : LoopAt E e₀, ∃ γ : LoopAt X (f a₀), 
              FundamentalGroup.map p β = FundamentalGroup.mk γ)) :
  ∃! F : A → E, Continuous F ∧ F a₀ = e₀ ∧ p ∘ F = f := by sorry
