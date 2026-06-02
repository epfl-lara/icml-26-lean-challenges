import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

open Topology unitInterval

theorem existsUnique_continuousMap_lifts {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    (p : E → X) (hp : IsLocalHomeomorph p)
    (f : A → X) (hf : Continuous f)
    (a₀ : A) (e₀ : E) (he₀ : p e₀ = f a₀)
    (h₁ : ∀ γ : C(I, A), γ 0 = a₀ → ∃ Γ : C(I, E), Γ 0 = e₀ ∧ p ∘ Γ = f ∘ γ)
    (h₂ : ∀ γ γ' : C(I, A), γ 0 = a₀ → γ' 0 = a₀ →
      ∀ Γ Γ' : C(I, E), Γ 0 = e₀ → Γ' 0 = e₀ →
      p ∘ Γ = f ∘ γ → p ∘ Γ' = f ∘ γ' →
      γ 1 = γ' 1 → Γ 1 = Γ' 1) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  by sorry
