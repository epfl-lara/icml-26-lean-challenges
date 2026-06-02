import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

open Topology unitInterval

theorem existsUnique_continuousMap_lifts 
  (E X A : Type*) [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  (p : E → X) (hp : IsLocalHomeomorph p)
  (hA_path_connected : IsPathConnected A)
  (hA_loc_path_connected : IsLocPathConnected A)
  (f : A → X) (hf : Continuous f)
  (a₀ : A) (e₀ : E) (he₀ : p e₀ = f a₀)
  (h1 : ∀ γ : unitInterval → A, γ 0 = a₀ → ∃ Γ : unitInterval → E, Γ 0 = e₀ ∧ p ∘ Γ = f ∘ γ)
  (h2 : ∀ γ γ' : unitInterval → A, γ 0 = a₀ → γ' 0 = a₀ →
    ∀ Γ Γ' : unitInterval → E, 
      (Γ 0 = e₀ ∧ p ∘ Γ = f ∘ γ) → 
      (Γ' 0 = e₀ ∧ p ∘ Γ' = f ∘ γ') →
      γ 1 = γ' 1 → Γ 1 = Γ' 1) :
  ∃! F : A → E, Continuous F ∧ F a₀ = e₀ ∧ p ∘ F = f := by sorry
