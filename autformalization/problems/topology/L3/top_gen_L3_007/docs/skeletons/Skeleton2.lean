import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

open Topology unitInterval

theorem exists_path_lifts (E X : Type*) [TopologicalSpace E] [TopologicalSpace X] 
  (p : E → X) (hp : IsCoveringMap p) (γ : I → X) (e : E) (h : γ 0 = p e) :
  ∃ Γ : I → E, Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e := by sorry

lemma eq_liftPath_iff (E X A : Type*) [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  (f : E → X) (hf : IsCoveringMap f) (g₁ g₂ : A → E) 
  (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hfg : f ∘ g₁ = f ∘ g₂)
  (hpreconnected : IsPreconnected A) (a : A) (ha : g₁ a = g₂ a) :
  g₁ = g₂ := by sorry

lemma eq_liftPath_iff' (E X : Type*) [TopologicalSpace E] [TopologicalSpace X] 
  (p : E → X) (hp : IsCoveringMap p) (γ : I → X) (e : E) (h : γ 0 = p e)
  (γ_tilde : I → E) (hγ_tilde_cont : Continuous γ_tilde) 
  (hγ_tilde : p ∘ γ_tilde = γ) (hγ_tilde_0 : γ_tilde 0 = e) :
  ∀ Γ : I → E, (Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e) ↔ (Γ = γ_tilde) := by sorry
