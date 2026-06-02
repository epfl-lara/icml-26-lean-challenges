import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

open Topology unitInterval

theorem exists_path_lifts {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {γ : C(I, X)} {e : E} (he : γ 0 = p e) :
    ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e := by sorry

lemma eq_liftPath_iff {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    {f : E → X} (hf : IsCoveringMap f) [PreconnectedSpace A] {g₁ g₂ : C(A, E)}
    (hfg : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) :
    g₁ = g₂ := by sorry

lemma eq_liftPath_iff' {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {γ : C(I, X)} {e : E} (he : γ 0 = p e)
    {γ̃ : C(I, E)} (hγ̃ : p ∘ γ̃ = γ ∧ γ̃ 0 = e) (Γ : I → E) :
    Γ = γ̃ ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e := by sorry
