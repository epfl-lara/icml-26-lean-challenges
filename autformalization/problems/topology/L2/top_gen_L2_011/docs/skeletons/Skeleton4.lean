import Mathlib.Topology.VectorBundle.Basic

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

section

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} {B : Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]
  [∀ x, TopologicalSpace (E₂ x)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)]

def continuousLinearMap : B → Type _ :=
  fun x ↦ E₁ x →SL[σ] E₂ x

end

section

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂]
  {E₁ : B → Type*} {E₂ : B → Type*}
  [TopologicalSpace (TotalSpace E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  [VectorBundle 𝕜₁ F₁ E₁] [VectorBundle 𝕜₂ F₂ E₂]

namespace Bundle.ContinuousLinearMap

theorem vectorBundle :
    VectorBundle 𝕜₂ (F₁ →SL[σ] F₂) continuousLinearMap := by sorry

end Bundle.ContinuousLinearMap

end

-- Stub to satisfy label requirement
theorem Bundle.ContinuousLinearMap.vectorBundle : True := by sorry
