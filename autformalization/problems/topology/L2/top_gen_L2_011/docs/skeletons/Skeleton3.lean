import Mathlib.Topology.VectorBundle.Basic

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

/-- The Hom-bundle of σ-semilinear maps between two vector bundles.
    Let E₁, E₂ be vector bundles over a base space B with fibers F₁, F₂, respectively,
    where Fᵢ is a normed space over a normed field kᵢ, for i=1,2.
    Let σ: k₁ → k₂ be an isometric ring homomorphism.
    The Hom-bundle Hom_σ(E₁,E₂) is defined to be a vector bundle over B
    whose fiber Hom_σ(E₁,E₂)_x is defined as the space of σ-semilinear maps
    between (E₁)_x and (E₂)_x. -/
def continuousLinearMap 
  {B : Type*} [TopologicalSpace B] 
  {k₁ k₂ : Type*} [NormedField k₁] [NormedField k₂]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace k₁ F₁] 
                [NormedAddCommGroup F₂] [NormedSpace k₂ F₂]
  (E₁ : VectorBundle B F₁) (E₂ : VectorBundle B F₂)
  (σ : k₁ →+* k₂) (hσ : Isometry σ)
  : VectorBundle B (F₁ →ₛₗ[σ] F₂) (VectorSpaceAssembly B (fun x => E₁.fiber x →ₛₗ[σ] E₂.fiber x)) := by sorry

/-- The Hom-bundle inherits the structure of a vector bundle.
    Let E₁, E₂ be vector bundles over a base space B with fibers F₁, F₂, respectively,
    where Fᵢ is a normed space over a normed field kᵢ, for i=1,2.
    Let σ: k₁ → k₂ be an isometric ring homomorphism.
    The Hom-bundle Hom_σ(E₁,E₂) inherits the natural structure of a vector bundle. -/
theorem Bundle.ContinuousLinearMap.vectorBundle 
  {B : Type*} [TopologicalSpace B] 
  {k₁ k₂ : Type*} [NormedField k₁] [NormedField k₂]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace k₁ F₁] 
                [NormedAddCommGroup F₂] [NormedSpace k₂ F₂]
  (E₁ : VectorBundle B F₁) (E₂ : VectorBundle B F₂)
  (σ : k₁ →+* k₂) (hσ : Isometry σ)
  : let Hom := continuousLinearMap E₁ E₂ σ hσ
    -- The Hom-bundle is indeed a vector bundle
    True := by sorry
