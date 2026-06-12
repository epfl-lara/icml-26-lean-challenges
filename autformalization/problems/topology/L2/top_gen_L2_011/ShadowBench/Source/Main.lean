import Mathlib.Topology.VectorBundle.Hom

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

/--
Source definition `continuousLinearMap` (`docs/source.tex`, line 17): for two vector bundles over
a common base, the Hom-bundle has fiber the type of continuous `σ`-semilinear maps between the
corresponding fibers. Mathlib's Hom-bundle construction equips this family with its topology and
bundle structure; this declaration records the source's named fiber family.
-/
noncomputable def continuousLinearMap
    {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁]
    {𝕜₂ : Type*} [NontriviallyNormedField 𝕜₂]
    (σ : 𝕜₁ →+* 𝕜₂) {B : Type*}
    (E₁ : B → Type*) (E₂ : B → Type*)
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]
    [∀ x, TopologicalSpace (E₂ x)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)] :
    B → Type _ :=
  fun x ↦ E₁ x →SL[σ] E₂ x

attribute [reducible] continuousLinearMap

/--
Source theorem `Bundle.ContinuousLinearMap.vectorBundle` (`docs/source.tex`, lines 21--54): the
Hom-bundle inherits a natural vector-bundle structure. The exact source theorem name is supplied by
Mathlib's imported instance `Bundle.ContinuousLinearMap.vectorBundle`; this local companion states
the same conclusion through the source alias `continuousLinearMap` without redeclaring that name.

Source proof: equip each fiber with the operator-norm topology and `𝕜₂`-scalar multiplication;
if `e₁` and `e₂` trivialize the input bundles, the induced local trivialization sends `T` to
`e₂ x ∘ T ∘ (e₁ x)⁻¹`; transition maps act by `S ↦ g₂ x ∘ S ∘ (g₁ x)⁻¹` and are continuous.

Prover notes: after statement/source review, unfold `continuousLinearMap` and use the imported
instance `Bundle.ContinuousLinearMap.vectorBundle` from `Mathlib.Topology.VectorBundle.Hom`.
-/
theorem homBundle_vectorBundle_statement
    {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁]
    {𝕜₂ : Type*} [NontriviallyNormedField 𝕜₂]
    {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
    {B : Type*} [TopologicalSpace B]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂]
    {E₁ : B → Type*} {E₂ : B → Type*}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)] :
    VectorBundle 𝕜₂ (F₁ →SL[σ] F₂) (continuousLinearMap σ E₁ E₂) := by
  simpa [continuousLinearMap] using (Bundle.ContinuousLinearMap.vectorBundle σ F₁ E₁ F₂ E₂)
