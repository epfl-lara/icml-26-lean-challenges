import Mathlib.Analysis.Calculus.LocalExtr.Basic

theorem saddle_sections_hasFDerivAt_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × F → ℝ)
    (x̃ : E)
    (z̃ : F)
    (h_saddle : ∀ x : E, ∀ z : F, f (x̃, z) ≤ f (x̃, z̃) ∧ f (x̃, z̃) ≤ f (x, z̃))
    (f₁ : E →L[ℝ] ℝ)
    (hf₁ : HasFDerivAt (fun x => f (x, z̃)) f₁ x̃)
    (f₂ : F →L[ℝ] ℝ)
    (hf₂ : HasFDerivAt (fun z => f (x̃, z)) f₂ z̃) :
    f₁ = 0 ∧ f₂ = 0 := by sorry
