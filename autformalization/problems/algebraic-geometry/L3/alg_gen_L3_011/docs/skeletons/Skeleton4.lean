import Mathlib

open CategoryTheory
open CategoryTheory.Limits

/-- Let g: X → Y be a morphism of schemes over S. If X is affine over S and the diagonal map 
Δ: Y → Y ×ˢ Y is affine, then g is affine. -/
theorem isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal
  {S X Y : Type*} [Scheme S] [Scheme X] [Scheme Y]
  
  -- Structure for X, Y being schemes over S
  (f : X → S) (hX_scheme : IsSchemeMorphism f)
  (h : Y → S) (hY_scheme : IsSchemeMorphism h)
  
  -- g is a morphism of schemes over S
  (g : X → Y) (hg_scheme : IsSchemeMorphism g)
  (hg_commute : ∀ x, h (g x) = f x) -- g commutes with projections to S
  
  -- Fiber product Y ×ˢ Y over S
  {Y_times_Y_over_S : Type*} [Scheme Y_times_Y_over_S]
  (p₁ : Y_times_Y_over_S → Y) (hp₁ : IsSchemeMorphism p₁)
  (p₂ : Y_times_Y_over_S → Y) (hp₂ : IsSchemeMorphism p₂)
  (p₀ : Y_times_Y_over_S → S) (hp₀ : IsSchemeMorphism p₀)
  (h_fiber_product : ∀ (c : Y_times_Y_over_S), h (p₁ c) = h (p₂ c) ∧ h (p₁ c) = p₀ c ∧ h (p₂ c) = p₀ c)
  
  -- Diagonal map Δ: Y → Y ×ˢ Y is a morphism of schemes
  (Δ : Y → Y_times_Y_over_S) (hΔ_scheme : IsSchemeMorphism Δ)
  (hΔ_diagonal : ∀ y, p₁ (Δ y) = y ∧ p₂ (Δ y) = y) -- Δ is the diagonal map
  
  -- Hypotheses
  (hX_affine : IsAffineHom f) -- X is affine over S
  (hΔ_affine : IsAffineHom Δ) -- Diagonal map is affine
  
  : IsAffineHom g := by sorry
:= by sorry
