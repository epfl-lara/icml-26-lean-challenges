import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/--
Source `docs/source.tex`, `line-17`.
Let `g : X → Y` be a morphism of schemes over `S`. If `X` is affine over `S`
and the diagonal map `Δ : Y → Y ×_S Y` is affine, then `g` is affine.

Source proof: the projection `X ×_S Y → Y` is the base change of `X → S`,
so it is affine. The graph morphism `(1,g) : X → X ×_S Y` is the base change
of the diagonal `Y → Y ×_S Y`, so it is affine. The morphism `g` is the
composition of these two affine morphisms.

Prover notes: `f : X ⟶ S` and `p : Y ⟶ S` are the structure morphisms, and
`w : g ≫ p = f` records that `g` is a morphism over `S`. Mathlib represents
`Y ×_S Y` as `pullback.diagonalObj p` and the diagonal as `pullback.diagonal p`.
Use stability of `IsAffineHom` under base change and composition.
-/
theorem isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal
    {S X Y : Scheme} (f : X ⟶ S) (p : Y ⟶ S) (g : X ⟶ Y)
    (w : g ≫ p = f) (hX : IsAffineHom f)
    (hΔ : IsAffineHom (pullback.diagonal p)) :
    IsAffineHom g := by
  sorry
