import Mathlib

open CategoryTheory Opposite

/--
A morphism `f : X → Y` is said to be of finite type if `Y` can be covered by
affine open subsets `(V_α)` such that for each `α`, the inverse image `f⁻¹(V_α)`
is a finite union of affine open subsets `(U_{α i})`, and for each `i`, the ring
`Γ(U_{α i}, 𝒪_X)` is a finitely generated algebra over `Γ(V_α, 𝒪_Y)`.
-/
def FiniteType {X Y : Scheme} (f : X → Y) : Prop := by sorry

/--
Let `X` and `Y` be two affine schemes. Then, `X` is of finite type over `Y` if and only if
`Γ(X, 𝒪_X)` is a finite type algebra over `Γ(Y, 𝒪_Y)`.
-/
theorem affineFiniteType_iff_globalSectionsFiniteType {X Y : Scheme} 
  (hX : IsAffine X) (hY : IsAffine Y) (f : X → Y) :
  FiniteType f ↔ IsFinitelyGeneratedAlgebra (globalSections Y) (globalSections X) := by sorry
