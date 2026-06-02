import Mathlib

open CategoryTheory Opposite
open TopologicalSpace

/-- A morphism of schemes is of finite type if the target can be covered by affine open 
subsets whose inverse images are covered by finitely many affine open subsets with 
corresponding rings of sections satisfying property (P). -/
def FiniteType {X Y : Type*} [Scheme X] [Scheme Y] (f : X → Y) : Prop := sorry

/-- Property (P): For an open affine subset V of Y, its inverse image f⁻¹(V) is a finite 
union of affine open subsets U_i such that each ring of sections Γ(U_i,𝒪_X) is a 
finitely generated algebra over Γ(V,𝒪_Y). -/
def hasPropertyP {X Y : Type*} [Scheme X] [Scheme Y] (f : X → Y) (V : Opens Y) (hV : IsAffine V) : Prop := sorry

/-- If f is a morphism of finite type, then every open affine subset of Y has property (P). -/
theorem hasPropertyP_of_finiteType {X Y : Type*} [Scheme X] [Scheme Y] (f : X → Y) (hf : FiniteType f) 
  (W : Opens Y) (hW : IsAffine W) : hasPropertyP f W hW := by sorry

/-- Let f : X → Y be an immersion. If the underlying space of Y is locally noetherian 
and the underlying space of X is noetherian, then f is of finite type. -/
theorem immersion_is_of_finiteType {X Y : Type*} [Scheme X] [Scheme Y] (f : X → Y) 
  (hf : IsImmersion f) (hY : TopologicalSpace.IsLocallyNoetherian (UnderlyingSpace Y)) 
  (hX : TopologicalSpace.IsNoetherian (UnderlyingSpace X)) : FiniteType f := by sorry
