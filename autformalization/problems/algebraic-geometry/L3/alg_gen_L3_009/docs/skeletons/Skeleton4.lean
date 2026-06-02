import Mathlib

open CategoryTheory Opposite

--region Definition of FiniteType for morphisms of schemes
/-- A morphism of schemes is of finite type if the target can be covered by affine open sets
    whose preimages are finite unions of affine open sets with finitely generated coordinate rings. -/
class FiniteType {X Y : Type*} [Scheme X] [Scheme Y] (f : X → Y) : Prop where
  /-- There exists an affine open cover of Y such that the preimages are finite unions of
      affine open sets with finitely generated coordinate rings. -/
  cover : ∃ (V : Set (Set (StructureSheaf.X Y))), 
    -- V is a cover of Y
    (⋃ s ∈ V, s) = Set.univ ∧
    -- Each element of V is an affine open subset
    (∀ s ∈ V, IsOpen s ∧ IsAffine s) ∧
    -- For each affine open set in the cover
    ∀ v ∈ V, 
      -- The preimage f⁻¹(v) can be written as a finite union of affine open sets
      ∃ (W : Finset (Set (StructureSheaf.X X))), 
        (⋃ w ∈ W, w) = f ⁻¹' v ∧
        -- Each element of W is an affine open subset
        (∀ w ∈ W, IsOpen w ∧ IsAffine w) ∧
        -- The coordinate ring of each w is a finitely generated algebra over the coordinate ring of v
        ∀ w ∈ W, FiniteAlgebra (Γ v) (Γ w)
where
  /-- Sections of the structure sheaf (coordinate rings) -/
  Γ : {Z : Type*} [Scheme Z] → Set (StructureSheaf.X Z) → Type* := by sorry

--endregion

--region Theorem about surjectivity of finite type morphisms
/-- Let f: X → Y be a morphism of finite type. In order that f be surjective, 
    it is necessary and sufficient that, for every algebraically closed field Ω,
    the map from the Ω-points of X to the Ω-points of Y induced by f be surjective. -/
theorem surjective_iff_surjective_on_algClosed_points_of_finiteType 
  {X Y : Type*} [Scheme X] [Scheme Y] (f : X → Y) [FiniteType f] : 
  Function.Surjective f ↔ 
  ∀ (Ω : Type*) [Field Ω] [IsAlgClosed Ω], 
    Function.Surjective (λ (x : XPoints Ω) => fOnPoints Ω x)
where
  /-- Ω-points of a scheme X (morphism from Spec(Ω) to X) -/
  XPoints : Type* → Type* := by sorry
  /-- Action of f on Ω-points -/
  fOnPoints : ∀ {Ω : Type*} [Field Ω], XPoints Ω → YPoints Ω := by sorry
end
:= by sorry

-- Missing declaration stub
theorem FiniteType : True := by sorry
