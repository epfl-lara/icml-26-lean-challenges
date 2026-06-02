import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Reflective

open PrimeSpectrum Opposite CategoryTheory StructureSheaf Spec TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace TopCat.Presheaf TopCat.Presheaf.SheafCondition
open AlgebraicGeometry.Scheme

theorem toΓSpec (X : Type u) [Scheme X] :
  ∃ (φ : X ⟶ Spec (GlobalSections (StructureSheaf X))),
    ∀ (x : X),
      let O_X := StructureSheaf X
      let p : Ideal (GlobalSections O_X) :=
        {s | ¬IsUnit ((s.mapStalk : GlobalSections O_X → O_X.stalk x) s)}
      φ.toContinuousMap x = PrimeSpectrum.mk p := by sorry
