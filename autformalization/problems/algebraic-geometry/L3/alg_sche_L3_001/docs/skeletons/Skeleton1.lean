import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Reflective

open PrimeSpectrum
open Opposite
open CategoryTheory
open StructureSheaf
open Spec (structureSheaf)
open TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace
open TopCat.Presheaf
open TopCat.Presheaf.SheafCondition
open AlgebraicGeometry.Scheme

/-- Let X be a scheme. There is a canonical morphism φ : X → Spec(Γ(X)) from X to the spectrum of its global sections where the underlying continuous map is given by sending a point x ∈ X to the prime ideal p of global sections that do not map to units in the stalk of the structure sheaf at x. -/
theorem toΓSpec (X : Type u) [Scheme X] : 
  -- There exists a canonical morphism (we don't assert uniqueness)
  ∃ (φ : X ⟶ (Spec (GlobalSections (StructureSheaf X)))), 
    -- For each point x in X, the continuous map part sends x to the prime ideal
    -- of global sections that do not map to units in the stalk at x
    ∀ (x : X),
      let O_X := StructureSheaf X
      -- The prime ideal is formed by global sections whose germ at x is not a unit
      let p : Ideal (GlobalSections O_X) := 
        {s | ¬IsUnit ((s.mapStalk : GlobalSections O_X → O_X.stalk x) s)}
      -- This is where the continuous map sends x
      φ.toContinuousMap x = PrimeSpectrum.mk p
