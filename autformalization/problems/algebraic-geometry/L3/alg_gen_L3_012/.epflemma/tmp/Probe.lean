import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

universe u

/--
A type-valued functor on the overcategory of schemes over `S` is limit preserving
when it sends every filtered inverse system of affine `S`-schemes with a limit to
a filtered colimit after passing to the opposite overcategory.
-/
def functorOfPointsOver {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (J : Type u) [SmallCategory J] [IsFiltered J] (T : Jᵒᵖ ⥤ Over S) [HasLimit T],
    (∀ j : Jᵒᵖ, IsAffine (T.obj j).left) →
      PreservesColimit T.op F

/--
Source proof: the forward direction reduces finite presentation on affine opens
`V ⊆ S`, `U ⊆ X` to preservation of morphism sets along affine inverse limits;
the reverse direction proves the two usual colimit conditions for morphisms into
`X` over `S`, first uniqueness after increasing the index and then existence by
finite affine covers and gluing.
Prover notes: unfold `functorOfPointsOver`, use `locallyOfFinitePresentation_iff`
and the affine open criterion, then translate between limits in `Over S` and
colimits in `(Over S)ᵒᵖ` for the representable functor `yoneda.obj (Over.mk f)`.
-/
theorem locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      functorOfPointsOver (yoneda.obj (Over.mk f)) := by
  sorry
