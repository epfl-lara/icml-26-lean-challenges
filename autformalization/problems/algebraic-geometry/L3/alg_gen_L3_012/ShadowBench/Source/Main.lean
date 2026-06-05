import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

universe u

/--
Source definition (`docs/source.tex`, lines 17-19): for a scheme `S`, a functor
`F : (Sch/S)ᵒᵖ ⥤ Sets` is limit preserving if every directed inverse system of
affine schemes over `S` with limit `T` is sent to the filtered colimit of its
values on the approximating affine schemes.

Formalization note: `Over S` is Lean's category `Sch/S`; `Type u` is the set
universe; a filtered category `J` and a diagram `Jᵒᵖ ⥤ Over S` encode a directed
inverse system; `PreservesColimit T.op F` is the categorical form of
`F(T) = colim_i F(T_i)`.
-/
def functorOfPointsOver {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (J : Type u) [SmallCategory J] [IsFiltered J] (T : Jᵒᵖ ⥤ Over S) [HasLimit T],
    (∀ j : Jᵒᵖ, IsAffine (T.obj j).left) →
      PreservesColimit T.op F

/--
Source proof (`docs/source.tex`, theorem lines 20-22; proof lines 22-59): assuming
`h_X` is limit preserving, reduce local finite presentation to affine opens
`U ⊆ X`, `V ⊆ S` and show the induced ring map is finitely presented by testing
maps to a filtered colimit of `𝒪_S(V)`-algebras.  Translating the affine algebra
system to an inverse system of affine `S`-schemes, use limit preservation for
morphisms into `X` and the eventual-containment-in-`U` argument via the closed
sets `g_i⁻¹(X \ U)`.

Proof sketch / prover notes: for the converse, prove the colimit comparison for
`yoneda.obj (Over.mk f)` by the usual uniqueness and existence parts.  Uniqueness
uses the open `W = ⋃ U ×_V U` around the diagonal in `X ×_S X`, eventual entry
into `W`, finite affine reduction, and finite presentation on affine rings.
Existence descends maps from the limit by finite affine covers, then uses the
uniqueness part on quasi-compact overlaps to glue after increasing the index.
Unfold `functorOfPointsOver`, use `AlgebraicGeometry.locallyOfFinitePresentation_iff`,
and translate limits in `Over S` to colimits in `(Over S)ᵒᵖ` for the represented
functor of points.
-/
theorem locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      functorOfPointsOver (yoneda.obj (Over.mk f)) := by
  sorry
