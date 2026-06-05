import Mathlib.AlgebraicGeometry.Morphisms.Proper

open CategoryTheory

/--
Source definition `line-17`: a finite morphism of schemes is affine and has finite
coordinate algebra on affine opens. This project-level name is a wrapper around Mathlib's
`AlgebraicGeometry.IsFinite`, whose affine-local definition matches the source statement.
-/
def IsFinite {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsFinite f

/--
Project-local representation bridge for the source's projective space `ℙ^n_Y`.

This records the scheme carrying the role of `ℙ^n_Y` and its projection to `Y`. The
blueprint marks this as a partial bridge because the current Mathlib search did not find a
canonical projective-space-over-a-scheme construction.
-/
structure ProjectiveSpaceOver (Y : AlgebraicGeometry.Scheme) (n : Nat) where
  space : AlgebraicGeometry.Scheme
  projection : space ⟶ Y

/--
Source definition `line-23`: source-shaped data witnessing that `f` factors through a
closed immersion into a projective-space object over the base.
-/
structure ProjectiveFactorization {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) where
  n : Nat
  P : ProjectiveSpaceOver Y n
  immersion : X ⟶ P.space
  isClosedImmersion : AlgebraicGeometry.IsClosedImmersion immersion
  factors : immersion ≫ P.projection = f

/--
Source definition `line-23`: a morphism is projective when it has a closed-immersion
factorization through `ℙ^n_Y` for some `n ≥ 0`, represented here by
`ProjectiveFactorization`.
-/
def IsProjective {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) : Prop :=
  Nonempty (ProjectiveFactorization f)

/--
Source theorem `line-35`: finite morphisms of schemes are projective.

Source proof: the statement is local on `Y`; after reducing to `Y = Spec A` and
`X = Spec B` with `B` finite over `A`, choose finite module generators of `B`, present
`B` as a quotient of a polynomial algebra, get a closed immersion into affine space, then
use the standard open immersion into projective space plus properness of finite morphisms
to obtain a closed subscheme of projective space.

Prover notes: unfold `IsFinite` to Mathlib's `AlgebraicGeometry.IsFinite`; search for
`AlgebraicGeometry.IsProper.instOfIsFinite` / `AlgebraicGeometry.instIsProperOfIsFinite`
for the properness step. The blueprint records that `ProjectiveSpaceOver` is the current
project-local bridge for `ℙ^n_Y`.
-/
theorem finite_implies_projective {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (hf : IsFinite f) : IsProjective f := by
  sorry
