import Mathlib

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

noncomputable section

/--
Integral model of projective `n`-space, realized as `Proj` of the standard homogeneous grading on
`ULift ℤ[x₀, ..., xₙ]`. The coordinate index type is `Fin (n + 1)`, matching the source convention
that `\mathbf{P}^n` has `n + 1` homogeneous coordinates.
-/
abbrev ProjectiveSpaceModel (n : ℕ) : Scheme.{u} := by
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))

/--
Projective space `\mathbf{P}^n_S` over a base scheme `S`, defined by base change of the integral
model of projective space along the unique map from `S` to the terminal scheme.
-/
def ProjectiveSpace (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (ProjectiveSpaceModel.{u} n))

namespace ProjectiveSpace

instance instCanonicallyOver (n : ℕ) (S : Scheme.{u}) :
    (ProjectiveSpace n S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The structure morphism `\pi : \mathbf{P}^n_S \to S`. -/
def π (n : ℕ) (S : Scheme.{u}) : ProjectiveSpace n S ⟶ S :=
  ProjectiveSpace n S ↘ S

end ProjectiveSpace

/--
Source definition (docs/source.tex, lines 17--27): a morphism `f : X \to S` of schemes is
Hartshorne-projective if it factors through a closed immersion into `\mathbf{P}^n_S` for some
`n ≥ 0`, followed by the structure morphism to `S`.
-/
def IsProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace n S),
    IsClosedImmersion i ∧ i ≫ ProjectiveSpace.π n S = f

/--
Source proof (docs/source.tex, lines 37--47): projective space over `S` is finite type, separated,
and universally closed. Universal closedness is shown by the valuative criterion: scale homogeneous
coordinates over a valuation ring so they lie in the ring and one is a unit, giving the required
extension; uniqueness follows from separatedness.

Prover notes: search for existing properness theorems for `Proj`/projective space first. Otherwise
unfold `IsProper` via finite type, separatedness, and universal closedness; the finite affine cover
by the standard opens `D_+(x_i)` and the valuative criterion are the source proof strategy.
-/
theorem is_projective_proper (S : Scheme.{u}) (n : ℕ) :
    IsProper (ProjectiveSpace.π n S) := by
  sorry

/--
Source proof (docs/source.tex, lines 53--60): if `f` is projective, choose a factorization
`X --i--> \mathbf{P}^n_S --π--> S` with `i` a closed immersion. Closed immersions are proper,
`π` is proper by `is_projective_proper`, and proper morphisms are stable under composition; rewrite
along the factorization equality to obtain properness of `f`.

Prover notes: unfold `IsProjective` to get witnesses `n`, `i`, `IsClosedImmersion i`, and
`i ≫ ProjectiveSpace.π n S = f`; combine properness of closed immersions with
`is_projective_proper S n` using properness stability under composition, then rewrite.
-/
theorem projective_isProper {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsProjective f) :
    IsProper f := by
  sorry

end

end AlgebraicGeometry

export AlgebraicGeometry (IsProjective is_projective_proper projective_isProper)
