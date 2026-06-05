import Mathlib

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

universe u

abbrev ProjectiveSpaceModel (n : ℕ) : Scheme.{u} := by
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))

noncomputable def ProjectiveSpace (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (ProjectiveSpaceModel.{u} n))

namespace ProjectiveSpace

instance instCanonicallyOver (n : ℕ) (S : Scheme.{u}) : (ProjectiveSpace n S).CanonicallyOver S where
  hom := pullback.fst _ _

noncomputable def π (n : ℕ) (S : Scheme.{u}) : ProjectiveSpace n S ⟶ S :=
  ProjectiveSpace n S ↘ S

end ProjectiveSpace

#check ProjectiveSpace
#check ProjectiveSpace.π
#check (ProjectiveSpace.π 2 (Spec (CommRingCat.of (ULift.{u} ℤ))))

end AlgebraicGeometry
