import Mathlib

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

#check Scheme
#check Proj
#check MvPolynomial.homogeneousSubmodule
#check (Proj (MvPolynomial.homogeneousSubmodule (Fin 3) (ULift ℤ)))
#check (terminal.from (Spec (CommRingCat.of (ULift ℤ))))
#check (pullback (terminal.from (Spec (CommRingCat.of (ULift ℤ)))) (terminal.from (Proj (MvPolynomial.homogeneousSubmodule (Fin 3) (ULift ℤ)))))
#check CategoryTheory.Over.hom
#check CanonicallyOver
#check (show (𝟙 (Spec (CommRingCat.of (ULift ℤ)))) = 𝟙 _ from rfl)
