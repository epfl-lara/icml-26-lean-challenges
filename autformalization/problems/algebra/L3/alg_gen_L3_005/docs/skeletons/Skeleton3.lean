import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem I_isPrimary (k : Type*) [Field k] :
  let R := MvPolynomial (Fin 2) k
  let x : R := MvPolynomial.X 0
  let y : R := MvPolynomial.X 1
  let I : Ideal R := Ideal.span {x^2, x*y, y^2}
  IsPrimary I := by sorry

theorem I_not_infIrred (k : Type*) [Field k] :
  let R := MvPolynomial (Fin 2) k
  let x : R := MvPolynomial.X 0
  let y : R := MvPolynomial.X 1
  let I : Ideal R := Ideal.span {x^2, x*y, y^2}
  let I1 : Ideal R := Ideal.span {x^2, y}
  let I2 : Ideal R := Ideal.span {x, y^2}
  (I = I1 ⊓ I2) ∧ (¬Irreducible I) := by sorry
