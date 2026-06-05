import Mathlib
import Aesop

open MvPolynomial

noncomputable section

abbrev algGenL3005Ring (k : Type*) [CommSemiring k] := MvPolynomial (Fin 2) k

def algGenL3005_x (k : Type*) [CommSemiring k] : algGenL3005Ring k :=
  MvPolynomial.X (0 : Fin 2)

def algGenL3005_y (k : Type*) [CommSemiring k] : algGenL3005Ring k :=
  MvPolynomial.X (1 : Fin 2)

def algGenL3005_I (k : Type*) [CommSemiring k] : Ideal (algGenL3005Ring k) :=
  Ideal.span ({algGenL3005_x k ^ 2, algGenL3005_x k * algGenL3005_y k, algGenL3005_y k ^ 2} :
    Set (algGenL3005Ring k))

def algGenL3005_J (k : Type*) [CommSemiring k] : Ideal (algGenL3005Ring k) :=
  Ideal.span ({algGenL3005_x k ^ 2, algGenL3005_y k} : Set (algGenL3005Ring k))

def algGenL3005_K (k : Type*) [CommSemiring k] : Ideal (algGenL3005Ring k) :=
  Ideal.span ({algGenL3005_x k, algGenL3005_y k ^ 2} : Set (algGenL3005Ring k))

/--
Source proof: Let `m = <x,y>`. The source identifies
`I = <x^2, xy, y^2>` with `m^2`, computes `radical I = m`, and uses
`k[x,y]/m ≃ k` to see that `m` is maximal. Therefore the radical of `I`
is maximal, so Mathlib's primary-ideal criterion should prove `I` is primary.
Prover notes: look for `Ideal.isPrimary_of_isMaximal_radical`; prove the radical
calculation through the square of the variable ideal.
-/
theorem I_isPrimary (k : Type*) [Field k] :
    Ideal.IsPrimary (algGenL3005_I k) := by
  sorry

/--
Source proof: Put `J = <x^2,y>` and `K = <x,y^2>`. The source proves
`I = J ∩ K` by checking monomials: membership in both `J` and `K` means
`(a ≥ 2 or b ≥ 1)` and `(a ≥ 1 or b ≥ 2)`, hence divisibility by `x^2`,
`xy`, or `y^2`. The strict containments are witnessed by `y ∈ J \ I` and
`x ∈ K \ I`, so the displayed equality is a nontrivial infimum decomposition.
Prover notes: use monomial ideal membership lemmas for the equality, then unfold
`InfIrred` and refute it using the equality with `J` and `K` plus strictness.
-/
theorem I_not_infIrred (k : Type*) [Field k] :
    (algGenL3005_I k = algGenL3005_J k ⊓ algGenL3005_K k) ∧
      ¬ InfIrred (algGenL3005_I k) := by
  sorry
