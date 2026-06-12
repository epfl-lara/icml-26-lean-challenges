import Mathlib.RingTheory.Nullstellensatz

/-!
ShadowBench problem `algebra/L2/alg_gen_L2_011`.

This file formalizes the source theorem from `docs/source.tex` using Mathlib's
`MvPolynomial.zeroLocus` for affine zero loci of ideals in multivariate
polynomial rings.
-/

/--
Source theorem `zeroLocus_mul` (`docs/source.tex`, lines 17--25): for ideals
`I` and `J` in `k[x_1, ..., x_n]`, the zero locus of `I * J` is the union of the
zero loci of `I` and `J`.

Source proof: a point of `V(I * J)` makes every product `g(a) * h(a)` vanish. If
all `g ∈ I` vanish, the point lies in `V(I)`; otherwise choose one nonvanishing
`g` and use the field no-zero-divisor property to force every `h ∈ J` to vanish.
Conversely, a point in `V(I)` or `V(J)` makes all product generators, hence all
of `I * J`, vanish.

Prover notes: use pointwise set extensionality and unfold `MvPolynomial.zeroLocus`,
or convert vanishing at a point to containment in the singleton vanishing ideal
`MvPolynomial.vanishingIdeal k {x}` and use its primeness to split `I * J`.
-/
theorem zeroLocus_mul {k : Type*} [Field k] (n : ℕ)
    (I J : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.zeroLocus k (I * J) =
      MvPolynomial.zeroLocus k I ∪ MvPolynomial.zeroLocus k J := by
  ext x
  constructor
  · intro hx
    let P : Ideal (MvPolynomial (Fin n) k) :=
      MvPolynomial.vanishingIdeal k ({x} : Set (Fin n → k))
    have hprod : I * J ≤ P := by
      intro p hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mpr (hx p hp)
    have hprime : P.IsPrime := by
      dsimp [P]
      infer_instance
    rcases hprime.mul_le.mp hprod with hI | hJ
    · left
      intro p hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp (hI hp)
    · right
      intro p hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp (hJ hp)
  · intro hx
    let P : Ideal (MvPolynomial (Fin n) k) :=
      MvPolynomial.vanishingIdeal k ({x} : Set (Fin n → k))
    have hprime : P.IsPrime := by
      dsimp [P]
      infer_instance
    have hprod : I * J ≤ P := by
      rcases hx with hI | hJ
      · have hIle : I ≤ P := by
          intro p hp
          exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mpr (hI p hp)
        exact hprime.mul_le.mpr (Or.inl hIle)
      · have hJle : J ≤ P := by
          intro p hp
          exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mpr (hJ p hp)
        exact hprime.mul_le.mpr (Or.inr hJle)
    intro p hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp (hprod hp)
