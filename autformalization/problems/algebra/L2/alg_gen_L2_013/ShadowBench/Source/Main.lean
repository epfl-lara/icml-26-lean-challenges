import Mathlib.RingTheory.Nullstellensatz

/--
An affine algebraic set in affine space over `k`, represented as a zero locus of an
ideal of multivariate polynomials. This is the Lean bridge for the source phrase
“affine algebraic set”.
-/
def IsAffineAlgebraicSet (k : Type*) [Field k] {σ : Type*} (W : Set (σ → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ k), W = MvPolynomial.zeroLocus k I

/--
The source expression `V(I(S))`: the zero locus of the vanishing ideal of a set of
points in affine space over `k`.
-/
def zariskiClosure (k : Type*) [Field k] {σ : Type*} (S : Set (σ → k)) : Set (σ → k) :=
  MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k S)

/--
Source proof (docs/source.tex, `line-17`, proof lines 21-23): if `W ⊇ S`, then
`I(W) ⊆ I(S)` by the inclusion-reversing property of vanishing ideals; applying
the inclusion-reversing property of zero loci gives `V(I(S)) ⊆ V(I(W))`, and for
an affine algebraic set `W`, the ideal-variety correspondence identifies
`V(I(W))` with `W`.

Prover notes: unfold `zariskiClosure` and `IsAffineAlgebraicSet`. Use
`MvPolynomial.zeroLocus_vanishingIdeal_le` for the containment of `S`. For the
minimality clause, use `MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal` and the
zero-locus/vanishing-ideal Galois connection to turn `S ⊆ W` into the needed
reverse inclusion of zero loci.
-/
theorem zariskiClosure_is_smallest_algebraic_set (k : Type*) [Field k] (n : ℕ)
    (S : Set (Fin n → k)) :
    S ⊆ zariskiClosure k S ∧
      ∀ W : Set (Fin n → k), IsAffineAlgebraicSet k W → S ⊆ W →
        zariskiClosure k S ⊆ W := by
  constructor
  · unfold zariskiClosure
    exact MvPolynomial.zeroLocus_vanishingIdeal_le S
  · intro W hW hSW
    rcases hW with ⟨I, rfl⟩
    unfold zariskiClosure
    exact MvPolynomial.zeroLocus_anti_mono ((MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).1 hSW)
