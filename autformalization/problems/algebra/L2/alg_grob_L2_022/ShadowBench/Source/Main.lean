import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder

/-- The set of monomial exponent vectors appearing in at least one polynomial of a set.
This is the Lean representation of the source notation `Mon(F)`. -/
def monomialSet {R : Type*} [CommSemiring R] {σ : Type*}
    (S : Set (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
  {m | ∃ f ∈ S, m ∈ f.support}

/--
Source proof: write `Mon(S)` as the union of the supports of all `f ∈ S`.  Then
membership in `Mon(F ∪ G)` is exactly membership in the support of some polynomial in
`F` or in `G`, so the result follows from the membership rule for set union.
Prover notes: unfold `monomialSet`, use `Set.ext` on an exponent vector, and split
`f ∈ F ∪ G` with `simp`.  The finiteness hypotheses and monomial-order parameter record
the source context but are not used by this set-theoretic identity.
-/
theorem monomial_set_union_distrib (R : Type*) [CommSemiring R] (σ : Type*)
    (_order : MonomialOrder σ) (F G : Set (MvPolynomial σ R))
    (_hF : F.Finite) (_hG : G.Finite) :
    monomialSet F ∪ monomialSet G = monomialSet (F ∪ G) := by
  ext m
  simp [monomialSet]
  aesop
