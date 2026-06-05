import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span

/--
`S k n` is the source set of all polynomials in `k[x₁, …, xₙ]` with no zeros on
`k^n`, represented in Lean by `MvPolynomial (Fin n) k` and points `Fin n → k`.
-/
def S (k : Type*) [Field k] (n : ℕ) : Set (MvPolynomial (Fin n) k) :=
  {p | ∀ x : Fin n → k, MvPolynomial.aeval x p ≠ 0}

/--
Source theorem (`docs/source.tex`, `line-17`): if an ideal `I` in `k[x₁, …, xₙ]`
is disjoint from the set `S` of polynomials having no zeros on `k^n`, then its
zero locus is nonempty.

Source proof: no proof is supplied in the source document.
Proof sketch: use the contrapositive. If `MvPolynomial.zeroLocus k I = ∅`, then
produce some `p ∈ I` whose evaluations are all nonzero, giving `p ∈ S k n` and
contradicting `(I : Set _) ∩ S k n = ∅`. Unfold `MvPolynomial.mem_zeroLocus_iff`
to translate membership in the zero locus into simultaneous vanishing.
Prover notes: the statement intentionally keeps the source's arbitrary-field
quantifier; if proof search fails, check whether an additional field hypothesis is
missing from the source rather than weakening this theorem silently.
-/
theorem zeroLocus_nonempty_of_disjoint_noZeros (k : Type*) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : (I : Set (MvPolynomial (Fin n) k)) ∩ S k n = ∅) :
    MvPolynomial.zeroLocus k I ≠ ∅ := by
  sorry
