import Mathlib.RingTheory.Polynomial.UniqueFactorization

open scoped BigOperators

theorem radical_span_singleton_eq_span_prod_irreducibles (k : Type*) [Field k] (n : ℕ) (f : MvPolynomial (Fin n) k) 
  (c : k) (factors : List (MvPolynomial (Fin n) k)) (exponents : List ℕ) 
  (h_nonzero : f ≠ 0)
  (h_factors_nonzero : ∀ g ∈ factors, g ≠ 0)
  (h_exponents_pos : ∀ e ∈ exponents, e > 0)
  (h_factorization : f = c • (factors.zip exponents).foldl (fun acc (g, e) => acc * g^e) 1)
  (h_irreducible : ∀ g ∈ factors, Irreducible g)
  (h_distinct : factors.Nodup)
  : Ideal.radical (Ideal.span {f}) = Ideal.span (factors.prod :: []) := by sorry
:= by sorry
