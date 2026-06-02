import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Henselian

theorem mem_monmul_supp_iff {K σ : Type*} [Field K] [DecidableEq σ] :
  ∀ (μ ν : Finsupp σ ℕ), 
    (MvPolynomial.X μ ∣ MvPolynomial.X ν) ↔ 
    (∃ f : MvPolynomial σ K, MvPolynomial.X ν ∈ (MvPolynomial.X μ * f).support) := by sorry
:= by sorry
