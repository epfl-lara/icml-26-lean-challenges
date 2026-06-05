import Mathlib

/--
Source `docs/source.tex`, line 17. `LCM m` denotes the least common multiple of
all positive integers up to the natural number `m`. This draft uses Mathlib's
the finite-set LCM over `Finset.Icc 1 m`, the interval of integers from `1`
through `m`.
-/
def LCM (m : ℕ) : ℕ :=
  (Finset.Icc 1 m).lcm id

/--
Source proof: unfold the definition of `LCM` and reduce positivity to the fact
that the LCM of the positive integers up to `m` is not zero.
Prover notes: unfold `LCM`; prove positivity of the finite LCM over `Finset.Icc 1 m`.
-/
lemma LCM_gt_0 (m : ℕ) : 0 < LCM m := by
  sorry

/--
Source proof: show the LCM is monotone by comparing the intervals `[1, m]` and
`[1, n]`; equivalently, prove the successor divisibility step and handle
`LCM 0 = LCM 1 = 1` directly.
Prover notes: unfold `LCM` and use monotonicity/inclusion facts for
the finite-set LCM over `Finset.Icc`.
-/
lemma LCM_monotone (m n : ℕ) (h : m ≤ n) : LCM m ≤ LCM n := by
  sorry

/--
Source proof: define `β'(m,n) = ∫_0^1 x^(m-1) * (1-x)^(n-m) dx`; compute it as
`1 / (m * binom n m)`, also expand it as an integer linear combination of
fractions `a_i / i` for `1 ≤ i ≤ n`. Clearing denominators with `LCM n`, since
each `i` divides `LCM n`, yields `m * binom n m ∣ LCM n`.
Prover notes: the Lean statement only records the arithmetic divisibility
claim. Existing binomial/LCM divisibility lemmas may avoid formalizing the
analytic beta-integral proof.
-/
lemma LCM_dvd_by (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    m * Nat.choose n m ∣ LCM n := by
  sorry

/--
Source proof: check `m = 7, 8` computationally. For odd `m = 2*k + 1`, use
binomial coefficient bounds together with divisibility of suitable products by
`LCM (2*k+1)`. For even `m`, reduce to a nearby odd case using monotonicity of
`LCM`.
Prover notes: likely dependencies are `LCM_dvd_by`, `LCM_monotone`, binomial
coefficient estimates, and coprimality/divisibility facts; finite-set LCM
facts over `Finset.Icc` should preserve the exact target statement.
-/
lemma LCM_range_lower_bdd (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ LCM m := by
  sorry
