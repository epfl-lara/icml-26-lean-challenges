import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Ring.Basic

/-
ShadowBench problem: analysis/L2/ana_comp_L2_002
Source: docs/source.tex
Instructions: docs/instructions.md
Blueprint: ShadowBench/Source/Blueprint.md
-/

/--
Source proof: write `z = x + i*y`, use the complex cosine formula
`cos (x + i*y) = cos x * cosh y - i * sin x * sinh y`, then compute the
complex modulus as the square root of the sum of squares of the real and
imaginary parts.
Proof sketch: the squared norm becomes
`cos^2 x * cosh^2 y + sin^2 x * sinh^2 y`; use `cosh^2 y = 1 + sinh^2 y`
and `cos^2 x + sin^2 x = 1` to simplify to `sinh^2 y + cos^2 x`.
Prover notes: start by rewriting with `hz`; relevant search hits include
`Complex.cos_add_mul_I`, complex norm/squared-norm identities, `Real.cosh_sq`,
and `Real.sin_sq_add_cos_sq`.
-/
theorem norm_cos_eq (z : ℂ) (x y : ℝ) (hz : z = x + Complex.I * y) :
    ‖Complex.cos z‖ = Real.sqrt (Real.sinh y ^ 2 + Real.cos x ^ 2) := by
  subst z
  rw [show Complex.I * (y : ℂ) = (y : ℂ) * Complex.I by ring]
  rw [Complex.cos_add_mul_I]
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sinh_ofReal_re]
  nlinarith [Real.cosh_sq y, Real.cos_sq_add_sin_sq x]
