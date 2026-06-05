import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
ShadowBench problem `analysis/L2/ana_gen_L2_003`.

The source theorem is formalized as vanishing of the two section derivatives at a
saddle point.  The source writes `∇ f(x̃, z̃) = 0`; because the hypotheses only
assume differentiability of the two coordinate sections, the Lean statement
records the proof-supported partial-gradient conclusion rather than the full
Fréchet derivative of the product map.
-/

/--
Source theorem `saddle_sections_hasFDerivAt_eq_zero`, `docs/source.tex`, lines 17-23.
A scalar function on `ℝ^n × ℝ^m` satisfies a saddle property at `(x̃, z̃)`: the
`z`-section has a global maximum at `z̃`, while the `x`-section has a global
minimum at `x̃`.  If both sections have Fréchet derivatives there, both section
derivatives vanish.

Source proof: apply Fermat's theorem separately.  The inequality
`f (x̃, z) ≤ f (x̃, z̃)` makes `z̃` a maximizer of `fun z => f (x̃, z)`, and the
inequality `f (x̃, z̃) ≤ f (x, z̃)` makes `x̃` a minimizer of
`fun x => f (x, z̃)`.

Prover notes: obtain `IsLocalMin (fun x => f (x, z̃)) x̃` and
`IsLocalMax (fun z => f (x̃, z)) z̃` from the global saddle inequality, then use
`IsLocalMin.hasFDerivAt_eq_zero` on `hf_x` and `IsLocalMax.hasFDerivAt_eq_zero`
on `hf_z`.
-/
theorem saddle_sections_hasFDerivAt_eq_zero
    {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n))
    (z0 : EuclideanSpace ℝ (Fin m))
    (h_saddle : ∀ (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)),
      f (x0, z) ≤ f (x0, z0) ∧ f (x0, z0) ≤ f (x, z0))
    (fx' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hf_x : HasFDerivAt (fun x => f (x, z0)) fx' x0)
    (fz' : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hf_z : HasFDerivAt (fun z => f (x0, z)) fz' z0) :
    fx' = 0 ∧ fz' = 0 := by
  sorry
