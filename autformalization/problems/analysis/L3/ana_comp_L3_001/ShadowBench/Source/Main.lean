import Mathlib

noncomputable section

/--
The bivariate function from the source theorem,
`f(x,y) = g(x) * (e^(2y) - e^(-2y))`.
-/
def productPotential (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  g x * (Real.exp (2 * y) - Real.exp (-(2 * y)))

/--
Coordinate Laplacian `∂²/∂x² + ∂²/∂y²` for a real-valued bivariate function.
This is the coordinate form used in the source proof.
-/
def coordinateLaplacian (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv 2 (fun x' => F x' y) x +
    iteratedDeriv 2 (fun y' => F x y') y

/--
Source-specific bridge for the phrase “`g(x)[e^{2y} - e^{-2y}]` is harmonic”.
It records the standard `C²` regularity needed for the source calculation and the vanishing
coordinate Laplacian of the displayed product for every real `x` and `y`.
-/
def HarmonicProductForm (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧
    ∀ x y : ℝ, coordinateLaplacian (productPotential g) x y = 0

/--
Source proof: For `f(x,y)=g(x)(e^(2y)-e^(-2y))`, the source computes
`f_xx = g''(x)(e^(2y)-e^(-2y))` and
`f_yy = 4 g(x)(e^(2y)-e^(-2y))`. Harmonicity gives
`g''(x)+4g(x)=0`; the general solution is `A sin(2x)+B cos(2x)`.
The initial conditions give `B=0` and `2A=1`, hence `A=1/2`.

Prover notes: Expand `HarmonicProductForm` and `coordinateLaplacian`, derive the ODE
`iteratedDeriv 2 g x + 4 * g x = 0` by evaluating the Laplacian equation at a `y`
where `Real.exp (2*y) - Real.exp (-(2*y))` is nonzero, then use uniqueness for the
second-order linear ODE with initial data `g 0 = 0` and `deriv g 0 = 1`.
-/
theorem main_theorem (g : ℝ → ℝ)
    (h_harmonic : HarmonicProductForm g)
    (h_g0 : g 0 = 0)
    (h_g_deriv0 : deriv g 0 = 1) :
    ∀ x : ℝ, g x = (1 / 2) * Real.sin (2 * x) := by
  sorry
