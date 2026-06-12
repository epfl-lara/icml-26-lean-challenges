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

private lemma expFactor_iteratedDeriv_two (y : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.exp (2 * x) - Real.exp (-(2 * x))) y =
      4 * (Real.exp (2 * y) - Real.exp (-(2 * y))) := by
  change iteratedDeriv 2 ((fun x : ℝ => Real.exp (2 * x)) -
      (fun x : ℝ => Real.exp (-(2 * x)))) y = _
  rw [iteratedDeriv_sub]
  · rw [show (iteratedDeriv 2 fun x : ℝ => Real.exp (2 * x)) =
        (fun x => (2 : ℝ) ^ 2 * Real.exp (2 * x)) by
        exact iteratedDeriv_exp_const_mul 2 (2 : ℝ)]
    rw [show (iteratedDeriv 2 fun x : ℝ => Real.exp (-(2 * x))) =
        (fun x => (-2 : ℝ) ^ 2 * Real.exp (-(2 * x))) by
        have h := (iteratedDeriv_exp_const_mul 2 (-2 : ℝ))
        simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using h]
    ring
  · fun_prop
  · fun_prop

private lemma harmonicProductForm_ode (g : ℝ → ℝ) (h_harmonic : HarmonicProductForm g) :
    ∀ x : ℝ, iteratedDeriv 2 g x + 4 * g x = 0 := by
  intro x
  have h := h_harmonic.2 x 1
  simp only [coordinateLaplacian, productPotential, mul_one, iteratedDeriv_mul_const_field,
    iteratedDeriv_const_mul_field] at h
  rw [expFactor_iteratedDeriv_two] at h
  norm_num at h
  have hfac : Real.exp (2 : ℝ) - Real.exp (-2 : ℝ) ≠ 0 := by
    have hlt : Real.exp (-2 : ℝ) < Real.exp (2 : ℝ) := by
      rw [Real.exp_lt_exp]
      norm_num
    linarith
  have h' : (iteratedDeriv 2 g x + 4 * g x) *
      (Real.exp (2 : ℝ) - Real.exp (-2 : ℝ)) = 0 := by
    nlinarith
  exact mul_eq_zero.mp h' |>.resolve_right hfac

private lemma sinHalf_deriv :
    deriv (fun x : ℝ => (1 / 2 : ℝ) * Real.sin (2 * x)) =
      fun x : ℝ => Real.cos (2 * x) := by
  ext t
  have hlin : deriv (fun x : ℝ => (2 : ℝ) * x) t = 2 := by
    rw [deriv_const_mul]
    · simp
    · fun_prop
  rw [deriv_const_mul]
  · rw [deriv_sin]
    · change (1 / 2 : ℝ) * (Real.cos (2 * t) *
          deriv (fun x : ℝ => (2 : ℝ) * x) t) = Real.cos (2 * t)
      rw [hlin]
      ring
    · fun_prop
  · fun_prop

private lemma sinHalf_ode (x : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => (1 / 2 : ℝ) * Real.sin (2 * x)) x +
      4 * ((1 / 2 : ℝ) * Real.sin (2 * x)) = 0 := by
  have hiter : iteratedDeriv 2 (fun x : ℝ => (1 / 2 : ℝ) * Real.sin (2 * x)) =
      deriv (deriv (fun x : ℝ => (1 / 2 : ℝ) * Real.sin (2 * x))) := by
    simpa [iteratedDeriv_one] using
      (iteratedDeriv_succ (n := 1) (f := fun x : ℝ => (1 / 2 : ℝ) * Real.sin (2 * x)))
  rw [hiter, sinHalf_deriv]
  have hlin : deriv (fun y : ℝ => (2 : ℝ) * y) x = 2 := by
    rw [deriv_const_mul]
    · simp
    · fun_prop
  rw [deriv_cos]
  · change -Real.sin (2 * x) * deriv (fun y : ℝ => (2 : ℝ) * y) x +
        4 * ((1 / 2 : ℝ) * Real.sin (2 * x)) = 0
    rw [hlin]
    ring
  · fun_prop

private lemma oscillator_zero
    (h : ℝ → ℝ)
    (hcont : ContDiff ℝ 2 h)
    (hode : ∀ x : ℝ, iteratedDeriv 2 h x + 4 * h x = 0)
    (h0 : h 0 = 0)
    (hd0 : deriv h 0 = 0) :
    ∀ x : ℝ, h x = 0 := by
  have hdiff : Differentiable ℝ h := hcont.differentiable (by norm_num)
  have hdiff_deriv : Differentiable ℝ (deriv h) := by
    simpa [iteratedDeriv_one] using
      (hcont.differentiable_iteratedDeriv (m := 1) (by norm_num))
  have hiter : iteratedDeriv 2 h = deriv (deriv h) := by
    simpa [iteratedDeriv_one] using (iteratedDeriv_succ (n := 1) (f := h))
  let E : ℝ → ℝ := fun x => (deriv h x) ^ 2 + 4 * (h x) ^ 2
  have hdiffE : Differentiable ℝ E := by
    dsimp [E]
    fun_prop
  have hderivE_zero : ∀ x : ℝ, deriv E x = 0 := by
    intro x
    have hdhx : HasDerivAt h (deriv h x) x := (hdiff x).hasDerivAt
    have hddhx : HasDerivAt (deriv h) (deriv (deriv h) x) x :=
      (hdiff_deriv x).hasDerivAt
    have hdE : HasDerivAt E
        (2 * deriv h x * deriv (deriv h) x + 4 * (2 * h x * deriv h x)) x := by
      dsimp [E]
      convert ((hddhx.pow 2).add ((hdhx.pow 2).const_mul (4 : ℝ))) using 1
      ring
    have hsec : deriv (deriv h) x + 4 * h x = 0 := by
      simpa [hiter] using hode x
    have hsecond_eq : deriv (deriv h) x = -4 * h x := by
      linarith
    have hdEeq := hdE.deriv
    rw [hsecond_eq] at hdEeq
    nlinarith
  intro x
  have hconst := is_const_of_deriv_eq_zero hdiffE hderivE_zero x 0
  have hE0 : E 0 = 0 := by
    dsimp [E]
    simp [h0, hd0]
  have hEx : E x = 0 := by
    simpa [hE0] using hconst
  have hx_sq_nonneg : 0 ≤ (h x) ^ 2 := sq_nonneg (h x)
  have hdx_sq_nonneg : 0 ≤ (deriv h x) ^ 2 := sq_nonneg (deriv h x)
  have hx_sq_zero : (h x) ^ 2 = 0 := by
    dsimp [E] at hEx
    nlinarith
  exact sq_eq_zero_iff.mp hx_sq_zero

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
  let s : ℝ → ℝ := fun x => (1 / 2 : ℝ) * Real.sin (2 * x)
  let h : ℝ → ℝ := fun x => g x - s x
  have hg_cont : ContDiff ℝ 2 g := h_harmonic.1
  have hs_cont : ContDiff ℝ 2 s := by
    dsimp [s]
    fun_prop
  have hh_cont : ContDiff ℝ 2 h := by
    dsimp [h]
    exact hg_cont.sub hs_cont
  have hg_ode : ∀ x : ℝ, iteratedDeriv 2 g x + 4 * g x = 0 :=
    harmonicProductForm_ode g h_harmonic
  have hh_ode : ∀ x : ℝ, iteratedDeriv 2 h x + 4 * h x = 0 := by
    intro x
    have hgx := hg_ode x
    have hsx : iteratedDeriv 2 s x + 4 * s x = 0 := by
      simpa [s] using sinHalf_ode x
    have hiter_sub : iteratedDeriv 2 h x = iteratedDeriv 2 g x - iteratedDeriv 2 s x := by
      dsimp [h]
      change iteratedDeriv 2 (g - s) x = iteratedDeriv 2 g x - iteratedDeriv 2 s x
      rw [iteratedDeriv_sub]
      · exact hg_cont.contDiffAt
      · exact hs_cont.contDiffAt
    dsimp [h]
    rw [hiter_sub]
    nlinarith
  have hh0 : h 0 = 0 := by
    dsimp [h, s]
    simp [h_g0]
  have hds0 : deriv s 0 = 1 := by
    simpa [s] using congrFun sinHalf_deriv 0
  have hdh0 : deriv h 0 = 0 := by
    have hg_diff0 : DifferentiableAt ℝ g 0 := (hg_cont.differentiable (by norm_num)) 0
    have hs_diff0 : DifferentiableAt ℝ s 0 := by
      dsimp [s]
      fun_prop
    dsimp [h]
    rw [deriv_fun_sub hg_diff0 hs_diff0]
    nlinarith
  have hzero : ∀ x : ℝ, h x = 0 := oscillator_zero h hh_cont hh_ode hh0 hdh0
  intro x
  have hx := hzero x
  dsimp [h, s] at hx
  linarith
