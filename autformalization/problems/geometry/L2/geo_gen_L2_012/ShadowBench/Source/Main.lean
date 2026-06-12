import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.NumberTheory.Real.Irrational

open Complex Real Manifold

/-- The unit circle in the complex plane, represented by the norm-one condition. -/
def complexUnitCircle : Set ℂ :=
  {z | ‖z‖ = 1}

/-- The two-dimensional torus `S¹ × S¹` as a subset of the ambient space `ℂ × ℂ`. -/
def complexTwoTorus : Set (ℂ × ℂ) :=
  {p | p.1 ∈ complexUnitCircle ∧ p.2 ∈ complexUnitCircle}

/-- A concrete ambient-coordinate predicate for a smooth immersion into a subset of `ℂ²`.
It records that the map lands in the subset, is smooth as a map to the ambient normed
space, and has injective Fréchet derivative at every point. -/
def SmoothImmersionInto (s : Set (ℂ × ℂ)) (f : ℝ → ℂ × ℂ) : Prop :=
  Set.MapsTo f Set.univ s ∧
    ContDiff ℝ ⊤ f ∧
    ∀ t : ℝ, Function.Injective (fderiv ℝ f t)

/-- The ambient-coordinate formula `γ(t) = (exp(2π i t), exp(2π i α t))`. -/
noncomputable def gamma (α : ℝ) : ℝ → ℂ × ℂ :=
  fun t =>
    (Complex.exp (2 * Real.pi * Complex.I * t),
      Complex.exp (2 * Real.pi * Complex.I * α * t))

/--
Source theorem `docs/source.tex`, lines 17-21 (`gamma_is_smooth_immersion`).
Source proof: none is supplied in the document.
Proof sketch: the two coordinate functions are complex exponentials of real-linear
maps, so they are smooth. Their norms are one because the exponents are purely
imaginary, hence the image lies in `S¹ × S¹`. The derivative has first coordinate
`2π i exp(2π i t)`, which is never zero, so the differential is injective at every
`t`; the irrationality of `α` is a source-side hypothesis but is not needed for
local smooth-immersion.
Prover notes: unfold `SmoothImmersionInto`, `complexTwoTorus`, and `gamma`; prove
`Set.MapsTo` using `Complex.norm_exp`/purely imaginary real part, prove smoothness
by `ContDiff` closure for real-linear maps and `Complex.exp`, and prove derivative
injectivity from the nonzero first component of the `fderiv`.
-/
theorem gamma_is_smooth_immersion (α : ℝ) (hα : Irrational α) :
    SmoothImmersionInto complexTwoTorus (gamma α) := by
  have _ := hα
  refine ⟨?_, ?_, ?_⟩
  · intro t _
    constructor
    · change ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t))
    · change ‖Complex.exp (2 * Real.pi * Complex.I * α * t)‖ = 1
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * α * t))
  ·
    let f1 : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * t)
    let f2 : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * α * t)
    have hinner1 :
        ContDiff ℝ ⊤ (fun t : ℝ => (2 * Real.pi * Complex.I : ℂ) * (t : ℂ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (2 * Real.pi * Complex.I : ℂ))).mul
          Complex.ofRealCLM.contDiff)
    have hinner2 :
        ContDiff ℝ ⊤ (fun t : ℝ => (((2 * Real.pi * α : ℝ) * Complex.I : ℂ) * (t : ℂ))) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((contDiff_const : ContDiff ℝ ⊤
          (fun _ : ℝ => (((2 * Real.pi * α : ℝ) * Complex.I : ℂ)))).mul
          Complex.ofRealCLM.contDiff)
    have h1 : ContDiff ℝ ⊤ f1 := by
      simpa [f1, mul_assoc, mul_left_comm, mul_comm] using (Complex.contDiff_exp.comp hinner1)
    have h2 : ContDiff ℝ ⊤ f2 := by
      simpa [f2, mul_assoc, mul_left_comm, mul_comm] using (Complex.contDiff_exp.comp hinner2)
    simpa [gamma, f1, f2] using h1.prodMk h2
  · intro t u v huv
    let f1 : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * t)
    let f2 : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * α * t)
    have hsub : (fderiv ℝ (gamma α) t) (u - v) = 0 := by
      calc
        (fderiv ℝ (gamma α) t) (u - v) = (fderiv ℝ (gamma α) t) u - (fderiv ℝ (gamma α) t) v := by
          exact (fderiv ℝ (gamma α) t).map_sub u v
        _ = 0 := by simp [huv]
    have hsub' : (fderiv ℝ (fun t => (f1 t, f2 t)) t) (u - v) = 0 := by
      simpa [f1, f2, gamma] using hsub
    have hcd1 : ContDiff ℝ ⊤ f1 := by
      have hinner1 :
          ContDiff ℝ ⊤ (fun t : ℝ => (2 * Real.pi * Complex.I : ℂ) * (t : ℂ)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (2 * Real.pi * Complex.I : ℂ))).mul
            Complex.ofRealCLM.contDiff)
      simpa [f1, mul_assoc, mul_left_comm, mul_comm] using (Complex.contDiff_exp.comp hinner1)
    have hcd2 : ContDiff ℝ ⊤ f2 := by
      have hinner2 :
          ContDiff ℝ ⊤ (fun t : ℝ => (((2 * Real.pi * α : ℝ) * Complex.I : ℂ) * (t : ℂ))) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((contDiff_const : ContDiff ℝ ⊤
            (fun _ : ℝ => (((2 * Real.pi * α : ℝ) * Complex.I : ℂ)))).mul
            Complex.ofRealCLM.contDiff)
      simpa [f2, mul_assoc, mul_left_comm, mul_comm] using (Complex.contDiff_exp.comp hinner2)
    have hfderiv1 : DifferentiableAt ℝ f1 t :=
      (hcd1.differentiable (by simp)).differentiableAt
    have hfderiv2 : DifferentiableAt ℝ f2 t :=
      (hcd2.differentiable (by simp)).differentiableAt
    have hdf :
        fderiv ℝ (fun t => (f1 t, f2 t)) t = (fderiv ℝ f1 t).prod (fderiv ℝ f2 t) := by
      simpa [f1, f2] using (DifferentiableAt.fderiv_prodMk (f₁ := f1) (f₂ := f2) hfderiv1 hfderiv2)
    have hfst_eq : (fderiv ℝ f1 t) (u - v) = 0 := by
      have hfst0 : ((fderiv ℝ (fun t => (f1 t, f2 t)) t) (u - v)).1 = 0 := by
        simpa using congrArg Prod.fst hsub'
      simpa [hdf, ContinuousLinearMap.prod_apply] using hfst0
    have hlin :
        HasDerivAt (fun y : ℝ => (y : ℂ) * (2 * Real.pi * Complex.I : ℂ))
          (2 * Real.pi * Complex.I : ℂ) t := by
      simpa [smul_eq_mul, one_smul] using
        ((hasDerivAt_id t).smul_const (2 * Real.pi * Complex.I : ℂ))
    have hderiv1 : deriv f1 t ≠ 0 := by
      have hexp : HasDerivAt f1
          (Complex.exp (2 * Real.pi * Complex.I * t) * (2 * Real.pi * Complex.I : ℂ)) t := by
        simpa [f1, mul_assoc, mul_left_comm, mul_comm] using hlin.cexp
      have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ (0 : ℂ))
          (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
      simp [hexp.deriv, hconst]
    have hsmul0 : (u - v : ℝ) • deriv f1 t = 0 := by
      calc
        (u - v : ℝ) • deriv f1 t = (fderiv ℝ f1 t) (u - v) := by
          exact (fderiv_eq_smul_deriv (f := f1) (x := t) (y := u - v)).symm
        _ = 0 := hfst_eq
    have huv0 : u - v = 0 := (smul_eq_zero.mp hsmul0).resolve_right hderiv1
    exact sub_eq_zero.mp huv0
