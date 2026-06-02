import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.NumberTheory.Real.Irrational

open Complex Real Manifold

/-- The 2-torus T² as S¹ × S¹ embedded in ℂ² -/
def Torus : Type := {p : ℂ × ℂ // Complex.abs p.1 = 1 ∧ Complex.abs p.2 = 1}

/-- The map γ from ℝ to the 2-torus defined by γ(t) = (e^{2πit}, e^{2πiαt}) -/
noncomputable def gamma (α : ℝ) : ℝ → Torus :=
  fun t => ⟨(Complex.exp (2 * Real.pi * Complex.I * t),
            Complex.exp (2 * Real.pi * Complex.I * α * t)),
           by sorry, sorry⟩

/-- The map γ is a smooth immersion when α is irrational -/
theorem gamma_is_smooth_immersion (α : ℝ) (hα : Irrational α) :
  IsSmooth (gamma α) ∧ IsImmersion (gamma α) := by sorry
