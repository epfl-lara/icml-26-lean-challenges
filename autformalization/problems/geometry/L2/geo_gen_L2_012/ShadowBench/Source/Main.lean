import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
  sorry
