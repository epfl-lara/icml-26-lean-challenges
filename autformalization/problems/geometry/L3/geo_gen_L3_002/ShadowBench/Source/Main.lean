import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Sheaf.Basic

noncomputable section

open scoped Manifold
open Real

/-- The Euclidean space used to model the source's `ℝ^n`. -/
abbrev BallRnSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The open unit ball `𝔹^n = {x : ℝ^n | ‖x‖ < 1}`. -/
abbrev BallRnUnitBall (n : ℕ) := {x : BallRnSpace n // ‖x‖ < (1 : ℝ)}

/-- Ambient formula for `F(x) = x / sqrt (1 - |x|^2)`. -/
def ballRnF (n : ℕ) (x : BallRnSpace n) : BallRnSpace n :=
  (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹ • x

/-- Ambient formula for `G(y) = y / sqrt (1 + |y|^2)`. -/
def ballRnG (n : ℕ) (y : BallRnSpace n) : BallRnSpace n :=
  (Real.sqrt (1 + ‖y‖ ^ 2))⁻¹ • y

/-- Source-domain version of `F : 𝔹^n → ℝ^n`. -/
def ballRnFOnBall (n : ℕ) (x : BallRnUnitBall n) : BallRnSpace n :=
  ballRnF n x

/--
A source-local bridge for the statement that the unit ball and Euclidean space are
diffeomorphic: it records smooth inverse data for ambient formulas, with the inverse
map landing in the open unit ball.
-/
structure BallRnDiffeomorphismData (n : ℕ) where
  toFun : BallRnSpace n → BallRnSpace n
  invFun : BallRnSpace n → BallRnSpace n
  invFun_mem : ∀ y, ‖invFun y‖ < (1 : ℝ)
  smooth_toFun : ContDiffOn ℝ ⊤ toFun {x : BallRnSpace n | ‖x‖ < (1 : ℝ)}
  smooth_invFun : ContDiff ℝ ⊤ invFun
  left_inv : ∀ x, ‖x‖ < (1 : ℝ) → invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

/--
Source proof (docs/source.tex, `ballRnDiffeomorph`, lines 17-53): compute
`‖F x‖^2 = ‖x‖^2 / (1 - ‖x‖^2)` for `‖x‖ < 1`, so substituting into `G`
gives `G (F x) = x`. Similarly compute
`‖G y‖^2 = ‖y‖^2 / (1 + ‖y‖^2)`, so substituting into `F` gives
`F (G y) = y`. Smoothness follows because squared norm is smooth and the
square-root denominators are positive on the stated domains.

Prover notes: prove the landing condition for `ballRnG`, then unfold `ballRnF`
and `ballRnG` for the two inverse identities; use positivity of
`sqrt (1 - ‖x‖^2)` on the ball and of `sqrt (1 + ‖y‖^2)` globally. For
smoothness, search for `Homeomorph.contDiff_unitBall`,
`OpenPartialHomeomorph.contDiff_univUnitBall`, and sqrt/`ContDiff` composition
lemmas.
-/
theorem ballRnDiffeomorph (n : ℕ) :
    ∃ hG : ∀ y : BallRnSpace n, ‖ballRnG n y‖ < (1 : ℝ),
      let F : BallRnUnitBall n → BallRnSpace n := ballRnFOnBall n
      let G : BallRnSpace n → BallRnUnitBall n := fun y => ⟨ballRnG n y, hG y⟩
      ContDiffOn ℝ ⊤ (ballRnF n) {x : BallRnSpace n | ‖x‖ < (1 : ℝ)} ∧
        ContDiff ℝ ⊤ (ballRnG n) ∧
          Function.LeftInverse G F ∧
            Function.RightInverse G F ∧
              ∃ D : BallRnDiffeomorphismData n,
                D.toFun = ballRnF n ∧ D.invFun = ballRnG n := by
  sorry
