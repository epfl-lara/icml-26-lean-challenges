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
  let U : OpenPartialHomeomorph (BallRnSpace n) (BallRnSpace n) :=
    OpenPartialHomeomorph.univUnitBall
  have hG : ∀ y : BallRnSpace n, ‖ballRnG n y‖ < (1 : ℝ) := by
    intro y
    have hy : U y ∈ Metric.ball (0 : BallRnSpace n) (1 : ℝ) := by
      exact U.map_source (by
        change y ∈ (Set.univ : Set (BallRnSpace n))
        simp)
    simpa [U, ballRnG, OpenPartialHomeomorph.univUnitBall, Metric.mem_ball, dist_eq_norm]
      using hy
  have hSmoothG : ContDiff ℝ ⊤ (ballRnG n) := by
    change ContDiff ℝ ⊤ (fun y : BallRnSpace n => (Real.sqrt (1 + ‖y‖ ^ 2))⁻¹ • y)
    suffices ContDiff ℝ ⊤ (fun y : BallRnSpace n => (Real.sqrt (1 + ‖y‖ ^ 2 : ℝ))⁻¹) from
      this.smul contDiff_id
    have hpos : ∀ y : BallRnSpace n, (0 : ℝ) < 1 + ‖y‖ ^ 2 := fun y => by positivity
    refine ContDiff.inv ?_ fun y => Real.sqrt_ne_zero'.mpr (hpos y)
    exact (contDiff_const.add <| contDiff_norm_sq ℝ).sqrt fun y => (hpos y).ne'
  have hSmoothF : ContDiffOn ℝ ⊤ (ballRnF n) {x : BallRnSpace n | ‖x‖ < (1 : ℝ)} := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ ⊤ (fun y : BallRnSpace n => (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • y) y
    suffices ContDiffAt ℝ ⊤ (fun y : BallRnSpace n => (Real.sqrt (1 - ‖y‖ ^ 2 : ℝ))⁻¹) y from
      this.smul contDiffAt_id
    have hpos : (0 : ℝ) < 1 - ‖y‖ ^ 2 := by
      have hylt : ‖y‖ < (1 : ℝ) := hy
      have hsquare : ‖y‖ ^ 2 < (1 : ℝ) := (sq_lt_one_iff₀ (norm_nonneg y)).mpr hylt
      nlinarith
    refine ContDiffAt.inv ?_ (Real.sqrt_ne_zero'.mpr hpos)
    change ContDiffAt ℝ ⊤ ((fun t : ℝ => Real.sqrt t) ∘ fun y : BallRnSpace n => (1 - ‖y‖ ^ 2)) y
    refine (Real.contDiffAt_sqrt hpos.ne').comp y ?_
    exact contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt
  have hLeftSubtype :
      Function.LeftInverse
        (fun y : BallRnSpace n => (⟨ballRnG n y, hG y⟩ : BallRnUnitBall n))
        (ballRnFOnBall n) := by
    intro x
    apply Subtype.ext
    have hx : (x : BallRnSpace n) ∈ Metric.ball (0 : BallRnSpace n) (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using x.2
    have h := U.right_inv (x := (x : BallRnSpace n)) hx
    simpa [U, ballRnFOnBall, ballRnF, ballRnG, OpenPartialHomeomorph.univUnitBall]
      using h
  have hRightSubtype :
      Function.RightInverse
        (fun y : BallRnSpace n => (⟨ballRnG n y, hG y⟩ : BallRnUnitBall n))
        (ballRnFOnBall n) := by
    intro y
    have h := U.left_inv (x := y) (by
      change y ∈ (Set.univ : Set (BallRnSpace n))
      simp)
    simpa [U, ballRnFOnBall, ballRnF, ballRnG, OpenPartialHomeomorph.univUnitBall]
      using h
  have hLeftAmbient : ∀ x : BallRnSpace n, ‖x‖ < (1 : ℝ) → ballRnG n (ballRnF n x) = x := by
    intro x hx
    have hx' : x ∈ Metric.ball (0 : BallRnSpace n) (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have h := U.right_inv (x := x) hx'
    simpa [U, ballRnF, ballRnG, OpenPartialHomeomorph.univUnitBall] using h
  have hRightAmbient : ∀ y : BallRnSpace n, ballRnF n (ballRnG n y) = y := by
    intro y
    have h := U.left_inv (x := y) (by
      change y ∈ (Set.univ : Set (BallRnSpace n))
      simp)
    simpa [U, ballRnF, ballRnG, OpenPartialHomeomorph.univUnitBall] using h
  refine ⟨hG, ?_⟩
  dsimp only
  refine ⟨hSmoothF, hSmoothG, hLeftSubtype, hRightSubtype, ?_⟩
  refine ⟨{ toFun := ballRnF n
            invFun := ballRnG n
            invFun_mem := hG
            smooth_toFun := hSmoothF
            smooth_invFun := hSmoothG
            left_inv := hLeftAmbient
            right_inv := hRightAmbient }, rfl, rfl⟩
