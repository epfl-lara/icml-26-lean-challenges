import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph

open Manifold Function

/-- The standard coordinate model for `ℝ²` used by the source theorem. -/
abbrev Plane := ℝ × ℝ

/-- Standard first coordinate `x` on `ℝ²`. -/
def standardX : Plane → ℝ := fun p => p.1

/-- Standard second coordinate `y` on `ℝ²`. -/
def standardY : Plane → ℝ := fun p => p.2

/-- The transformed first coordinate `x̃ = x`. -/
def tildeX : Plane → ℝ := fun p => p.1

/-- The transformed second coordinate `ỹ = y + x^3`. -/
def tildeY : Plane → ℝ := fun p => p.2 + p.1 ^ 3

/-- The global coordinate map `p ↦ (x̃ p, ỹ p)`. -/
def tildeCoord : Plane → Plane := fun p => (tildeX p, tildeY p)

/-- The explicit inverse coordinate map `(x̃, ỹ) ↦ (x̃, ỹ - x̃^3)`. -/
def tildeCoordInv : Plane → Plane := fun q => (q.1, q.2 - q.1 ^ 3)

/-- The standard point `p = (1, 0)`. -/
def sourcePoint : Plane := (1, 0)

/--
A concrete bridge for the source phrase “global smooth coordinates”: the coordinate
map and the displayed inverse are two-sided inverses and both are `C^∞` smooth.
-/
def IsGlobalSmoothCoord (Φ Ψ : Plane → Plane) : Prop :=
  Function.LeftInverse Ψ Φ ∧ Function.RightInverse Ψ Φ ∧
    ContDiff ℝ ⊤ Φ ∧ ContDiff ℝ ⊤ Ψ

/-- Directional derivative at `p` in the standard `x` direction. -/
noncomputable def standardPartialXAt (p : Plane) : ((Plane → ℝ) → ℝ) :=
  fun f => fderiv ℝ f p (1, 0)

/--
Directional derivative at `p` for the transformed coordinate `x̃`, with `ỹ` held fixed.
For the inverse map `(u,v) ↦ (u, v - u^3)`, this is the standard tangent vector
`(1, -3 * u^2)`, and at the source point its `u`-coordinate is `1`.
-/
noncomputable def tildePartialXAt (p : Plane) : ((Plane → ℝ) → ℝ) :=
  fun f => fderiv ℝ f p (1, -3 * p.1 ^ 2)

/--
Source theorem `line-17` / `partial_x_ne_partial_xtilde_at_p` from `docs/source.tex`.
The coordinate map `(x, y) ↦ (x̃, ỹ) = (x, y + x^3)` is recorded by
`IsGlobalSmoothCoord tildeCoord tildeCoordInv`; the identity of the first coordinate
functions is `∀ q, standardX q = tildeX q`; and the displayed inequality is the
operator inequality between the two derivations at `p = (1, 0)`.

Source proof: no proof is supplied in the source. The intended proof is to use the
inverse coordinate formula `(u,v) ↦ (u, v - u^3)`, so `∂/∂x̃` at `p` is the directional
derivative in standard coordinates along `(1, -3)`, while `∂/∂x` is along `(1, 0)`.
A witness function such as `standardY` separates the two operators.
-/
theorem partial_x_ne_partial_xtilde_at_p :
    IsGlobalSmoothCoord tildeCoord tildeCoordInv ∧
      (∀ q : Plane, standardX q = tildeX q) ∧
      standardPartialXAt sourcePoint ≠ tildePartialXAt sourcePoint := by
  constructor
  · unfold IsGlobalSmoothCoord
    constructor
    · intro p
      ext <;> simp [tildeCoord, tildeCoordInv, tildeX, tildeY]
    · constructor
      · intro q
        ext <;> simp [tildeCoord, tildeCoordInv, tildeX, tildeY]
      · constructor
        · unfold tildeCoord tildeX tildeY
          fun_prop
        · unfold tildeCoordInv
          fun_prop
  · constructor
    · intro q
      rfl
    · intro h
      have hY := congrFun h standardY
      unfold standardPartialXAt tildePartialXAt sourcePoint at hY
      rw [show standardY = (Prod.snd : Plane → ℝ) by rfl] at hY
      norm_num [fderiv_snd] at hY
