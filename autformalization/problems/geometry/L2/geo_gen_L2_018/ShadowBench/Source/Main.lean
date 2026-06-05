import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Matrix

def linearConstraintImage {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Matrix (Fin p) (Fin n) ℝ) (g : Fin p → ℝ) : Set (Fin m → ℝ) :=
  {y : Fin m → ℝ | ∃ x : Fin n → ℝ, F.mulVec x = g ∧ y = A.mulVec x + b}

/--
Source proof: choose two witnesses `x₁`, `x₂` for two points of `{A x + b | F x = g}`.
For an arbitrary real `θ`, use the witness `θ • x₁ + (1 - θ) • x₂`; matrix-vector
linearity gives both the output identity and the constraint `F x = g`.
Prover notes: build the corresponding `AffineSubspace` or prove closure under real affine
combinations and convert that closure to Mathlib's `AffineSubspace` representation.
-/
theorem affineSubspace_image_of_linear_constraints (m n p : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Matrix (Fin p) (Fin n) ℝ) (g : Fin p → ℝ) :
    ∃ S : AffineSubspace ℝ (Fin m → ℝ),
      (S : Set (Fin m → ℝ)) = linearConstraintImage A b F g := by
  sorry
