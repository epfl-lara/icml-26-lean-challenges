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
  refine ⟨
    { carrier := linearConstraintImage A b F g
      smul_vsub_vadd_mem := ?_ }, rfl⟩
  intro c y₁ y₂ y₃ hy₁ hy₂ hy₃
  rcases hy₁ with ⟨x₁, hx₁F, hy₁eq⟩
  rcases hy₂ with ⟨x₂, hx₂F, hy₂eq⟩
  rcases hy₃ with ⟨x₃, hx₃F, hy₃eq⟩
  refine ⟨c • (x₁ - x₂) + x₃, ?_, ?_⟩
  · simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hx₁F, hx₂F, hx₃F]
  · subst y₁
    subst y₂
    subst y₃
    ext i
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_neg, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm]
    ring
