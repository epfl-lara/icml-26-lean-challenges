import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Convex.Cone.Dual

open Matrix PointedCone

/-!
ShadowBench problem: geometry/L3/geo_gen_L3_003
Source: `docs/source.tex`
Blueprint: `ShadowBench/Source/Blueprint.md`
-/

/-- Pointwise nonnegativity, the finite-vector encoding of `x \succeq 0`. -/
def pointwiseNonneg {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ x i

/-- The image of the nonnegative orthant under a real matrix `A`. -/
def nonnegOrthantImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  {z | ∃ x : Fin n → ℝ, pointwiseNonneg x ∧ z = A.mulVec x}

/-- The finite-dimensional dual cone predicate, unfolded as nonnegative dot products. -/
def finiteDualCone {m : ℕ} (K : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {y | ∀ z, z ∈ K → 0 ≤ ∑ i, z i * y i}

/--
Source proof: unfold the dual cone as all `y` with nonnegative dot product against every
`z ∈ K`. For the forward inclusion, test the dual condition on `A` applied to each
standard basis vector of the nonnegative orthant, giving every component of `Aᵀ y`
nonnegative. Conversely, if `Aᵀ y` is pointwise nonnegative and `z = A x` with `x ≥ 0`,
rewrite `⟪z, y⟫` as `∑ j, x j * (Aᵀ y) j`; every summand is nonnegative.

Prover notes: prove by set extensionality in `y`; unfold `finiteDualCone`,
`nonnegOrthantImage`, and `pointwiseNonneg`. The forward direction should use a standard
basis vector such as `Pi.single j 1`. The reverse direction should use the searched matrix
identity `Matrix.dotProduct_transpose_mulVec` (or expand `Matrix.mulVec`) and
`Finset.sum_nonneg` with `mul_nonneg`.
-/
theorem dual_cone_matrix_image_nonneg (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    finiteDualCone (nonnegOrthantImage A) =
      {y : Fin m → ℝ | pointwiseNonneg (A.transpose.mulVec y)} := by
  ext y
  constructor
  · intro hy j
    have hsingle_nonneg : pointwiseNonneg (Pi.single j (1 : ℝ)) := by
      intro k
      by_cases hkj : k = j
      · subst k
        simp [Pi.single]
      · simp [Pi.single, hkj]
    have hz : A.mulVec (Pi.single j (1 : ℝ)) ∈ nonnegOrthantImage A := by
      exact ⟨Pi.single j (1 : ℝ), hsingle_nonneg, rfl⟩
    have htest := hy (A.mulVec (Pi.single j (1 : ℝ))) hz
    have hmulVec_single : A.mulVec (Pi.single j (1 : ℝ)) = fun i => A i j := by
      ext i
      rw [Matrix.mulVec, dotProduct]
      rw [Fintype.sum_eq_single j]
      · simp [Pi.single]
      · intro k hk
        simp [Pi.single, hk]
    have htest' : 0 ≤ ∑ i, A i j * y i := by
      simpa [hmulVec_single] using htest
    simpa [Matrix.mulVec, dotProduct] using htest'
  · intro hy z hz
    rcases hz with ⟨x, hx, rfl⟩
    calc
      0 ≤ ∑ j, x j * (A.transpose.mulVec y) j := by
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hy j))
      _ = ∑ i, (A.mulVec x) i * y i := by
        calc
          (∑ j, x j * (A.transpose.mulVec y) j)
              = ∑ j, ∑ i, x j * (A i j * y i) := by
                simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
          _ = ∑ i, ∑ j, x j * (A i j * y i) := by
                exact Finset.sum_comm
          _ = ∑ i, ∑ j, (A i j * x j) * y i := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = ∑ i, (∑ j, A i j * x j) * y i := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_mul]
          _ = ∑ i, (A.mulVec x) i * y i := by
                simp [Matrix.mulVec, dotProduct]
