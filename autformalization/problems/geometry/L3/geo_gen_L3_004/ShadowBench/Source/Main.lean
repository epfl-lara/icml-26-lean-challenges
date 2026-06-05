import Mathlib

open scoped Manifold ContDiff

noncomputable section

/--
The Lean representation of the source notation `𝔛(M)`: smooth vector fields are
infinitely differentiable sections of the tangent bundle.
-/
abbrev SmoothVectorFields
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Type _ :=
  ContMDiffSection I E ∞ (TangentSpace I : M → Type _)

/--
Source theorem `line-17` (`smoothVectorField_infinite_dimensional`).
Let `M` be a nonempty positive-dimensional smooth manifold with or without boundary;
then the space `𝔛(M)` of smooth vector fields on `M` is infinite-dimensional.

Source proof: argue by contradiction. If `𝔛(M)` had finite dimension `k`, choose
`k + 1` distinct points in one positive-dimensional coordinate chart, separate them by
pairwise disjoint open neighborhoods, and choose smooth bump functions `fᵢ` supported
there with `fᵢ xᵢ = 1`. Multiplying a nonzero local coordinate vector field
`∂/∂x¹` by these bumps and extending by zero gives global smooth vector fields `Xᵢ`
with disjoint supports. Evaluating a linear relation at `xⱼ` forces its `j`th
coefficient to vanish, giving `k + 1` independent vector fields, a contradiction.

Prover notes: `SmoothVectorFields I M` abbreviates Mathlib's
`ContMDiffSection I E ∞ (TangentSpace I)`. The side conditions make explicit that the
source manifold is Hausdorff, nonempty, and modeled on a finite-dimensional real vector
space of positive dimension; the model-with-corners parameter `I` represents the
source's “with or without boundary” cases.
-/
theorem smoothVectorField_infinite_dimensional
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [Nonempty M] [FiniteDimensional ℝ E]
    (h_pos : 0 < Module.finrank ℝ E) :
    ¬ FiniteDimensional ℝ (SmoothVectorFields I M) := by
  sorry
