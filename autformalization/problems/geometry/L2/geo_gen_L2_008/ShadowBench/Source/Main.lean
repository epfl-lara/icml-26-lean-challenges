import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Defs

open Set
open scoped ContDiff Manifold

/--
Source theorem `line-17` (`smooth_function_separating_closed_sets`).
Source proof: choose smooth nonnegative functions whose zero sets are `A` and `B`, then set
`f x = g_A x / (g_A x + g_B x)`; disjointness makes the denominator positive, and the quotient
has values in `[0,1]`, zero set `A`, and one set `B`.
Prover notes: Mathlib has `exists_contMDiff_zero_iff_one_iff_of_isClosed` in
`Mathlib.Geometry.Manifold.PartitionOfUnity`, which gives the exact zero/one level-set version;
convert `Set.range f ⊆ Icc 0 1` to the pointwise inequalities and rewrite the iff level sets as
preimage equalities.
-/
theorem smooth_function_separating_closed_sets
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (A B : Set M)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ f : M → ℝ,
      ContMDiff I 𝓘(ℝ) ∞ f ∧
        (∀ x : M, 0 ≤ f x ∧ f x ≤ 1) ∧
          f ⁻¹' {0} = A ∧ f ⁻¹' {1} = B := by
  rcases exists_contMDiff_zero_iff_one_iff_of_isClosed (I := I) (n := ⊤) hA hB hAB with
    ⟨f, hf_smooth, hf_range, hzero, hone⟩
  refine ⟨f, hf_smooth, ?_, ?_, ?_⟩
  · intro x
    exact hf_range (mem_range_self x)
  · ext x
    simp [hzero x]
  · ext x
    simp [hone x]
