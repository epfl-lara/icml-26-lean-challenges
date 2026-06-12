import Mathlib

open Filter TopologicalSpace
open scoped Topology

/-!
# ShadowBench analysis/L2/ana_gen_L2_004

Formalization draft for `docs/source.tex`.
-/

/--
Source theorem `line-17` (`exists_seq_finite_rank_strongly_convergent_to`) states
that on a separable Hilbert space every bounded operator is the strong limit of
finite-rank bounded operators.

Source proof: choose a countable orthonormal basis, let `T_seq n` agree with `T`
on the first `n` basis vectors and vanish on the remaining basis vectors, so each
`T_seq n` has finite-dimensional range. For convergence, prove convergence first
on finite linear combinations of basis vectors, then approximate an arbitrary
vector and use boundedness plus the triangle inequality.

Prover notes: the source proof's final sentence should be read with the standard
density/approximation argument; it is not literally eventually zero for every
vector unless the vector has finite support in the chosen basis.
-/
theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [SeparableSpace H] (T : H →L[𝕜] H) :
    ∃ T_seq : ℕ → (H →L[𝕜] H),
      (∀ n, FiniteDimensional 𝕜 (LinearMap.range (T_seq n).toLinearMap)) ∧
      (∀ x : H, Tendsto (fun n : ℕ => T_seq n x) atTop (𝓝 (T x))) := by
  classical
  let d : ℕ → H := TopologicalSpace.denseSeq H
  let K : ℕ → Submodule 𝕜 H := fun n =>
    Submodule.span 𝕜 (((Finset.range (n + 1)).image d : Finset H) : Set H)
  have hKfd : ∀ n, FiniteDimensional 𝕜 (K n) := by
    intro n
    dsimp [K]
    infer_instance
  let P : ℕ → (H →L[𝕜] H) := fun n =>
    haveI : FiniteDimensional 𝕜 (K n) := hKfd n
    haveI : IsUniformAddGroup (K n) := AddSubgroup.isUniformAddGroup (K n).toAddSubgroup
    haveI : CompleteSpace (K n) := FiniteDimensional.complete 𝕜 (K n)
    (K n).starProjection
  let T_seq : ℕ → (H →L[𝕜] H) := fun n => T.comp (P n)
  refine ⟨T_seq, ?_, ?_⟩
  · intro n
    haveI : FiniteDimensional 𝕜 (K n) := hKfd n
    haveI : IsUniformAddGroup (K n) := AddSubgroup.isUniformAddGroup (K n).toAddSubgroup
    haveI : CompleteSpace (K n) := FiniteDimensional.complete 𝕜 (K n)
    have hPrange : LinearMap.range (P n).toLinearMap = K n := by
      simp [P]
    change FiniteDimensional 𝕜 (LinearMap.range (T.toLinearMap.comp (P n).toLinearMap))
    rw [LinearMap.range_comp]
    rw [hPrange]
    infer_instance
  · have hP_tendsto : ∀ x : H, Tendsto (fun n : ℕ => P n x) atTop (𝓝 x) := by
      intro x
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨j, hj⟩ :=
        (TopologicalSpace.denseRange_denseSeq (α := H)).exists_dist_lt x (half_pos hε)
      refine ⟨j, ?_⟩
      intro n hn
      haveI : FiniteDimensional 𝕜 (K n) := hKfd n
      haveI : IsUniformAddGroup (K n) := AddSubgroup.isUniformAddGroup (K n).toAddSubgroup
      haveI : CompleteSpace (K n) := FiniteDimensional.complete 𝕜 (K n)
      have hjmem_finset : d j ∈ ((Finset.range (n + 1)).image d : Finset H) := by
        exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩
      have hjmem : d j ∈ K n := by
        exact Submodule.subset_span hjmem_finset
      have hproj_d : P n (d j) = d j := by
        simpa [P] using (Submodule.starProjection_eq_self_iff (K := K n)).2 hjmem
      have hdist_proj : dist (P n x) (d j) ≤ dist x (d j) := by
        calc
          dist (P n x) (d j) = dist (P n x) (P n (d j)) := by rw [hproj_d]
          _ ≤ dist x (d j) := by
            simpa [P] using ((K n).lipschitzWith_starProjection.dist_le_mul x (d j))
      calc
        dist (P n x) x ≤ dist (P n x) (d j) + dist (d j) x := dist_triangle _ _ _
        _ ≤ dist x (d j) + dist (d j) x := by gcongr
        _ = dist x (d j) + dist x (d j) := by rw [dist_comm (d j) x]
        _ = 2 * dist x (d j) := by ring
        _ < ε := by linarith
    intro x
    simpa [T_seq, ContinuousLinearMap.comp_apply] using (T.continuous.tendsto x).comp (hP_tendsto x)
