import Mathlib

open Filter
open scoped Topology

/--
A continuous linear operator has finite rank when the range of its underlying linear map
is finite-dimensional. This is the Lean bridge for the source phrase "bounded operator
of finite rank".
-/
def HasFiniteRankOperator
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)

/--
Strong convergence of a sequence of bounded operators to a bounded operator, encoded as
pointwise convergence on every vector. This avoids the operator-norm topology on
`H →L[𝕜] H`, which would express norm convergence rather than strong convergence.
-/
def StrongOperatorTendsto
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (TSeq : ℕ → H →L[𝕜] H) (T : H →L[𝕜] H) : Prop :=
  ∀ x : H, Tendsto (fun n : ℕ => TSeq n x) atTop (𝓝 (T x))

/--
Source `docs/source.tex`, theorem `line-17`
(`exists_seq_finite_rank_strongly_convergent_to`): in a separable Hilbert space, every
bounded operator is the strong limit of a sequence of finite-rank bounded operators.

Source proof: choose a countable orthonormal basis `(g_k)`. Define `T_n` to agree with
`T` on the first `n` basis vectors and to vanish on the remaining basis vectors; equivalently,
`T_n = T` composed with the orthogonal projection onto the span of the first `n` basis
vectors. Each `T_n` has finite-dimensional range. The finite-span projections converge
strongly to the identity, hence `T_n x → T x` for every vector `x`.

Prover notes: use Hilbert-space orthonormal/Hilbert basis machinery for a separable space,
construct finite-span orthogonal projections, prove finite rank from the finite-dimensional
range of the projection, then compose with `T` and use pointwise convergence plus continuity
of `T`.
-/
theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (T : H →L[𝕜] H) :
    ∃ TSeq : ℕ → H →L[𝕜] H,
      (∀ n : ℕ, HasFiniteRankOperator (TSeq n)) ∧
        StrongOperatorTendsto TSeq T := by
  classical
  letI : Nonempty H := ⟨0⟩
  let u : ℕ → H := TopologicalSpace.denseSeq H
  let U : ℕ → Submodule 𝕜 H := fun n =>
    Submodule.span 𝕜 (((Finset.range n).image u : Finset H) : Set H)
  haveI hUfin : ∀ n : ℕ, FiniteDimensional 𝕜 (U n) := fun n => by
    dsimp [U]
    infer_instance
  haveI hUcomplete : ∀ n : ℕ, CompleteSpace (U n) := fun n => by
    exact completeSpace_coe_iff_isComplete.mpr ((U n).complete_of_finiteDimensional)
  have hUmono : Monotone U := by
    intro m n hmn
    dsimp [U]
    refine Submodule.span_mono ?_
    intro x hx
    rw [Finset.coe_image] at hx ⊢
    rcases hx with ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hmn), rfl⟩
  have hspan_le : Submodule.span 𝕜 (Set.range u) ≤ ⨆ n : ℕ, U n := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact (le_iSup U (k + 1)) (Submodule.subset_span (by
      rw [Finset.coe_image]
      exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩))
  have hu_dense : DenseRange u := by
    simp [u, TopologicalSpace.denseRange_denseSeq]
  have hspan_dense : ⊤ ≤ (Submodule.span 𝕜 (Set.range u)).topologicalClosure := by
    intro x hx
    exact Submodule.closure_subset_topologicalClosure_span (R := 𝕜) (s := Set.range u) (by
      simp [DenseRange.closure_range hu_dense])
  have hU_dense : ⊤ ≤ (⨆ n : ℕ, U n).topologicalClosure :=
    hspan_dense.trans (Submodule.topologicalClosure_mono hspan_le)
  refine ⟨fun n => T.comp (U n).starProjection, ?_, ?_⟩
  · intro n
    unfold HasFiniteRankOperator
    haveI : FiniteDimensional 𝕜 ((U n).map T.toLinearMap) := by infer_instance
    refine Submodule.finiteDimensional_of_le (S₂ := (U n).map T.toLinearMap) ?_
    rintro y ⟨x, rfl⟩
    change T ((U n).starProjection x) ∈ (U n).map T.toLinearMap
    exact ⟨(U n).starProjection x, (U n).starProjection_apply_mem x, rfl⟩
  · intro x
    have hx : Tendsto (fun n : ℕ => (U n).starProjection x) atTop (𝓝 x) :=
      Submodule.starProjection_tendsto_self U hUmono x hU_dense
    simpa [StrongOperatorTendsto, ContinuousLinearMap.comp_apply] using
      (T.continuous.tendsto x).comp hx
