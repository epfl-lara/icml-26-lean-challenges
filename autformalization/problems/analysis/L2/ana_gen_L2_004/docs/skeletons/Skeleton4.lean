import Mathlib

open Filter TopologicalSpace
open scoped Topology

theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [SeparableSpace H] (T : ContinuousLinearMap 𝕜 H H) :
    ∃ T_seq : ℕ → ContinuousLinearMap 𝕜 H H,
      (∀ n, FiniteDimensional 𝕜 (LinearMap.range (T_seq n).toLinearMap)) ∧
      (∀ x : H, Tendsto (fun n => T_seq n x) atTop (𝓝 (T x))) := by sorry
