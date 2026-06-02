import Mathlib

open Filter TopologicalSpace
open scoped Topology

theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [SeparableSpace H]
    (T : H →L[𝕜] H) :
    ∃ (T_seq : ℕ → (H →L[𝕜] H)),
      (∀ n, FiniteDimensional 𝕜 (LinearMap.range (T_seq n).toLinearMap)) ∧
      (∀ x, Tendsto (fun n => T_seq n x) atTop (𝓝 (T x))) := by sorry
