import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem exists_seq_finite_rank_strongly_convergent_to (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H] :
  ∀ T : H →L[ℝ] H, ∃ (T_seq : ℕ → (H →L[ℝ] H)), 
    (∀ n, FiniteDimensional ℝ (LinearMap.range (T_seq n))) ∧
    Filter.Tendsto (fun n => T_seq n) Filter.atTop (nhds T) := by sorry
