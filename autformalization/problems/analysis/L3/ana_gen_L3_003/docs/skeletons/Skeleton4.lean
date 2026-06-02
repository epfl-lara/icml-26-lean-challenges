import Mathlib

theorem convexOn_sq_div {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s t : Set E} {f g : E → ℝ}
    (hf : ConvexOn ℝ s f) (hg : ConcaveOn ℝ t g)
    (hf_nonneg : ∀ x ∈ s, 0 ≤ f x) (hg_pos : ∀ x ∈ t, 0 < g x) :
    ConvexOn ℝ (s ∩ t) (fun x => f x ^ 2 / g x) := by sorry
