import Mathlib

theorem convexOn_sq_div {n : ℕ} {dom_f dom_g : Set (Fin n → ℝ)} 
  (f : (Fin n → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
  (hf_nonneg : ∀ x ∈ dom_f, 0 ≤ f x)
  (hf_convex : ConvexOn ℝ dom_f f)
  (hg_pos : ∀ x ∈ dom_g, 0 < g x)
  (hg_concave : ConcaveOn ℝ dom_g g) :
  let h := fun x => (f x)^2 / g x
  let dom_h := dom_f ∩ dom_g
  ConvexOn ℝ dom_h h := by sorry
