import Mathlib

/-!
ShadowBench problem `analysis/L3/ana_gen_L3_003`.
Source document: `docs/source.tex`.
Blueprint: `ShadowBench/Source/Blueprint.md`.
-/

/--
Source theorem `line-17`, `convexOn_sq_div` in `docs/source.tex`.
Source proof: use the convex quadratic-over-linear map `(x, y) ↦ x^2 / y` on
`x ≥ 0`, `y > 0`; it is monotone increasing in `x` and monotone decreasing in
`y`, so composing it with a nonnegative convex `f` and a positive concave `g`
gives convexity of `f^2/g` on the common domain.
Prover notes: Mathlib may not expose this two-variable composition rule directly.
A direct Jensen proof can combine the `ConvexOn` inequality for `f`, the
`ConcaveOn` inequality for `g`, monotonicity of division by a positive
denominator, and the scalar quadratic-over-linear Jensen inequality.
-/
theorem convexOn_sq_div {n : ℕ} {dom_f dom_g : Set (Fin n → ℝ)}
    (f g : (Fin n → ℝ) → ℝ)
    (hf_nonneg : ∀ x ∈ dom_f, 0 ≤ f x)
    (hf_convex : ConvexOn ℝ dom_f f)
    (hg_pos : ∀ x ∈ dom_g, 0 < g x)
    (hg_concave : ConcaveOn ℝ dom_g g) :
    ConvexOn ℝ (dom_f ∩ dom_g) (fun x => (f x) ^ 2 / g x) := by
  sorry
