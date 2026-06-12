import Mathlib

/-!
ShadowBench problem `analysis/L3/ana_gen_L3_003`.
Source document: `docs/source.tex`.
Blueprint: `ShadowBench/Source/Blueprint.md`.
-/

private lemma weighted_average_pos {a b r s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hr : 0 < r) (hs : 0 < s) :
    0 < a * r + b * s := by
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by nlinarith
    subst a
    subst b
    simpa using hs
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
    have har : 0 < a * r := mul_pos ha_pos hr
    have hbs : 0 ≤ b * s := mul_nonneg hb (le_of_lt hs)
    nlinarith

private lemma sq_div_jensen_scalar {a b u v r s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hr : 0 < r) (hs : 0 < s) :
    (a * u + b * v) ^ 2 / (a * r + b * s) ≤
      a * (u ^ 2 / r) + b * (v ^ 2 / s) := by
  have hden : 0 < a * r + b * s := weighted_average_pos ha hb hab hr hs
  field_simp [hr.ne', hs.ne', hden.ne']
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  have hsq : 0 ≤ (s * u - r * v) ^ 2 := sq_nonneg (s * u - r * v)
  have hprod : 0 ≤ (a * b) * (s * u - r * v) ^ 2 := mul_nonneg hab_nonneg hsq
  nlinarith [hprod]

private lemma sq_div_mono_scalar {p U q R : ℝ}
    (hp0 : 0 ≤ p) (hpU : p ≤ U) (hR : 0 < R) (hRq : R ≤ q) :
    p ^ 2 / q ≤ U ^ 2 / R := by
  have hq : 0 < q := lt_of_lt_of_le hR hRq
  have hU0 : 0 ≤ U := le_trans hp0 hpU
  have hp2U2 : p ^ 2 ≤ U ^ 2 := by
    have hnonneg : 0 ≤ (U - p) * (U + p) :=
      mul_nonneg (sub_nonneg.mpr hpU) (add_nonneg hU0 hp0)
    nlinarith
  have hmul : p ^ 2 * R ≤ U ^ 2 * q :=
    mul_le_mul hp2U2 hRq (le_of_lt hR) (sq_nonneg U)
  field_simp [hq.ne', hR.ne']
  simpa [mul_comm] using hmul

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
  refine ⟨hf_convex.1.inter hg_concave.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx_f, hx_g⟩
  rcases hy with ⟨hy_f, hy_g⟩
  let z : Fin n → ℝ := a • x + b • y
  have hz_f : z ∈ dom_f := by
    simpa [z] using hf_convex.1 hx_f hy_f ha hb hab
  have hz_g : z ∈ dom_g := by
    simpa [z] using hg_concave.1 hx_g hy_g ha hb hab
  let U : ℝ := a * f x + b * f y
  let R : ℝ := a * g x + b * g y
  have hf_le : f z ≤ U := by
    simpa [z, U, smul_eq_mul] using hf_convex.2 hx_f hy_f ha hb hab
  have hg_le : R ≤ g z := by
    simpa [z, R, smul_eq_mul] using hg_concave.2 hx_g hy_g ha hb hab
  have hRpos : 0 < R := by
    exact weighted_average_pos ha hb hab (hg_pos x hx_g) (hg_pos y hy_g)
  have hmono : (f z) ^ 2 / g z ≤ U ^ 2 / R :=
    sq_div_mono_scalar (hf_nonneg z hz_f) hf_le hRpos hg_le
  have hjensen : U ^ 2 / R ≤ a * ((f x) ^ 2 / g x) + b * ((f y) ^ 2 / g y) := by
    simpa [U, R] using
      (sq_div_jensen_scalar (a := a) (b := b) (u := f x) (v := f y)
        (r := g x) (s := g y) ha hb hab (hg_pos x hx_g) (hg_pos y hy_g))
  exact by
    simpa [z, smul_eq_mul] using hmono.trans hjensen
