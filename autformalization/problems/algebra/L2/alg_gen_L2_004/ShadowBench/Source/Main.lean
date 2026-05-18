import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

noncomputable section

/-- The coordinate ring representing the source notation `ℝ[x,y]`. -/
abbrev ShadowBenchRxy := MvPolynomial (Fin 2) ℝ

/-- The source polynomial variable `x`, represented as the first coordinate. -/
def shadowX : ShadowBenchRxy := X (0 : Fin 2)

/-- The source polynomial variable `y`, represented as the second coordinate. -/
def shadowY : ShadowBenchRxy := X (1 : Fin 2)

/-- The source ideal `J = ⟨x^2 + y^2 - 1, y - 1⟩` in `ℝ[x,y]`. -/
def shadowJ : Ideal ShadowBenchRxy :=
  Ideal.span
    ({shadowX ^ 2 + shadowY ^ 2 - (1 : ShadowBenchRxy),
      shadowY - (1 : ShadowBenchRxy)} : Set ShadowBenchRxy)

/--
Source `line-16`: for `J = ⟨x^2 + y^2 - 1, y - 1⟩` in `ℝ[x,y]`, find a
polynomial `f ∈ I(V(J))` with `f ∉ J`.

Source proof: take `f = x`. The common zeroes of `J` satisfy `y = 1` and then
`x^2 = 0`, hence the zero locus is `{(0,1)}`, so `x` vanishes on it. To show
`x ∉ J`, specialize `y` to `1`; the two generators map to `x^2` and `0`, so any
image of an element of `J` lies in `⟨x^2⟩`, but `x` does not.

Prover notes: instantiate the existential with `shadowX`; unfold `shadowJ`,
`zeroLocus`, and `vanishingIdeal` for the vanishing claim, and use the source's
specialization homomorphism argument for nonmembership.
-/
theorem exists_mem_vanishingIdeal_zeroLocus_not_mem_J :
    ∃ f : ShadowBenchRxy,
      f ∈ (vanishingIdeal ℝ (zeroLocus ℝ shadowJ) : Ideal ShadowBenchRxy) ∧
        f ∉ shadowJ := by
  use shadowX
  constructor
  · -- Show shadowX vanishes on the zero locus of shadowJ
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro p hp
    rw [MvPolynomial.mem_zeroLocus_iff] at hp
    have h1 : aeval p (shadowY - (1 : ShadowBenchRxy)) = 0 := by
      apply hp
      exact Ideal.subset_span (by simp)
    have h2 : aeval p (shadowX ^ 2 + shadowY ^ 2 - (1 : ShadowBenchRxy)) = 0 := by
      apply hp
      exact Ideal.subset_span (by simp)
    simp only [shadowX, shadowY, aeval_X, map_one, map_sub, map_add, map_pow] at h1 h2
    have h1' : p 1 = 1 := by linarith
    rw [h1'] at h2
    have h3 : p 0 = 0 := by nlinarith
    simp [shadowX, aeval_X, h3]
  · -- Show shadowX is not in shadowJ
    intro h
    rw [shadowJ] at h
    rw [Ideal.mem_span_pair] at h
    rcases h with ⟨a, b, h_eq⟩
    let φ : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
      MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (X 0 : MvPolynomial (Fin 2) ℝ)
        else (1 : MvPolynomial (Fin 2) ℝ))
    have h2 := congr_arg φ h_eq
    have h3 : φ shadowX = shadowX := by
      simp [φ, shadowX, aeval_X]
    have h4 : φ (shadowX ^ 2 + shadowY ^ 2 - (1 : ShadowBenchRxy)) = shadowX ^ 2 := by
      simp [φ, shadowX, shadowY, aeval_X, map_sub, map_add, map_pow]
    have h5 : φ (shadowY - (1 : ShadowBenchRxy)) = 0 := by
      simp [φ, shadowY, aeval_X, map_sub]
    have h2' : φ (a * (shadowX ^ 2 + shadowY ^ 2 - 1) + b * (shadowY - 1)) = φ a * shadowX ^ 2 := by
      rw [map_add, map_mul, map_mul, h4, h5]
      ring
    rw [h3, h2'] at h2
    have h6 : shadowX ∈ Ideal.span ({shadowX ^ 2} : Set ShadowBenchRxy) := by
      rw [Ideal.mem_span_singleton']
      exact ⟨φ a, h2⟩
    rw [Ideal.mem_span_singleton'] at h6
    rcases h6 with ⟨c, hc⟩
    have h7 : shadowX * (1 - c * shadowX) = 0 := by
      have h : c * shadowX ^ 2 = shadowX := hc
      calc
        shadowX * (1 - c * shadowX) = shadowX - c * shadowX ^ 2 := by ring
        _ = shadowX - shadowX := by rw [h]
        _ = 0 := by ring
    have h8 : shadowX ≠ 0 := by
      intro h0
      have h9 := congr_arg
        (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else (0 : ℝ))) h0
      simp [shadowX, aeval_X] at h9
    have h9 : 1 - c * shadowX = 0 := by
      apply (mul_eq_zero.mp h7).resolve_left
      exact h8
    have h10 : c * shadowX = 1 := by
      calc
        c * shadowX = 1 - (1 - c * shadowX) := by ring
        _ = 1 - 0 := by rw [h9]
        _ = 1 := by ring
    have h11 : IsUnit shadowX := by
      use Units.mk shadowX c (by rw [mul_comm]; exact h10) h10
    have h12 : ¬IsUnit shadowX := by
      intro h13
      rcases h13 with ⟨u, hu⟩
      have h14 : shadowX * u.inv = 1 := by
        rw [← hu]
        exact u.val_inv
      have h15 := congr_arg (MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℝ))) h14
      have h16 : MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℝ)) (shadowX * u.inv) = 0 := by
        rw [map_mul, shadowX, aeval_X]
        simp
      have h17 : MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℝ)) (1 : ShadowBenchRxy) = 1 := by
        simp
      rw [h16, h17] at h15
      exfalso
      norm_num at h15
    contradiction
