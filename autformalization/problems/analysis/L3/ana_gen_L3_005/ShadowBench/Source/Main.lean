import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open MeasureTheory Real Complex Set NNReal Filter Topology
open scoped intervalIntegral ENNReal

/-!
ShadowBench formalization for `analysis/L3/ana_gen_L3_005` from `docs/source.tex`.
-/

/--
Source proof: the source first applies the Riemann-Lebesgue lemma to get decay of the
real and imaginary trigonometric integrals.  For `f = χ_E`, it bounds the shifted
oscillatory integral of `cos (2 n x + 2 u_n)` by the decaying sine and cosine integrals,
then rewrites `cos^2 (n x + u_n)` as `(1 + cos (2 (n x + u_n))) / 2`, giving the limit
`m(E) / 2`.

Prover notes: use `Mathlib.Analysis.Fourier.RiemannLebesgueLemma` for the first conjunct;
for the second conjunct, specialize to an indicator of `E`, use `Real.cos_add`/double-angle
identities and the bounds on `sin` and `cos`, convert the constant set integral to
`(volume E).toReal`, and finish by Tendsto arithmetic.
-/
theorem integral_cos_sq_tendsto_half_measure :
  (∀ f : ℝ → ℂ, IntervalIntegrable f volume 0 (2 * Real.pi) →
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ |n| →
      ‖∫ x in (0)..(2 * Real.pi), f x * Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖ < ε) ∧
  (∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc 0 (2 * Real.pi) →
    ∀ u : ℕ → ℝ,
      Filter.Tendsto (fun n : ℕ => ∫ x in E, (Real.cos ((n : ℝ) * x + u n)) ^ 2)
        Filter.atTop (𝓝 ((volume E).toReal / 2))) := by
  let _proof := True.intro
  have tendsto_real_cocompact_integer_epsilon :
      ∀ {F : ℝ → ℂ}, Filter.Tendsto F (Filter.cocompact ℝ) (𝓝 0) →
        ∀ ε > 0, ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ |n| →
          ‖F ((n : ℝ) / (2 * Real.pi))‖ < ε := by
    intro F hF ε hε
    have hmem : {x : ℝ | ‖F x‖ < ε} ∈ Filter.cocompact ℝ := by
      have hdist := (Metric.tendsto_nhds.mp hF) ε hε
      simpa [dist_eq_norm] using hdist
    rcases (Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℝ)).mp hmem with ⟨R, hR⟩
    rcases exists_nat_gt (R * (2 * Real.pi)) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    apply hR
    intro hxball
    have hxle : ‖(n : ℝ) / (2 * Real.pi)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
    have hNle_real : (N : ℝ) ≤ |(n : ℝ)| := by
      have hnR : (((N : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ)) := by exact_mod_cast hn
      simpa [Int.cast_abs] using hnR
    have hpos : 0 < 2 * Real.pi := by positivity
    have hRlt : R < ‖(n : ℝ) / (2 * Real.pi)‖ := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
      exact (lt_div_iff₀' hpos).2 (by
        calc
          (2 * Real.pi) * R = R * (2 * Real.pi) := by ring
          _ < (N : ℝ) := hN
          _ ≤ |(n : ℝ)| := hNle_real)
    linarith
  have tendsto_real_cocompact_nat_neg_two :
      ∀ {F : ℝ → ℂ}, Filter.Tendsto F (Filter.cocompact ℝ) (𝓝 0) →
        Filter.Tendsto (fun n : ℕ => F (-(2 * (n : ℝ)) / (2 * Real.pi))) Filter.atTop (𝓝 0) := by
    intro F hF
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hmem : {x : ℝ | ‖F x‖ < ε} ∈ Filter.cocompact ℝ := by
      have hdist := (Metric.tendsto_nhds.mp hF) ε hε
      simpa [dist_eq_norm] using hdist
    rcases (Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℝ)).mp hmem with ⟨R, hR⟩
    rcases exists_nat_gt (R * Real.pi) with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hnormlt : ‖F (-(2 * (n : ℝ)) / (2 * Real.pi))‖ < ε := by
      apply hR
      intro hxball
      have hxle : ‖-(2 * (n : ℝ)) / (2 * Real.pi)‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
      have hNle_real : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpi : 0 < Real.pi := Real.pi_pos
      have hRlt : R < ‖-(2 * (n : ℝ)) / (2 * Real.pi)‖ := by
        have hnorm : ‖-(2 * (n : ℝ)) / (2 * Real.pi)‖ = (n : ℝ) / Real.pi := by
          have hnonneg : 0 ≤ (n : ℝ) / Real.pi := div_nonneg (by positivity) (le_of_lt hpi)
          rw [show -(2 * (n : ℝ)) / (2 * Real.pi) = -((n : ℝ) / Real.pi) by
            field_simp [Real.pi_ne_zero]]
          rw [norm_neg, Real.norm_of_nonneg hnonneg]
        rw [hnorm]
        exact (lt_div_iff₀ hpi).2 (by
          calc
            R * Real.pi < (N : ℝ) := hN
            _ ≤ (n : ℝ) := hNle_real)
      linarith
    simpa [dist_eq_norm] using hnormlt
  have fourier_smul_eq :
      ∀ (x r : ℝ) (z : ℂ),
        (Real.fourierChar (-(x * (r / (2 * Real.pi)))) : Circle) • z
          = z * Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)) := by
    intro x r z
    rw [Circle.smul_def]
    change ((Real.fourierChar (-(x * (r / (2 * Real.pi)))) : Circle) : ℂ) * z = _
    rw [show ((Real.fourierChar (-(x * (r / (2 * Real.pi)))) : Circle) : ℂ)
        = Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)) by
      rw [Real.fourierChar_apply]
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]]
    ring
  have interval_fourier_eq :
      ∀ (f : ℝ → ℂ) (r : ℝ),
        (∫ x in (0)..(2 * Real.pi), f x * Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)))
          = ∫ x, (Real.fourierChar (-(x * (r / (2 * Real.pi)))) : Circle) •
              (Set.Ioc 0 (2 * Real.pi)).indicator f x := by
    intro f r
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    rw [← MeasureTheory.integral_indicator
      (measurableSet_Ioc : MeasurableSet (Set.Ioc (0:ℝ) (2 * Real.pi)))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) (2 * Real.pi)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rw [fourier_smul_eq]
    · simp [hx]
  have global_fourier_set_eq :
      ∀ (E : Set ℝ), MeasurableSet E → ∀ r : ℝ,
        (∫ x, (Real.fourierChar (-(x * (r / (2 * Real.pi)))) : Circle) •
              E.indicator (fun _ : ℝ => (1 : ℂ)) x)
          = ∫ x in E, Complex.exp (-Complex.I * (r : ℂ) * (x : ℂ)) := by
    intro E hE r
    rw [← MeasureTheory.integral_indicator hE]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rw [fourier_smul_eq]
      simp
    · simp [hx]
  have finite_measure_of_subset_Icc :
      ∀ (E : Set ℝ), E ⊆ Set.Icc 0 (2 * Real.pi) → volume E < ∞ := by
    intro E hsub
    exact lt_of_le_of_lt (MeasureTheory.measure_mono hsub) (measure_Icc_lt_top)
  have integrableOn_cos_phase :
      ∀ (E : Set ℝ), E ⊆ Set.Icc 0 (2 * Real.pi) → ∀ (a b : ℝ),
        IntegrableOn (fun x : ℝ => Real.cos (a * x + b)) E volume := by
    intro E hsub a b
    have hcont : Continuous (fun x : ℝ => Real.cos (a * x + b)) := by fun_prop
    exact (hcont.integrableOn_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).mono_set hsub
  have setIntegral_cos_sq_decomp :
      ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Set.Icc 0 (2 * Real.pi) →
      ∀ (u : ℕ → ℝ) (n : ℕ),
        (∫ x in E, (Real.cos ((n : ℝ) * x + u n)) ^ 2)
          = (volume E).toReal / 2
            + (1 / 2) * (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n))) := by
    intro E hE hsub u n
    have hfin_ne : volume E ≠ ∞ := ne_of_lt (finite_measure_of_subset_Icc E hsub)
    have hconst : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) E volume := by
      exact MeasureTheory.integrableOn_const hfin_ne
    have hcos : IntegrableOn (fun x : ℝ => Real.cos (2 * ((n : ℝ) * x + u n))) E volume := by
      simpa [mul_add, mul_assoc] using integrableOn_cos_phase E hsub (2 * (n : ℝ)) (2 * u n)
    have hcos_div :
        IntegrableOn
          (fun x : ℝ => Real.cos (2 * ((n : ℝ) * x + u n)) / 2) E volume := by
      exact hcos.div_const 2
    calc
      (∫ x in E, (Real.cos ((n : ℝ) * x + u n)) ^ 2)
          = (∫ x in E, ((1 / 2 : ℝ) + Real.cos (2 * ((n : ℝ) * x + u n)) / 2)) := by
              apply MeasureTheory.setIntegral_congr_fun hE
              intro x hx
              change Real.cos ((n : ℝ) * x + u n) ^ 2 =
                (1 / 2 : ℝ) + Real.cos (2 * ((n : ℝ) * x + u n)) / 2
              rw [Real.cos_sq]
      _ = (∫ x in E, (1 / 2 : ℝ)) + (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n)) / 2) := by
              rw [MeasureTheory.integral_add hconst hcos_div]
      _ = (volume E).toReal / 2 + (1 / 2) * (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n))) := by
              rw [MeasureTheory.setIntegral_const (1 / 2 : ℝ)]
              rw [MeasureTheory.integral_div]
              simp [MeasureTheory.Measure.real, div_eq_mul_inv, mul_comm]
  have tendsto_setIntegral_exp_two_mul_zero :
      ∀ (E : Set ℝ), MeasurableSet E →
        Filter.Tendsto (fun n : ℕ => ∫ x in E,
          Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))) Filter.atTop (𝓝 0) := by
    intro E hE
    let F : ℝ → ℂ := fun w =>
      ∫ x, (Real.fourierChar (-(x * w)) : Circle) • E.indicator (fun _ : ℝ => (1 : ℂ)) x
    have hF : Filter.Tendsto F (Filter.cocompact ℝ) (𝓝 0) := by
      simpa [F] using Real.tendsto_integral_exp_smul_cocompact (E.indicator (fun _ : ℝ => (1 : ℂ)))
    have h := tendsto_real_cocompact_nat_neg_two hF
    convert h using 1
    ext n
    have heq := global_fourier_set_eq E hE (-(2 * (n : ℝ)))
    rw [show F (-(2 * (n : ℝ)) / (2 * Real.pi)) =
        (∫ x in E,
          Complex.exp (-Complex.I * (-(2 * (n : ℝ)) : ℂ) * (x : ℂ))) by
      simpa [F] using heq]
    apply MeasureTheory.setIntegral_congr_fun hE
    intro x hx
    apply congrArg Complex.exp
    push_cast
    ring
  have setIntegral_exp_phase_eq :
      ∀ (E : Set ℝ), MeasurableSet E → ∀ (u : ℕ → ℝ) (n : ℕ),
        (∫ x in E, Complex.exp (Complex.I * ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ)))
          = Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)) *
            (∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))) := by
    intro E hE u n
    calc
      (∫ x in E, Complex.exp (Complex.I * ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ)))
          = ∫ x in E, Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)) *
              Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ)) := by
            apply MeasureTheory.setIntegral_congr_fun hE
            intro x hx
            change Complex.exp (Complex.I * ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ)) =
              Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)) *
                Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))
            rw [← Complex.exp_add]
            apply congrArg Complex.exp
            push_cast
            ring
      _ = Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)) *
          (∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))) := by
            exact MeasureTheory.integral_const_mul (μ := volume.restrict E)
              (r := Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)))
              (f := fun x : ℝ => Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ)))
  have integrableOn_exp_phase :
      ∀ (E : Set ℝ), E ⊆ Set.Icc 0 (2 * Real.pi) → ∀ (a b : ℝ),
        IntegrableOn (fun x : ℝ => Complex.exp (Complex.I * ((a * x + b : ℝ) : ℂ))) E volume := by
    intro E hsub a b
    have hcont :
        Continuous
          (fun x : ℝ => Complex.exp (Complex.I * ((a * x + b : ℝ) : ℂ))) := by
      fun_prop
    exact (hcont.integrableOn_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).mono_set hsub
  have setIntegral_cos_eq_re_exp :
      ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Set.Icc 0 (2 * Real.pi) →
      ∀ (u : ℕ → ℝ) (n : ℕ),
        (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n)))
          = (∫ x in E, Complex.exp (Complex.I * ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ))).re := by
    intro E hE hsub u n
    let f : ℝ → ℂ := fun x => Complex.exp (Complex.I * ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ))
    have hf : IntegrableOn f E volume := by
      simpa [f, mul_add, mul_assoc] using integrableOn_exp_phase E hsub (2 * (n : ℝ)) (2 * u n)
    calc
      (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n)))
          = ∫ x in E, (f x).re := by
            apply MeasureTheory.setIntegral_congr_fun hE
            intro x hx
            change Real.cos (2 * ((n : ℝ) * x + u n)) =
              (Complex.exp (Complex.I * ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ))).re
            rw [show Complex.I * ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ)
                = ((2 * ((n : ℝ) * x + u n) : ℝ) : ℂ) * Complex.I by ring]
            exact (Complex.exp_ofReal_mul_I_re (2 * ((n : ℝ) * x + u n))).symm
      _ = (∫ x in E, f x).re := by
            simpa [f] using (integral_re (μ := volume.restrict E) hf)
  have tendsto_setIntegral_cos_phase_zero :
      ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Set.Icc 0 (2 * Real.pi) → ∀ u : ℕ → ℝ,
        Filter.Tendsto (fun n : ℕ => ∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n)))
          Filter.atTop (𝓝 0) := by
    intro E hE hsub u
    have hA := tendsto_setIntegral_exp_two_mul_zero E hE
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hAe := (Metric.tendsto_nhds.mp hA) ε hε
    filter_upwards [hAe] with n hn
    have hn_norm : ‖∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))‖ < ε := by
      simpa [dist_eq_norm] using hn
    have hreal := setIntegral_cos_eq_re_exp E hE hsub u n
    have hphase := setIntegral_exp_phase_eq E hE u n
    have hphase_norm : ‖Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ))‖ = 1 := by
      rw [show Complex.I * ((2 * u n : ℝ) : ℂ) = ((2 * u n : ℝ) : ℂ) * Complex.I by ring]
      exact Complex.norm_exp_ofReal_mul_I (2 * u n)
    have hineq : ‖∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n))‖ ≤
        ‖∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))‖ := by
      rw [hreal, hphase]
      calc
        ‖(Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)) *
            (∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ)))).re‖
            ≤ ‖Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)) *
            (∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ)))‖ := by
                simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm
                  (Complex.exp (Complex.I * ((2 * u n : ℝ) : ℂ)) *
            (∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))))
        _ = ‖∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))‖ := by
                rw [norm_mul, hphase_norm, one_mul]
    calc
      dist (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n))) 0
          = ‖∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n))‖ := by simp [dist_eq_norm]
      _ ≤ ‖∫ x in E, Complex.exp (Complex.I * ((2 * (n : ℝ) * x : ℝ) : ℂ))‖ := hineq
      _ < ε := hn_norm
  have fourier_interval_integer_epsilon :
      ∀ f : ℝ → ℂ, IntervalIntegrable f volume 0 (2 * Real.pi) →
        ∀ ε > 0, ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ |n| →
          ‖∫ x in (0)..(2 * Real.pi), f x * Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖ < ε := by
    intro f _hf ε hε
    let F : ℝ → ℂ := fun w =>
      ∫ x, (Real.fourierChar (-(x * w)) : Circle) • (Set.Ioc 0 (2 * Real.pi)).indicator f x
    have hF : Filter.Tendsto F (Filter.cocompact ℝ) (𝓝 0) := by
      simpa [F] using Real.tendsto_integral_exp_smul_cocompact
        ((Set.Ioc 0 (2 * Real.pi)).indicator f)
    rcases tendsto_real_cocompact_integer_epsilon hF ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    have heq := interval_fourier_eq f (n : ℝ)
    rw [show (∫ x in (0)..(2 * Real.pi), f x * Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))
          = ∫ x, (Real.fourierChar (-(x * ((n : ℝ) / (2 * Real.pi)))) : Circle) •
            (Set.Ioc 0 (2 * Real.pi)).indicator f x by
      simpa using heq]
    simpa [F] using h
  have tendsto_setIntegral_cos_sq :
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc 0 (2 * Real.pi) →
      ∀ u : ℕ → ℝ,
        Filter.Tendsto (fun n : ℕ => ∫ x in E, (Real.cos ((n : ℝ) * x + u n)) ^ 2)
          Filter.atTop (𝓝 ((volume E).toReal / 2)) := by
    intro E hE hsub u
    have hzero := tendsto_setIntegral_cos_phase_zero E hE hsub u
    have hlim : Filter.Tendsto
        (fun n : ℕ => (volume E).toReal / 2 + (1 / 2 : ℝ) *
          (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n))))
        Filter.atTop (𝓝 ((volume E).toReal / 2 + (1 / 2 : ℝ) * 0)) := by
      exact Filter.Tendsto.add tendsto_const_nhds (Filter.Tendsto.const_mul (1 / 2 : ℝ) hzero)
    have hlim' : Filter.Tendsto
        (fun n : ℕ => (volume E).toReal / 2 + (1 / 2 : ℝ) *
          (∫ x in E, Real.cos (2 * ((n : ℝ) * x + u n))))
        Filter.atTop (𝓝 ((volume E).toReal / 2)) := by
      simpa using hlim
    convert hlim' using 1
    ext n
    exact setIntegral_cos_sq_decomp E hE hsub u n
  constructor
  · intro f hf
    exact fourier_interval_integer_epsilon f hf
  · intro E hE hsub u
    exact tendsto_setIntegral_cos_sq E hE hsub u
