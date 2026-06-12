import Mathlib

open Set MeasureTheory

/--
Source definition bridge for `docs/source.tex`, theorem `line-17`.
The paper defines `g x = ∫ t in x..b, f t / t` only for `0 < x ≤ b`.
For Lean's total-function setting we use the zero-extension outside that source domain;
this does not change interval integrability or the interval integral over `[0,b]` except
at the null endpoint.
-/
noncomputable def intervalTailIntegral (f : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun x => if 0 < x ∧ x ≤ b then ∫ t in x..b, f t / t else 0

private lemma intervalTailIntegral_eq_tailKernel_setIntegral (b : ℝ) (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Set.Ioc 0 b) :
    intervalTailIntegral f b x =
      ∫ t in Set.Ioc 0 b, (if x ≤ t then f t / t else 0) := by
  have hxb : x ≤ b := hx.2
  have hxpos : 0 < x := hx.1
  unfold intervalTailIntegral
  rw [if_pos ⟨hxpos, hxb⟩]
  calc
    (∫ t in x..b, f t / t) = ∫ t in Set.Ioc x b, f t / t := by
      exact intervalIntegral.integral_of_le hxb
    _ = ∫ t in Set.Icc x b, f t / t := by
      exact (MeasureTheory.integral_Icc_eq_integral_Ioc (x := x) (y := b)
        (f := fun t : ℝ => f t / t) (μ := volume)).symm
    _ = ∫ t in Set.Ioc 0 b, (if x ≤ t then f t / t else 0) := by
      symm
      calc
        (∫ t in Set.Ioc 0 b, (if x ≤ t then f t / t else 0))
            = ∫ t in Set.Ioc 0 b,
                (Set.Ici x).indicator (fun t : ℝ => f t / t) t := by
                apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
                intro t ht
                by_cases hxt : x ≤ t <;> simp [Set.indicator, hxt]
        _ = ∫ t in Set.Ici x, f t / t ∂(volume.restrict (Set.Ioc 0 b)) := by
                rw [MeasureTheory.integral_indicator
                  (μ := volume.restrict (Set.Ioc 0 b)) (s := Set.Ici x)
                  (f := fun t : ℝ => f t / t) measurableSet_Ici]
        _ = ∫ t in (Set.Ici x ∩ Set.Ioc 0 b), f t / t := by
                simp [Measure.restrict_restrict measurableSet_Ici]
        _ = ∫ t in Set.Icc x b, f t / t := by
                have hset : Set.Ici x ∩ Set.Ioc 0 b = Set.Icc x b := by
                  ext t
                  constructor
                  · intro ht
                    exact ⟨ht.1, ht.2.2⟩
                  · intro ht
                    exact ⟨ht.1, ⟨lt_of_lt_of_le hxpos ht.1, ht.2⟩⟩
                rw [hset]

private lemma tailKernel_inner_intervalIntegral (b : ℝ) (f : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 b) :
    (∫ x in 0..b, (if x ≤ t then f t / t else 0)) = f t := by
  have htIcc : t ∈ Set.Icc 0 b := ⟨le_of_lt ht.1, ht.2⟩
  calc
    (∫ x in 0..b, (if x ≤ t then f t / t else 0))
        = ∫ x in 0..b, ({x : ℝ | x ≤ t}.indicator (fun _ : ℝ => f t / t)) x := by
            apply intervalIntegral.integral_congr
            intro x hx
            by_cases hxt : x ≤ t <;> simp [hxt]
    _ = ∫ x in 0..t, f t / t := by
            exact intervalIntegral.integral_indicator (μ := volume)
              (f := fun _ : ℝ => f t / t) htIcc
    _ = f t := by
            simp [intervalIntegral.integral_const, ht.1.ne']

private lemma tailKernel_norm_x_integral (b : ℝ) (f : ℝ → ℝ) {t : ℝ}
    (hb : 0 < b) (ht : t ∈ Set.Ioc 0 b) :
    (∫ x, ‖(if x ≤ t then f t / t else 0 : ℝ)‖
        ∂(volume.restrict (Set.Ioc 0 b))) = ‖f t‖ := by
  calc
    (∫ x, ‖(if x ≤ t then f t / t else 0 : ℝ)‖
        ∂(volume.restrict (Set.Ioc 0 b)))
        = ∫ x in Set.Ioc 0 b, (if x ≤ t then ‖f t‖ / t else 0) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with x
            by_cases hxt : x ≤ t
            · simp [hxt, norm_div, abs_of_pos ht.1]
            · simp [hxt]
    _ = ∫ x in 0..b, (if x ≤ t then ‖f t‖ / t else 0) := by
            rw [intervalIntegral.integral_of_le hb.le]
    _ = ‖f t‖ := by
            simpa using tailKernel_inner_intervalIntegral b (fun _ : ℝ => ‖f t‖) ht

private lemma tailKernel_integrable_prod (b : ℝ) (f : ℝ → ℝ)
    (hb : 0 < b) (hf : IntervalIntegrable f volume 0 b) :
    Integrable
      (Function.uncurry (fun (x : ℝ) (t : ℝ) => if x ≤ t then f t / t else 0))
      ((volume.restrict (Set.uIoc 0 b)).prod (volume.restrict (Set.Ioc 0 b))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 b)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfμ : Integrable f μ := by
    simpa [μ] using (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1 hf
  have hL : Integrable
      (fun p : ℝ × ℝ => if p.2 ≤ p.1 then f p.1 / p.1 else 0) (μ.prod μ) := by
    have hbase : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 / p.1) (μ.prod μ) := by
      have hfcomp : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1) (μ.prod μ) := by
        simpa using hfμ.aestronglyMeasurable.comp_fst (ν := μ)
      have hinv : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1)⁻¹) (μ.prod μ) := by
        exact (measurable_fst.inv).aestronglyMeasurable
      simpa [div_eq_mul_inv] using hfcomp.mul hinv
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := by
      exact measurableSet_le measurable_snd measurable_fst
    have hL_aesm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => if p.2 ≤ p.1 then f p.1 / p.1 else 0) (μ.prod μ) := by
      have h_ind := hbase.indicator hset
      simpa [Set.indicator] using h_ind
    refine (MeasureTheory.integrable_prod_iff hL_aesm).2 ?_
    constructor
    · filter_upwards [] with t
      have hconst : Integrable (fun _ : ℝ => f t / t) μ := by
        exact MeasureTheory.integrable_const (f t / t)
      have h_ind := hconst.indicator (measurableSet_Iic : MeasurableSet (Set.Iic t))
      simpa [Set.indicator, Set.Iic] using h_ind
    · have hnorm_ae :
          (fun t : ℝ => ∫ x, ‖(if x ≤ t then f t / t else 0 : ℝ)‖ ∂μ) =ᶠ[ae μ]
            (fun t : ℝ => ‖f t‖) := by
        dsimp [μ]
        filter_upwards [self_mem_ae_restrict (μ := volume) (s := Set.Ioc 0 b)
          measurableSet_Ioc] with t ht
        exact tailKernel_norm_x_integral b f hb ht
      exact hfμ.norm.congr hnorm_ae.symm
  have hK : Integrable (fun p : ℝ × ℝ => if p.1 ≤ p.2 then f p.2 / p.2 else 0)
      (μ.prod μ) := by
    exact (MeasureTheory.integrable_swap_iff (μ := μ) (ν := μ)
      (f := fun p : ℝ × ℝ => if p.1 ≤ p.2 then f p.2 / p.2 else 0)).1 (by
        simpa [Function.comp_def] using hL)
  simpa [μ, Function.uncurry, Set.uIoc_of_le hb.le] using hK

/--
Source theorem `line-17` (`intervalIntegrable_g_and_integral_g_eq_integral`).
Source proof: first prove the claim for nonnegative `f` by Tonelli/Fubini on the region
`0 ≤ x ≤ t ≤ b`, obtaining
`∫_0^b ∫_x^b f t / t dt dx = ∫_0^b (f t / t) * t dt = ∫_0^b f t dt`.
Since the last integral is finite, `g` is integrable.  Then apply the same argument to
positive and negative parts of a general integrable real function and use linearity.
Prover notes: use interval-integral congruence to ignore the zero-extension and the
endpoint `0`; the explicit hypothesis `0 < b` records the source's positive interval
convention.
-/
theorem intervalIntegrable_g_and_integral_g_eq_integral (b : ℝ) (f : ℝ → ℝ)
    (hb : 0 < b) (hf : IntervalIntegrable f volume 0 b) :
    IntervalIntegrable (intervalTailIntegral f b) volume 0 b ∧
      ∫ x in 0..b, intervalTailIntegral f b x = ∫ t in 0..b, f t := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 b)
  have hprod := tailKernel_integrable_prod b f hb hf
  have hpartial_int :
      IntervalIntegrable (fun x : ℝ => ∫ t, (if x ≤ t then f t / t else 0 : ℝ) ∂μ)
        volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2
    have h := hprod.integral_prod_left
    simpa [μ, Set.uIoc_of_le hb.le, Function.uncurry] using h
  have hbridge_restrict :
      (fun x : ℝ => ∫ t, (if x ≤ t then f t / t else 0 : ℝ) ∂μ)
        =ᶠ[ae (volume.restrict (Set.uIoc 0 b))] intervalTailIntegral f b := by
    rw [Set.uIoc_of_le hb.le]
    dsimp [μ]
    filter_upwards [self_mem_ae_restrict (μ := volume) (s := Set.Ioc 0 b)
      measurableSet_Ioc] with x hx
    exact (intervalTailIntegral_eq_tailKernel_setIntegral b f hx).symm
  constructor
  · exact hpartial_int.congr_ae hbridge_restrict
  · calc
      ∫ x in 0..b, intervalTailIntegral f b x
          = ∫ x in 0..b, ∫ t in Set.Ioc 0 b,
              (if x ≤ t then f t / t else 0 : ℝ) := by
              apply intervalIntegral.integral_congr_ae (μ := volume)
              filter_upwards [] with x hx
              have hxIoc : x ∈ Set.Ioc 0 b := by simpa [Set.uIoc_of_le hb.le] using hx
              exact intervalTailIntegral_eq_tailKernel_setIntegral b f hxIoc
      _ = ∫ t in Set.Ioc 0 b, ∫ x in 0..b,
            (if x ≤ t then f t / t else 0 : ℝ) := by
              simpa [Function.uncurry] using (MeasureTheory.intervalIntegral_integral_swap hprod)
      _ = ∫ t in Set.Ioc 0 b, f t := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
              intro t ht
              exact tailKernel_inner_intervalIntegral b f ht
      _ = ∫ t in 0..b, f t := by
              rw [intervalIntegral.integral_of_le hb.le]
