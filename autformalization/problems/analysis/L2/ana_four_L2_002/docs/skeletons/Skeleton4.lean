import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

lemma ABM_analysis_L2_ana_four_L2_002_item_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {μ : Measure V} {f : V → E} (hf : Integrable f μ) (w : V)
    {g : V → E} (hg : Integrable g μ) (v : V) :
    Integrable (fun x ↦ cexp (-2 * π * I * ⟪w, x⟫_ℝ) • f x) μ ∧
    Integrable (fun w' ↦ cexp (2 * π * I * ⟪w', v⟫_ℝ) • g w') μ := by sorry

lemma tendsto_integral_cexp_sq_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {μ : Measure V} (f : V → E) (hf : Integrable f μ) :
    Tendsto (fun c : ℝ ↦ ∫ v, Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v ∂μ) atTop (𝓝 (∫ v, f v ∂μ)) := by sorry
