import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open MeasureTheory Real Complex Set NNReal Filter Topology

theorem integral_cos_sq_tendsto_half_measure {E : Set ℝ} (hE : MeasurableSet E) (hE' : E ⊆ Icc 0 (2 * π))
    (u : ℕ → ℝ) :
    Tendsto (fun n => ∫ x in E, (cos ((n : ℝ) * x + u n)) ^ 2) atTop (𝓝 ((volume E).toReal / 2)) := by sorry
