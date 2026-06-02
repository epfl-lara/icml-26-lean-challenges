import Mathlib
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

open Set Filter Topology Metric Real

/-- Given a differential operator L and a function u, defines Lu as specified in the problem -/
noncomputable def Lu {n : ℕ} 
    (a : Fin n → Fin n → (EuclideanSpace ℝ (Fin n) → ℝ))
    (b : Fin n → (EuclideanSpace ℝ (Fin n) → ℝ))
    (c : EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) 
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := 
  (∑ i : Fin n, ∑ j : Fin n, (a i j x) * ((iteratedFderiv ℝ 2 u) (Pi.single i 1) (Pi.single j 1) x)) +
  (∑ i : Fin n, (b i x) * ((fderiv ℝ u) (Pi.single i 1) x)) + (c x) * (u x)

/-- If Lu > 0 in Ω and c ≤ 0, then u cannot attain a nonnegative maximum in the interior -/
lemma no_interior_max_of_Lu_pos {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ_bounded : Bornology.IsBounded Ω)
    (hΩ_connected : IsConnected Ω)
    (a : Fin n → Fin n → (EuclideanSpace ℝ (Fin n) → ℝ))
    (b : Fin n → (EuclideanSpace ℝ (Fin n) → ℝ))
    (c : EuclideanSpace ℝ (Fin n) → ℝ)
    (ha_cont : ∀ i j, Continuous (a i j))
    (hb_cont : ∀ i, Continuous (b i))
    (hc_cont : Continuous c)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu_C2 : ContDiff ℝ 2 u)
    (hu_cont : ContinuousOn u (closure Ω))
    (hL_pos : ∀ x ∈ Ω, Lu a b c u x > 0)
    (hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (hmax : ∃ M : ℝ, (∀ x ∈ closure Ω, u x ≤ M) ∧ 
      (∃ x₀ ∈ closure Ω, u x₀ = M) ∧ u x₀ ≥ 0) :
    ¬∃ x ∈ Ω, (∀ y ∈ closure Ω, u y ≤ u x) ∧ u x ≥ 0 := by sorry

/-- If Lu > 0 in Ω and c ≤ 0, then u attains its nonnegative maximum on the boundary of Ω -/
theorem main_theorem {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ_bounded : Bornology.IsBounded Ω)
    (hΩ_connected : IsConnected Ω)
    (a : Fin n → Fin n → (EuclideanSpace ℝ (Fin n) → ℝ))
    (b : Fin n → (EuclideanSpace ℝ (Fin n) → ℝ))
    (c : EuclideanSpace ℝ (Fin n) → ℝ)
    (ha_cont : ∀ i j, Continuous (a i j))
    (hb_cont : ∀ i, Continuous (b i))
    (hc_cont : Continuous c)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu_C2 : ContDiff ℝ 2 u)
    (hu_cont : ContinuousOn u (closure Ω))
    (hL_pos : ∀ x ∈ Ω, Lu a b c u x > 0)
    (hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (hmax : ∃ M : ℝ, (∀ x ∈ closure Ω, u x ≤ M) ∧ 
      (∃ x₀ ∈ closure Ω, u x₀ = M) ∧ u x₀ ≥ 0) :
    ∃ x ∈ frontier Ω, (∀ y ∈ closure Ω, u y ≤ u x) ∧ u x ≥ 0 := by sorry
