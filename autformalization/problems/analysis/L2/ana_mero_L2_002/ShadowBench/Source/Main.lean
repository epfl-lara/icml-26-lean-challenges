import Mathlib.Analysis.Meromorphic.Divisor

open Filter Topology

/--
Source proof: The paper reduces divisor values to meromorphic orders, with the convention that
infinite order contributes `0`; the nontrivial finite-order case uses the standard inequality
`min (ord_z f₁) (ord_z f₂) ≤ ord_z (f₁ + f₂)`.

Prover notes: rewrite the three divisor values using `MeromorphicOn.divisor_apply` at `hz`, derive
pointwise meromorphicity from `hf₁ z hz` and `hf₂ z hz`, apply `meromorphicOrderAt_add`, and handle
`WithTop.untop₀`/`⊤` cases using the finite-order hypothesis for the sum.
-/
theorem min_divisor_le_divisor_add {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {U : Set 𝕜} {f₁ f₂ : 𝕜 → E} {z : 𝕜}
    (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U)
    (hz : z ∈ U) (h_fin : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
    min (MeromorphicOn.divisor f₁ U z) (MeromorphicOn.divisor f₂ U z) ≤
      MeromorphicOn.divisor (f₁ + f₂) U z := by
  rw [MeromorphicOn.divisor_apply hf₁ hz,
    MeromorphicOn.divisor_apply hf₂ hz,
    MeromorphicOn.divisor_apply (hf₁.add hf₂) hz]
  set A : WithTop ℤ := meromorphicOrderAt f₁ z
  set B : WithTop ℤ := meromorphicOrderAt f₂ z
  set C : WithTop ℤ := meromorphicOrderAt (f₁ + f₂) z
  have hCfin : C ≠ ⊤ := by simpa [C] using h_fin
  have hle : min A B ≤ C := by
    simpa [A, B, C] using meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)
  by_cases hA : A = ⊤
  · by_cases hB : B = ⊤
    · have htop : (⊤ : WithTop ℤ) ≤ C := by simpa [hA, hB] using hle
      exact (hCfin (top_le_iff.mp htop)).elim
    · have hleB : B ≤ C := by simpa [hA] using hle
      exact le_trans (min_le_right A.untop₀ B.untop₀)
        (WithTop.untop₀_le_untop₀ hCfin hleB)
  · by_cases hB : B = ⊤
    · have hleA : A ≤ C := by simpa [hB] using hle
      exact le_trans (min_le_left A.untop₀ B.untop₀)
        (WithTop.untop₀_le_untop₀ hCfin hleA)
    · have hmain : (min A B).untop₀ ≤ C.untop₀ := WithTop.untop₀_le_untop₀ hCfin hle
      simpa [WithTop.untop₀_min hA hB] using hmain
