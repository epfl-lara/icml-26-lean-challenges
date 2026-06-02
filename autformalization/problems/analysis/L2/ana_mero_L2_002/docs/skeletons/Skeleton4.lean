import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp

open Filter Topology

theorem min_divisor_le_divisor_add {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {U : Set 𝕜} {f₁ f₂ : 𝕜 → E}
    (hf₁ : ∀ z ∈ U, IsMeromorphicAt f₁ z)
    (hf₂ : ∀ z ∈ U, IsMeromorphicAt f₂ z)
    {z : 𝕜} (hz : z ∈ U)
    (h_fin : OrderAt (f₁ + f₂) z ≠ ⊤) :
    min (divisor 𝕜 E U f₁ z) (divisor 𝕜 E U f₂ z) ≤ divisor 𝕜 E U (f₁ + f₂) z := by sorry
