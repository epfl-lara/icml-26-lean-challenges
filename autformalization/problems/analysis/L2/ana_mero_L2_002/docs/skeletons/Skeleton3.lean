import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp

open Filter Topology

-- Working with meromorphic functions on complex field
variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

-- A type class for meromorphic functions
class IsMeromorphicOn (f : 𝕜 → E) (U : Set 𝕜) : Prop

-- Divisor/order function for meromorphic functions
def div_U {f : 𝕜 → E} {U : Set 𝕜} [h : IsMeromorphicOn f U] (z : 𝕜) : WithTop ℕ := by sorry

theorem min_divisor_le_divisor_add {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
  (h_mero₁ : IsMeromorphicOn f₁ U)
  (h_mero₂ : IsMeromorphicOn f₂ U)
  (hz : z ∈ U)
  (h_finite : (div_U (f₁ + f₂) z).IsSome) :
  min (div_U f₁ z) (div_U f₂ z) ≤ div_U (f₁ + f₂) z := by sorry
