import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp

open Filter Topology

/-- The divisor of a function on a set. -/
noncomputable def divisor (K : Type*) [NontriviallyNormedField K]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (U : Set K) (f : K → E) : K → ℤ := sorry

/-- The support of the divisor function. -/
noncomputable def divisor_support (K : Type*) [NontriviallyNormedField K]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (U : Set K) (f : K → E) : Set K :=
      {z ∈ U | divisor K E U f z ≠ 0}

/-- If f is meromorphic on U, then the support of divisor_U(f) is locally finite in U. -/
theorem divisor_support_locally_finite (K : Type*) [NontriviallyNormedField K]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (U : Set K) (f : K → E)
    (hf : ∀ z ∈ U, IsMeromorphicAt f z) :
    ∀ x ∈ U, ∃ V : Set K, IsOpen V ∧ x ∈ V ∧
    Finite {z ∈ U | divisor K E U f z ≠ 0 ∧ z ∈ V} := by sorry
