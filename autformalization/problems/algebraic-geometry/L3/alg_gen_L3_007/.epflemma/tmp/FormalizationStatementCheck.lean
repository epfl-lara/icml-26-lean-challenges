import Mathlib
import Aesop

open AlgebraicGeometry
open Topology

/-- Test statement for the ShadowBench source theorem. -/
theorem isDominant_iff_forall_genericPoints_mem_fiber_check
    {X Y : Scheme} (f : X ⟶ Y) (hf : QuasiCompact f) :
    IsDominant f ↔ ∀ y : Y, y ∈ genericPoints Y → ∃ x : X, x ∈ genericPoints X ∧ f x = y := by
  sorry
