import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.VectorBundle.Basic

open Bundle ContinuousMap Topology

/--
Source proof: choose the zero section as homotopy inverse to the bundle projection. The
projection after the zero section is the identity on the base, and the composite in the total
space is homotopic to the identity by fiberwise scalar multiplication `H(v,t)=t • v`.
Prover notes: construct a `ContinuousMap.HomotopyEquiv` whose forward map is `π F E` and whose
inverse is `Bundle.zeroSection F E`; prove the endpoint equations with `Bundle.zeroSection_proj`
and the vector-space identities `zero_smul` and `one_smul` after establishing continuity of the
fiberwise scaling homotopy in local trivializations.
-/
theorem proj_homotopyEquiv
    {M F : Type*} {E : M → Type*}
    [TopologicalSpace M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
    [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (Bundle.TotalSpace F E)]
    [FiberBundle F E] [VectorBundle ℝ F E] :
    ∃ h : ContinuousMap.HomotopyEquiv (Bundle.TotalSpace F E) M,
      h.toFun =
        { toFun := π F E
          continuous_toFun := FiberBundle.continuous_proj F E } := by
  sorry
