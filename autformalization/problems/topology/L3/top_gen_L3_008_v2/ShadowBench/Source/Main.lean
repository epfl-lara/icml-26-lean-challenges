import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting

open Topology unitInterval

/--
Source theorem `docs/source.tex`, line-17.
Source proof: choose paths from the basepoint and define the lift by the endpoint of the
lifted path. The fundamental-group range hypothesis proves independence of this choice by
lifting a homotopy between loops through the covering map. Local path connectedness gives
small path-connected neighborhoods on which the lift is the local inverse of `p`, hence is
continuous. Uniqueness follows from uniqueness of path lifting.
Prover notes: this is Mathlib's covering-space lifting criterion. The source inclusion
`f_* π₁(A,a₀) ⊆ p_* π₁(E,e₀)` is formalized as the range inclusion
`(FundamentalGroup.map f a₀).range ≤ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he₀).range`;
the source's second inclusion is represented by the codomain of `mapOfEq`.
-/
theorem existsUnique_continuousMap_lifts_of_range_le
    {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    {p : E → X} (hp : IsCoveringMap p)
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he₀ : p e₀ = f a₀)
    (hπ₁ : (FundamentalGroup.map f a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he₀).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  exact hp.existsUnique_continuousMap_lifts_of_range_le he₀ hπ₁
