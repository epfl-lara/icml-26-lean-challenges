import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting

open Topology unitInterval

/--
Source proof: choose paths from `a₀` to each point of `A`, lift their images under `f`
through the covering map starting at `e₀`, and define `F` by the lifted endpoint.  The
fundamental-group range inclusion shows the endpoint is independent of the path by comparing
the loop `γ` followed by the reverse of `γ'` with a loop in `E`; covering homotopy/path-lift
uniqueness then identifies the endpoints.  Continuity is local on evenly covered
neighborhoods, using local path connectedness of `A`, and uniqueness follows because any
other lift sends each path from `a₀` to its unique lifted path.

Prover notes: this is the lifting criterion.  Mathlib contains the matching theorem
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`; after statement/source review,
a direct application of `hp.existsUnique_continuousMap_lifts_of_range_le he hle` should close
this skeleton.
-/
theorem existsUnique_continuousMap_lifts_of_range_le
    {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    {p : E → X} (hp : IsCoveringMap p)
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (hle : (FundamentalGroup.map f a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  exact hp.existsUnique_continuousMap_lifts_of_range_le he hle
