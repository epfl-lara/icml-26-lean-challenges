import Mathlib.Order.KrullDimension
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds

open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  Order.krullDim (IrreducibleCloseds T)

theorem IsInducing.topologicalKrullDim_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : IsInducing f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by sorry

theorem IsHomeomorph.topologicalKrullDim_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y := by sorry

theorem topologicalKrullDim_subspace_le {X : Type*} [TopologicalSpace X] (s : Set X) :
    topologicalKrullDim s ≤ topologicalKrullDim X := by sorry
