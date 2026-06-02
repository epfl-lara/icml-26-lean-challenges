import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.VectorBundle.Basic

open Bundle ContinuousMap Topology

theorem proj_homotopyEquiv {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
  [VectorBundle M E] : 
  IsHomotopyEquiv (Bundle.proj M E) := by sorry
