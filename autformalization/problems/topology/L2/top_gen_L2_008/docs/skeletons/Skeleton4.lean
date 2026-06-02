import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.CategoryTheory.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit

open CategoryTheory
open ContinuousMap
open scoped ContinuousMap

def paths_homotopic (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty (FundamentalGroupoid X ≌ CategoryTheory.Discrete PUnit)

theorem simply_connected_iff_paths_homotopic (X : Type*) [TopologicalSpace X] :
  paths_homotopic X ↔ (IsPathConnected X ∧ ∀ (x y : X) (p q : Path x y), p.Homotopic q) := by sorry
