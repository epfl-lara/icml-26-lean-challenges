import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton

open scoped unitInterval Topology
open Homeomorph

/-- 
Definition of the space of generalized N-loops in a topological space X based at point x.
This is the space Ω^N(X,x) of continuous maps from the N-dimensional unit cube I^N to X
that map the boundary of I^N to the basepoint x, equipped with the compact-open topology.
-/
noncomputable def setoid (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ) : Type* := 
  {f : C(Π i : Fin N, unitInterval, X) // 
    ∀ (y : Π i : Fin N, unitInterval), 
      (∃ i : Fin N, y i = 0 ∨ y i = 1) → f y = x}

/-- 
With respect to the compact-open topology on Ω^N(X,x), the evaluation map
is continuous.
-/
theorem evaluation_map_continuous (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ) :
  Continuous (fun (p : setoid X x N × (Π i : Fin N, unitInterval)) => 
    (p.1 : C(Π i : Fin N, unitInterval, X)) p.2) := by sorry

/--
For each fixed y ∈ I^N, the map f ↦ f(y) from Ω^N(X,x) to X is continuous.
-/
theorem fixed_point_evaluation_continuous (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ) 
  (y : Π i : Fin N, unitInterval) :
  Continuous (fun (f : setoid X x N) => (f : C(Π i : Fin N, unitInterval, X)) y) := by sorry
