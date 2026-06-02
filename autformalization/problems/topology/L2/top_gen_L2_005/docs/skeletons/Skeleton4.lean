import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton

open scoped unitInterval Topology
open Homeomorph

def setoid (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ) : Type _ :=
  { f : C(Fin N → unitInterval, X) // ∀ y, (∃ i : Fin N, y i = 0 ∨ y i = 1) → f y = x }

def ev (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ) :
    setoid X x N × (Fin N → unitInterval) → X :=
  fun p => p.1.val p.2

theorem continuous_ev (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ) :
    Continuous (ev X x N) := by sorry

theorem continuous_ev_at (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ)
    (y : Fin N → unitInterval) :
    Continuous (fun f : setoid X x N => f.val y) := by sorry
