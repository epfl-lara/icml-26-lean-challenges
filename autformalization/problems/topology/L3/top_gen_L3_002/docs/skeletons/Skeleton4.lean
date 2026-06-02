import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton

open scoped unitInterval Topology
open Homeomorph

/-- The N-fold iterated loop space Ω^N(X,x) -/
def IteratedLoopSpace (N : Type*) [Fintype N] (X : Type*) [TopologicalSpace X] (x : X) : Type* := by sorry

/-- 
The quotient π_N(X,x) = Ω^N(X,x)/≃_∂I^N is the set of homotopy classes 
of N-loops relative to the boundary.
-/
def PiNQuotient (N : Type*) [Fintype N] (X : Type*) [TopologicalSpace X] (x : X) : Type* := by sorry

/-- 
For fixed i∈N, there is a map that identifies N-loops as "loops of (N\{i})-loops":
toLoop_i : Ω^N(X,x) → Ω(Ω^(N\{i})(X,x), const)
-/
def toLoop_i (N : Type*) [Fintype N] (X : Type*) [TopologicalSpace X] (x : X) (i : N) :
  IteratedLoopSpace N X x → IteratedLoopSpace (N \ {i}) (IteratedLoopSpace (N \ {i}) X x) (fun _ => x) := by sorry

/-- 
The definition `isUnital_auxGroup`: For a topological space X and a finite index set N,
let π_N(X,x) be the set of homotopy classes relative to the boundary. 
For fixed i∈N, there is an induced binary operation *_i on π_N(X,x) obtained by 
transporting the usual loop concatenation in the i-direction. 
We define `auxGroup(i)` to be the group whose underlying set and binary operation 
are π_N(X,x) and *_i, respectively.
-/
def auxGroup (N : Type*) [Fintype N] (X : Type*) [TopologicalSpace X] (x : X) (i : N) : 
  Group (PiNQuotient N X x) := by sorry

/-- 
Let X be a topological space and N be a finite index set. 
Then for any i,j∈N, the groups `auxGroup(i)` and `auxGroup(j)` are isomorphic.
-/
theorem auxGroup_indep (N : Type*) [Fintype N] (X : Type*) [TopologicalSpace X] (x : X) (i j : N) :
  -- auxGroup(i) and auxGroup(j) are isomorphic as groups
  sorry
:= by sorry

-- Missing declaration stub
theorem isUnital_auxGroup : True := by sorry
