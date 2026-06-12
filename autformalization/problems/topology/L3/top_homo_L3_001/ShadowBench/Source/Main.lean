import Mathlib.Topology.Homotopy.HomotopyGroup

open scoped unitInterval Topology
open Homeomorph

noncomputable section

universe u v

/--
Source `docs/source.tex`, line-17 (`isUnital_auxGroup`).  The source defines, for a
finite index set `N`, the auxiliary group structure on `π_N(X,x)` obtained by viewing
`N`-loops as loops of `(N \ {i})`-loops and transporting ordinary loop concatenation in
the `i`-direction.

Here `HomotopyGroup N X x` is Mathlib's model of `π_N(X,x)`, and
`HomotopyGroup.auxGroup i` is Mathlib's completed construction of the transported group
structure.  The declaration keeps the source-required name `isUnital_auxGroup`; the
canonical Mathlib name of the underlying construction is `HomotopyGroup.auxGroup`.
-/
noncomputable abbrev isUnital_auxGroup
    (X : Type u) [TopologicalSpace X] (N : Type v) [Fintype N] (x : X) (i : N) :
    Group (HomotopyGroup N X x) := by
  classical
  exact HomotopyGroup.auxGroup (X := X) (x := x) i

/--
Source `docs/source.tex`, line-28 (`auxGroup_indep`).  The source says that for
`i,j ∈ N`, the groups obtained from coordinate-`i` and coordinate-`j` concatenation are
isomorphic; its proof then shows the stronger statement that the two group structures on
the same set `π_N(X,x)` coincide.

Source proof / Prover notes: split the case `i = j`; otherwise use the two unital
operations with common unit `[c]`, prove the interchange law by the grid homotopy for
concatenating in the independent `i`- and `j`-directions, and apply the Eckmann--Hilton
argument.  In Mathlib this argument is already packaged as
`HomotopyGroup.auxGroup_indep`, using `HomotopyGroup.isUnital_auxGroup`,
`EckmannHilton.mul`, and `transAt_distrib`.  A later proof pass should unfold
`isUnital_auxGroup` and close this from `HomotopyGroup.auxGroup_indep`.
-/
theorem auxGroup_indep
    (X : Type u) [TopologicalSpace X] (N : Type v) [Fintype N] (x : X) (i j : N) :
    (isUnital_auxGroup X N x i : Group (HomotopyGroup N X x)) =
      isUnital_auxGroup X N x j := by
  classical
  simpa [isUnital_auxGroup] using HomotopyGroup.auxGroup_indep (X := X) (x := x) i j
