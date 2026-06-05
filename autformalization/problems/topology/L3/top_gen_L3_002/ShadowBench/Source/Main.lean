import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
ShadowBench problem: `topology/L3/top_gen_L3_002`.

This draft follows `docs/source.tex` and uses Mathlib's existing implementation
of generalized loops and higher homotopy groups. See
`ShadowBench/Source/Blueprint.md` for the source map and fidelity notes.
-/

open scoped unitInterval Topology
open Homeomorph

noncomputable section

/--
Source definition `isUnital_auxGroup` (docs/source.tex, lines 17--25): for a
topological space `X`, finite index type `N`, basepoint `x`, and coordinate
`i : N`, the source defines the auxiliary group on
`π_N(X,x) = Ω^N(X,x) / ≃_{∂ I^N}` whose multiplication is transported from
ordinary loop concatenation after viewing an `N`-loop as a loop of
`(N \ {i})`-loops.

Lean coverage: `HomotopyGroup N X x` is Mathlib's quotient of generalized
`N`-loops by relative homotopy, and `HomotopyGroup.auxGroup i` is precisely the
auxiliary group structure induced by the `i`-direction loop equivalence. The
source label is retained as the top-level abbreviation name required by the
problem instructions.
-/
@[reducible]
def isUnital_auxGroup (X : Type*) [TopologicalSpace X] (x : X)
    (N : Type*) [Fintype N] (i : N) :
    Group (HomotopyGroup N X x) := by
  classical
  exact HomotopyGroup.auxGroup (X := X) (x := x) i

/--
Source theorem `auxGroup_indep` (docs/source.tex, lines 28--70): for indices
`i,j ∈ N`, the auxiliary groups obtained by concatenating generalized loops in
the `i`- and `j`-directions are isomorphic. The Lean statement records the
stronger equality of the two group structures on the common carrier
`HomotopyGroup N X x`, matching the source proof's final conclusion that the
group structures coincide.

Source proof / prover notes: if `i = j`, rewrite. Otherwise use the
Eckmann--Hilton argument for the two unital operations with common unit given by
the constant loop class. The interchange law comes from the standard grid
homotopy comparing horizontal-then-vertical and vertical-then-horizontal
concatenation in the `(i,j)` square. After statement review, Mathlib's theorem
`HomotopyGroup.auxGroup_indep` should close the proof with
`simpa [isUnital_auxGroup] using HomotopyGroup.auxGroup_indep (X := X) (x := x) i j`.
-/
theorem auxGroup_indep (X : Type*) [TopologicalSpace X] (x : X)
    (N : Type*) [Fintype N] (i j : N) :
    (isUnital_auxGroup X x N i : Group (HomotopyGroup N X x)) =
      isUnital_auxGroup X x N j := by
  classical
  simpa [isUnital_auxGroup] using
    HomotopyGroup.auxGroup_indep (X := X) (x := x) i j
