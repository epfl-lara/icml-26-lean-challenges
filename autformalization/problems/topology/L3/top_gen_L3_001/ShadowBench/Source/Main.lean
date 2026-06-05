import Mathlib.Topology.Homotopy.HomotopyGroup

open scoped unitInterval Topology Topology.Homotopy
open Homeomorph

noncomputable section

variable {N X : Type*} [DecidableEq N] [TopologicalSpace X] {x : X}

/--
Source definition `homotopyTo` (`docs/source.tex`, lines 17-42).
For a generalized `N`-loop `p : Ω^ N X x`, insert the coordinate `t : I` in
position `i` using `Cube.insertAt i`, obtaining a based loop in the generalized
loop space over the deleted-coordinate subtype `{j // j ≠ i}`. The source states
`N` is finite; Mathlib's construction works for any decidable index type, which
covers the finite source case.
-/
def homotopyTo (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j ≠ i } X x) GenLoop.const :=
  GenLoop.toLoop i p

/--
Source theorem `homotopyTo_apply` (`docs/source.tex`, lines 44-68).
Source proof: the source checks that fixed-`t` slices preserve the deleted-coordinate
boundary, and that the slices at `t = 0` and `t = 1` are the constant generalized
loop, because `Cube.insertAt i` sends those points into `Cube.boundary N`.
Prover notes: unfold `homotopyTo`; this is the pointwise formula for
`GenLoop.toLoop`, with well-definedness already encoded in the codomain.
-/
theorem homotopyTo_apply (i : N) (p : Ω^ N X x) (t : I) (y : I^{ j // j ≠ i }) :
    homotopyTo i p t y = p (Cube.insertAt i (t, y)) := by
  sorry

/--
Source theorem `homotopicTo` (`docs/source.tex`, lines 73-161).
Source proof: identify `I^N` with `I × I^{N \ {i}}` using `Cube.splitAt i` and
`Cube.insertAt i`; uncurry a path homotopy between `homotopyTo i p` and
`homotopyTo i q` to a map `I × I^N → X`; the boundary is fixed either because the
`i`-coordinate is `0` or `1`, or because the remaining coordinates lie in the
boundary of the deleted cube. Endpoints reduce to the defining formula for
`homotopyTo`.
Prover notes: Mathlib contains this converse as `GenLoop.homotopicFrom`; after
unfolding `homotopyTo`, `simpa [homotopyTo] using GenLoop.homotopicFrom (i := i) H`
should be the direct route.
-/
theorem homotopicTo (i : N) {p q : Ω^ N X x}
    (H : (homotopyTo i p).Homotopic (homotopyTo i q)) :
    GenLoop.Homotopic p q := by
  sorry
