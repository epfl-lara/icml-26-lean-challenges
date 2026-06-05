import Mathlib

open CategoryTheory Opposite
open TopologicalSpace
open AlgebraicGeometry

/--
Source theorem `line-17` (`isAffineOpen_inf_preimage`) from `docs/source.tex`:
if `Y` is a separated scheme, `f : X ⟶ Y` is a morphism, `U` is an affine open of `X`,
and `V` is an affine open of `Y`, then `U ∩ f^{-1}(V)` is affine.

Source proof: let `p₁,p₂` be the projections from `X ×_ℤ Y`. Identify
`U ∩ f^{-1}(V)` with the image under `p₁` of the graph of `f` intersected with
`p₁^{-1}(U) ∩ p₂^{-1}(V)`. The latter ambient open is the affine scheme
`U ×_ℤ V`; separatedness of `Y` makes the graph closed, so this intersection is a
closed subscheme of an affine scheme and hence affine. Finally transfer affineness back along
the graph immersion.

Prover notes: Mathlib encodes affine opens as `IsAffineOpen`, scheme separatedness as
`[Y.IsSeparated]`, inverse image of opens as `f ⁻¹ᵁ V`, and intersection as `⊓`. Search first
for existing affine-open/intersection lemmas around `IsAffineOpen.inf`, `IsSeparated`, and graph
closed-immersion infrastructure before expanding the source graph argument.
-/
theorem isAffineOpen_inf_preimage {X Y : Scheme} [Y.IsSeparated] (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ f ⁻¹ᵁ V) := by
  sorry
