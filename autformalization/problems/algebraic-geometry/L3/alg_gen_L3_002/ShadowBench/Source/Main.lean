import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/--
Being an open immersion satisfies fpqc descent.

Source proof (docs/source.tex, theorem line 17; proof lines 19-30): after an fpqc
base change is an open immersion, the base-changed morphism is universally open
and universally injective, hence the original morphism is too and has open image.
On each affine open in this image, pull back to the fpqc affine cover and reduce
to descent of an isomorphism. In the isomorphism case the source proof shows the
morphism is a homeomorphism, hence affine, and then uses faithful flat descent on
global sections to identify the coordinate rings.

Prover notes: this is the Mathlib `MorphismProperty.DescendsAlong` encoding of
“satisfies fpqc descent”, with fpqc represented by
`@Surjective ⊓ @Flat ⊓ @QuasiCompact`. The proof should follow the existing
fpqc-descent argument for open immersions: use descent of universal openness and
universal injectivity, restrict to the open range via `IsOpenImmersion.lift`,
reduce to fpqc descent for isomorphisms, then compose with the open immersion of
the image.
-/
theorem descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact' :
    IsOpenImmersion.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  sorry

end AlgebraicGeometry

export AlgebraicGeometry (descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact')
