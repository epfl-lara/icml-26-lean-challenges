import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

open CategoryTheory Topology
open AlgebraicGeometry

/--
Source theorem `line-17` (`docs/source.tex`): if `f : X → Y` is a morphism of schemes
of finite presentation, then the image of a locally constructible subset of `X` is locally
constructible in `Y`.

Source proof: reduce local constructibility on the target to affine opens, use quasi-compactness
to reduce the source to finitely many affine opens, then reduce to the affine Chevalley theorem
for spectra of finitely presented algebras via polynomial presentations. The affine proof cuts
`Spec R` into `V(c)` and `D(c)`, inducts on the number and degrees of defining polynomials, and
handles the bases `D(f) ∩ V(g)` by a characteristic-polynomial/nilpotence argument and `D(f)` by
checking nonvanishing of coefficients after passing to residue fields.

Prover notes: Mathlib represents a scheme morphism "of finite presentation" by the two hypotheses
`[LocallyOfFinitePresentation f] [QuasiCompact f]`. The proof should use
`AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image`.
-/
theorem locallyOfFinitePresentation_isStableUnderBaseChange
    {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    {E : Set X} (hE : IsLocallyConstructible E) :
    IsLocallyConstructible (f '' E) := by
  sorry
