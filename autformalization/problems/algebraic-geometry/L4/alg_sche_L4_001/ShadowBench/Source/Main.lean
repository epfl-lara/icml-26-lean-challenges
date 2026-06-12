import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

open CategoryTheory

/--
A lightweight formal bridge for the phrase "`V = Spec B` is an affine open subset" in
`docs/source.tex` line 86.  The field `carrier` is the open subset of the ambient scheme,
`vanishingSet` is the chart-level interpretation of `V(I)`, and
`closed_subsets_are_vanishing` records the affine-scheme fact that chart-relative
closed subsets are cut out by ideals of `B`.
-/
structure AffineOpenModel (Y : AlgebraicGeometry.Scheme) (B : Type*) [CommRing B] where
  carrier : Set Y.carrier
  isOpen_carrier : IsOpen carrier
  vanishingSet : Ideal B → Set Y.carrier
  vanishingSet_subset_carrier : ∀ I : Ideal B, vanishingSet I ⊆ carrier
  closed_subsets_are_vanishing :
    ∀ S : Set Y.carrier,
      (∃ C : Set Y.carrier, IsClosed C ∧ S = carrier ∩ C) →
        ∃ I : Ideal B, S = vanishingSet I

/--
Source proof: The paper works locally on source and target, reduces to an affine map
`Spec B → Spec A` with `A` noetherian and `B` a finitely generated flat `A`-algebra,
then shows the image of each principal open is open.  The affine image is constructible
by Chevalley and stable under generalization by going-down for flat finite-type maps,
so it is open in the noetherian target.
Prover notes: Mathlib has `AlgebraicGeometry.UniversallyOpen.of_flat`, stating that a
flat morphism locally of finite presentation is universally open, and
`AlgebraicGeometry.Scheme.Hom.isOpenMap`.  In this draft, finite type is represented by
local finite type plus quasi-compactness; over a noetherian target, the local finite
type part is locally of finite presentation by
`AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType`.
-/
theorem flat_is_open {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] :
    IsOpenMap f.base := by
  exact AlgebraicGeometry.Scheme.Hom.isOpenMap f

/--
Source proof: By `flat_is_open`, the morphism is an open map; applying the definition of
`IsOpenMap` to the open subset `U` gives that `f(U)` is open in the target.
Prover notes: After invoking `flat_is_open f`, this should reduce to applying the
resulting `IsOpenMap` hypothesis to `hU`.
-/
theorem flat_open_image {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f]
    (U : Set X.carrier) (hU : IsOpen U) :
    IsOpen (f.base '' U) := by
  exact (flat_is_open f) U hU

/--
Source proof: The cited openness theorem makes `f(U) ∩ V` open in the affine open chart
`V`; its complement inside `V` is therefore relatively closed, and closed subsets of
`Spec B` are of the form `V(I)` for an ideal `I ⊆ B`.  The source statement omits the
finite-type/noetherian hypotheses needed to invoke the cited openness theorem; the Lean
statement records this proof-compatible strengthening, with finite type represented by
local finite type plus quasi-compactness.
Prover notes: The Lean statement uses `AffineOpenModel` to carry the affine-open chart
and its relative closed-subset/ideal dictionary.  First obtain openness of `f.base '' U`
from `flat_open_image`, express `V.carrier \\ (f.base '' U ∩ V.carrier)` as the
intersection of `V.carrier` with the closed complement of `f.base '' U`, then apply
`V.closed_subsets_are_vanishing`.
-/
theorem flat_morphism_complement_of_image_is_closed
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f]
    (U : Set X.carrier) (hU : IsOpen U)
    {B : Type*} [CommRing B] (V : AffineOpenModel Y B) :
    ∃ I : Ideal B, V.carrier \ (f.base '' U ∩ V.carrier) = V.vanishingSet I := by
  exact V.closed_subsets_are_vanishing _ ⟨(f.base '' U)ᶜ,
    (flat_open_image f U hU).isClosed_compl, by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1, by
          intro hyImage
          exact hy.2 ⟨hyImage, hy.1⟩⟩
      · intro hy
        exact ⟨hy.1, by
          intro hyInter
          exact hy.2 hyInter.1⟩⟩
