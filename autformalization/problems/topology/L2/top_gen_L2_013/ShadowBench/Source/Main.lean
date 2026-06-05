import Mathlib.Topology.Sheaves.LocallySurjective

open CategoryTheory
open TopologicalSpace
open Opposite
open scoped AlgebraicGeometry

universe u

/-- Source definition `line-17`: a morphism of type-valued presheaves is locally surjective if every
section over an open set, near every point of that open set, is locally in the image after shrinking
to a smaller open neighborhood. Lean represents open sets as `Opens X` and the restriction `t|_V` as
`G.map (homOfLE hVU).op t`. -/
def IsLocallySurjective {X : TopCat} {F G : X.Presheaf (Type u)} (T : F ⟶ G) : Prop :=
  ∀ (U : Opens X) (t : G.obj (op U)) (x : X), x ∈ U →
    ∃ (V : Opens X) (hVU : V ≤ U),
      (∃ (s : F.obj (op V)), T.app (op V) s = G.map (homOfLE hVU).op t) ∧ x ∈ V

/-- Source theorem `line-21`.
Source proof: a germ represented by a section over an open neighborhood lifts after shrinking by
local surjectivity; conversely, a stalk preimage of the germ of a section can be represented on some
neighborhood, and equality of germs gives a further neighborhood where the two restrictions agree.
Prover notes: compare this pointwise definition with `TopCat.Presheaf.isLocallySurjective_iff`, then
use `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`; the source proof uses
`germ_exist`, `germ_eq`, and functoriality of restriction maps. -/
theorem locally_surjective_iff_surjective_on_stalks {X : TopCat} {F G : X.Presheaf (Type u)}
    (T : F ⟶ G) :
    IsLocallySurjective T ↔
      ∀ x : X, Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map T) := by
  sorry
