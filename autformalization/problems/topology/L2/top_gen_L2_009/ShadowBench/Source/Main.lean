import Mathlib.Topology.Sheaves.Sheafify

open TopCat Opposite TopologicalSpace CategoryTheory

universe v

noncomputable section

/--
Source `docs/source.tex`, lines 17-23 (`stalkToFiber_injective`).
The source defines the sheafification of a set-valued presheaf as the sheaf of
families in the product of stalks that are locally equal to germs of original
sections. Mathlib already implements exactly this construction as
`TopCat.Presheaf.sheafify`; this top-level definition preserves the
source-required declaration name.
-/
def stalkToFiber_injective {X : TopCat.{v}} (F : Presheaf (Type v) X) : Sheaf (Type v) X :=
  F.sheafify

/--
Source `docs/source.tex`, lines 25-49 (`sheafifyStalkIso`).
Source proof: surjectivity sends a germ `(U, s) ∈ F_x` to the section of the
sheafification over `U` whose value at `y` is the germ `s_y`; evaluation at `x`
recovers `(U, s)`. For injectivity, if two germs in the sheafification have the
same value at `x`, the local-germ condition gives smaller neighborhoods where
both are represented by sections of `F`; equality of germs in `F_x` gives a
further neighborhood on which those representatives agree, hence the original
sheafified germs agree.
Prover notes: the forward map is Mathlib's `TopCat.Presheaf.stalkToFiber`, and
Mathlib packages the source proof through `stalkToFiber_injective`,
`stalkToFiber_surjective`, and `sheafifyStalkIso`.
-/
def sheafifyStalkIso {X : TopCat.{v}} (F : Presheaf (Type v) X) (x : X) :
    (stalkToFiber_injective F).presheaf.stalk x ≅ F.stalk x :=
  TopCat.Presheaf.sheafifyStalkIso F x
