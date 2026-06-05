import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Functors

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v w

noncomputable section

/--
Source `docs/source.tex`, line-17 (`skyscraperPresheaf_eq_pushforward`).
The source defines the skyscraper presheaf at a point `p₀` with value `A` as the presheaf
whose value on an open `U` is `A` when `p₀ ∈ U` and a terminal object when `p₀ ∉ U`.
This Lean declaration implements the canonical such presheaf; see `Blueprint.md` for the
recorded representation choice.
-/
def skyscraperPresheaf_eq_pushforward {X : TopCat.{u}} (p₀ : X)
    {C : Type v} [Category.{w} C] [HasTerminal C] (A : C) : Presheaf C X := by
  classical
  exact
    { obj := fun U => if p₀ ∈ unop U then A else terminal C
      map := fun {U V} i =>
        if h : p₀ ∈ unop V then
          eqToHom <| by rw [if_pos h, if_pos (by simpa using i.unop.le h)]
        else
          ((if_neg h).symm.ndrec terminalIsTerminal).from _
      map_id := fun U =>
        (em (p₀ ∈ U.unop)).elim (fun h => dif_pos h) fun h =>
          ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext _ _
      map_comp := fun {U V W} iVU iWV => by
        by_cases hW : p₀ ∈ unop W
        · have hV : p₀ ∈ unop V := leOfHom iWV.unop hW
          simp only [dif_pos hW, dif_pos hV, eqToHom_trans]
        · dsimp
          rw [dif_neg hW]
          apply ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext }

/--
Source `docs/source.tex`, line-22 (`skyscraperPresheaf_isSheaf`).
Source proof: identify the skyscraper presheaf on `X` with the pushforward along the
constant map `TopCat.of PUnit ⟶ X` sending `*` to `p₀` of the corresponding skyscraper
presheaf on the one-point space. On the one-point space, the source presheaf is a sheaf
because its value on `∅` is terminal; pushforward of a sheaf is a sheaf, and the equality
transports the sheaf condition.
Prover notes: use `Presheaf.isSheaf_on_punit_of_isTerminal`,
`Sheaf.pushforward_sheaf_of_sheaf`, and an extensional comparison of opens with the
constant-map preimage cases `p₀ ∈ U` and `p₀ ∉ U`.
-/
theorem skyscraperPresheaf_isSheaf {X : TopCat.{u}} (p₀ : X)
    {C : Type v} [Category.{w} C] [HasTerminal C] (A : C) :
    (skyscraperPresheaf_eq_pushforward p₀ A).IsSheaf := by
  sorry

end
