import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Functors

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

def skyscraperPresheaf_eq_pushforward {X : TopCat} (p₀ : X) {C : Type*} [Category C]
    [HasTerminal C] (A : C) : X.Presheaf C := sorry

theorem skyscraperPresheaf_isSheaf {X : TopCat} (p₀ : X) {C : Type*} [Category C]
    [HasTerminal C] (A : C) :
    Presheaf.IsSheaf (skyscraperPresheaf_eq_pushforward p₀ A) := by sorry
