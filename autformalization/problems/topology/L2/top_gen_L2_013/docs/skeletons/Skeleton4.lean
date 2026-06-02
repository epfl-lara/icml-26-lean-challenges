import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.LocallySurjective

open CategoryTheory
open TopologicalSpace
open Opposite
open scoped AlgebraicGeometry

universe u

def IsLocallySurjective {X : TopCat} {F G : X.Presheaf (Type u)} (T : F ⟶ G) : Prop :=
  ∀ (U : Opens X) (t : G.obj (op U)) (x : X) (hx : x ∈ U),
    ∃ (V : Opens X) (hxV : x ∈ V) (hVU : V ≤ U),
      ∃ (s : F.obj (op V)), T.app (op V) s = G.map (homOfLE hVU).op t

theorem locally_surjective_iff_surjective_on_stalks {X : TopCat} {F G : X.Presheaf (Type u)} (T : F ⟶ G) :
    IsLocallySurjective T ↔ ∀ (x : X), Function.Surjective (TopCat.Presheaf.stalkMap T x) := by sorry
