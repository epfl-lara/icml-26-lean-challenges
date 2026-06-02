import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.LocallySurjective

open CategoryTheory
open TopologicalSpace
open Opposite
open scoped AlgebraicGeometry

-- Definition: IsLocallySurjective
def IsLocallySurjective {X : Type*} [TopologicalSpace X] 
  {F G : Presheaf X} (T : F → G) : Prop :=
  ∀ (U : Set X) (hU : IsOpen U) (t : G U) (x : X) (hx : x ∈ U),
    ∃ (V : Set X) (hV : IsOpen V) (hV_subset : V ⊆ U) (hx_in_V : x ∈ V) (s : F V),
      T s = t.restrict V hV_subset

-- Theorem: locally_surjective_iff_surjective_on_stalks
theorem locally_surjective_iff_surjective_on_stalks {X : Type*} [TopologicalSpace X] 
  {F G : Presheaf X} (T : F → G) : 
  IsLocallySurjective T ↔ 
  ∀ x : X, Function.Surjective (Presheaf.stalkMap T x) := by sorry
