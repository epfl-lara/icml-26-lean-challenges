import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective

open TopCat TopologicalSpace Opposite CategoryTheory Presheaf Limits
open scoped AlgebraicGeometry

/-- A presheaf F on X is called flasque if for every inclusion of open sets V ⊆ U, 
the restriction map F(U) → F(V) is an epimorphism. -/
def isFlasquePresheaf {X : Type*} [TopologicalSpace X] (F : Presheaf (OpenSet X) (AddCommGroup)) : Prop :=
  ∀ (V U : OpenSet X), V ≤ U → Function.Surjective (F.restrict V U)

/-- A sheaf is called flasque if its underlying presheaf is flasque. -/
def isFlasqueSheaf {X : Type*} [TopologicalSpace X] (F : Sheaf (OpenSet X) (AddCommGroup)) : Prop :=
  isFlasquePresheaf F.toPresheaf

/-- Suppose 0 → F → G → H → 0 is a short exact sequence of sheaves of abelian groups on X.
If F and G are flasque, then H is flasque. -/
theorem of_shortExact_of_isFlasque {X : Type*} [TopologicalSpace X]
  (F G H : Sheaf (OpenSet X) (AddCommGroup))
  (f : F →ₗ G) (g : G →ₗ H)
  (hShortExact : ∀ U, Function.Injective (f.toPresheaf.map U) ∧ 
                   LinearMap.ker (g.toPresheaf.map U) = LinearMap.range (f.toPresheaf.map U) ∧
                   Function.Surjective (g.toPresheaf.map U))
  (hF : isFlasqueSheaf F)
  (hG : isFlasqueSheaf G) :
  isFlasqueSheaf H := sorry
