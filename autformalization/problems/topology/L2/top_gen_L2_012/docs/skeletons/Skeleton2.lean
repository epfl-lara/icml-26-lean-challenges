import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Functors

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

/--
Let $X$ be a topological space. $p_0 \in X$. Let $\mathcal{C}$ be a category with a terminal object
and $A \in \text{Ob}(\mathcal{C})$ be an object of $\mathcal{C}$. A skyscraper sheaf $\mathcal{F}$ with
value $A$ is a presheaf on $X$ with values in $\mathcal{C}$ such that
$\mathcal{F}(U) = A$ if $p_0 \in U$ and $\mathcal{F}(U) = 1_\mathcal{C}$ if $p_0 \notin U$
where $1_\mathcal{C}$ is some terminal object of $\mathcal{C}$.
-/
def skyscraperPresheaf_eq_pushforward {X : Type*} [TopologicalSpace X] 
  {C : Type*} [Category C] [Terminal C] (p₀ : X) (A : C) (F : Presheaf C X) : Prop :=
  ∀ (U : Set X), IsOpen U → 
    ((p₀ ∈ U) → F.obj ⟨U, ‹IsOpen U›⟩ = A) ∧
    ((p₀ ∉ U) → F.obj ⟨U, ‹IsOpen U›⟩ = default)

/--
A skyscraper presheaf with value $A$ is a sheaf.
-/
theorem skyscraperPresheaf_isSheaf {X : Type*} [TopologicalSpace X] 
  {C : Type*} [Category C] [Terminal C] (p₀ : X) (A : C) (F : Presheaf C X) 
  (h : skyscraperPresheaf_eq_pushforward p₀ A F) : 
  IsSheaf F := by sorry
