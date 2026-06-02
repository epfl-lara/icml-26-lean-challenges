import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Stalks

open TopCat Opposite TopologicalSpace CategoryTheory

/-- 
The sheafification of a presheaf `F` on a topological space `X`.
For each open set `U`, it consists of functions `s : U → ⋃_{x∈U} F_x` such that
for every `x ∈ U`, there exists an open neighborhood `V` of `x` and a section `t ∈ F(V)`
such that for all `y ∈ V`, `s(y)` equals the germ of `t` at `y`.
-/
def stalkToFiber_injective {X : Type*} [TopologicalSpace X] {α : Type*} (F : Presheaf α X) : 
  Sheaf α X := by sorry

/--
Let `X` be a topological space and `F` a presheaf of sets on `X`. 
Let `tilde_F` be the sheafification of `F`. For `x ∈ X`, there is a map
`φ_x: tilde_F.stalk x → F.stalk x`
defined by `(U,s) ↦ s(x)`. 
This map is an isomorphism of stalks.
-/
theorem sheafifyStalkIso {X : Type*} [TopologicalSpace X] {α : Type*} (F : Presheaf α X) (x : X) : 
  -- The map φ_x takes a germ in the stalk of the sheafification (represented as Germ U s)
  -- and maps it to s(x) in F.stalk x
  -- Note: In the natural language statement, Germ U s corresponds to (U,s)
  Function.Bijective (λ germ : (stalkToFiber_injective F).stalk x => germ.repr.data.snd x) := by sorry
