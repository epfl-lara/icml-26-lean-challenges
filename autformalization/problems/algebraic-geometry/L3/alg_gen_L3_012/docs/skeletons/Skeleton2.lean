import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open Opposite

/-- The functor of points of a scheme X -/
def functorOfPoints {S : Scheme} (X : Scheme) : (Schemes_over S)^op → Type := sorry

/-- Definition: A functor F:(Sch/S)^{opp} → Sets is limit preserving if 
    for every directed inverse system {T_i}_{i∈I} of affine schemes with limit T,
    we have F(T) = colim_i F(T_i). -/
def IsLimitPreserving {S : Scheme} (F : (Schemes_over S)^op → Type) : Prop :=
  ∀ {I : Type} [Preorder I] [IsDirected I] {T : I → Scheme}
    (hT_affine : ∀ i, Nonempty (AffineSite (T i)))
    (lim_T : Scheme) (proj : ∀ i, lim_T → T i)
    (comm : ∀ {i j} (hij : i ≤ j), proj i = proj j ∘ sorry) -- Commutativity condition
    (univ : ∀ (U : Scheme) (φ : ∀ i, U → T i), 
            (∀ {i j} (hij : i ≤ j), φ i = φ j ∘ sorry) → -- Commutativity condition
            ∃! (g : U → lim_T), ∀ i, φ i = proj i ∘ g), -- Universal property of limit
  F (Opposite.op lim_T) = 
    Colim (fun i => F (Opposite.op (T i))) (fun {i j} hij => sorry) -- Colim with transition maps

/-- Theorem: A morphism of schemes f:X → S is locally of finite presentation if and only if
    the functor of points h_X of X is limit preserving. -/
theorem locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving 
  {S : Scheme} (X : Scheme) (f : X → S) : 
  LocallyFinitePresentation f ↔ 
  IsLimitPreserving (functorOfPoints X) := by sorry

def functorOfPointsOver : Prop := by sorry
