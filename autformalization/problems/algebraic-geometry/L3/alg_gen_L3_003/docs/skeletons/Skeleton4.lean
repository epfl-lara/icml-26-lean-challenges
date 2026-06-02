import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

open CategoryTheory Topology

/-- Predicate indicating a subset of a topological space is locally constructible -/
def LocallyConstructible {X : Type*} [TopologicalSpace X] (S : Set X) : Prop := by sorry

/-- If f: X → Y is a morphism of schemes of finite presentation, 
    then the image of a locally constructible subset under f is also locally constructible. -/
theorem locallyOfFinitePresentation_isStableUnderBaseChange
    {X Y : Type*} [Scheme X] [Scheme Y] 
    (f : SchemeMorphism X Y) -- Using a generic morphism type for schemes
    (hf : IsOfFinitePresentation f) : -- Using "of finite presentation" as stated in the problem
    ∀ (S : Set X), LocallyConstructible S → LocallyConstructible (Set.image f S) := by sorry
:= by sorry
