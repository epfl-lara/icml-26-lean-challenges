import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

open CategoryTheory Schemes MorphismProperty

/--
Being an open immersion satisfies fpqc descent.
That is, a morphism is an open immersion if and only if its base change along any fpqc covering is also an open immersion.
-/
theorem descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact' 
  {X Y : Scheme} (f : X → Y) :
  IsOpenImmersion f ↔ 
    ∀ {Y' : Scheme} (g : Y' → Y) (hg : IsFpqcCovering g), 
      let baseChange := BaseChange.mk f g
      IsOpenImmersion baseChange.f := by sorry
:= by sorry
