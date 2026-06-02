import Mathlib

open CategoryTheory AlgebraicGeometry

-- Definition of IsProjective - a morphism being projective in the H-projective sense
def IsProjective {S X : Type*} [Scheme S] [Scheme X] (f : X → S) : Prop :=
  ∃ (n : ℕ) (i : X → ProjectiveSpace n S), 
    -- i is a closed immersion (monomorphism that is locally closed)
    IsMonomorphism i ∧ IsLocallyClosed i ∧
    -- i is a morphism over S (commutes with structure morphisms)
    (f = (structureMorphism : ProjectiveSpace n S → S) ∘ i)

-- Theorem: the structure morphism of projective space is proper
theorem is_projective_proper {S : Type*} [Scheme S] (n : ℕ) : 
  Proper (structureMorphism : ProjectiveSpace n S → S) := by sorry

-- Theorem: every projective morphism is proper
theorem projective_isProper {S X : Type*} [Scheme S] [Scheme X] (f : X → S) 
  (hf : IsProjective f) : Proper f := by sorry
