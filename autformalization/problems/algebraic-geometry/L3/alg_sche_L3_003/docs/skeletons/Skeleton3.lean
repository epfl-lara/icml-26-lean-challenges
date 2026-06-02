import Mathlib

open CategoryTheory AlgebraicGeometry

theorem projective_isProper (S X : Type*) [Scheme S] [Scheme X] (f : X → S) 
  (hf : IsProjective f) : IsProper f := by sorry
